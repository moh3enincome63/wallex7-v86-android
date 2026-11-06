# Wallex 7 V86 Android foreground position guard.
# Uses the unchanged V85 RiskEngine and close_demo_position implementation.
# This service manages existing PAPER positions only; it never opens trades.
import json
import os
import time
import traceback

from jnius import autoclass

from main import Wallex7App, MarketDataEngine, RiskEngine, MOTOR_START_BALANCE

STATE_NAME = "wallex7_v85_paper_state.json"
STOP_NAME = "wallex7_v86_service.stop"
PAUSED_NAME = "wallex7_v86_ui_paused.flag"


def atomic_json(path, data):
    tmp = path + ".service.tmp"
    with open(tmp, "w", encoding="utf-8") as handle:
        json.dump(data, handle, ensure_ascii=False, separators=(",", ":"))
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(tmp, path)


def read_state(path):
    try:
        with open(path, "r", encoding="utf-8") as handle:
            state = json.load(handle)
        return state if isinstance(state, dict) and state.get("version") == 1 else None
    except Exception:
        return None


def state_payload(app):
    return {
        "version": 1,
        "saved_at": time.time(),
        "motor_balance": float(app.motor_balance),
        "demo_positions": app.demo_positions,
        "next_position_id": int(app.next_position_id),
        "trade_history": app.trade_history,
        "metrics": app.metrics,
        "trade_percent": float(app.trade_percent),
        "leverage": int(app.leverage),
        "symbol_cooldowns": app.symbol_cooldowns,
    }


def apply_state(app, state):
    app.motor_balance = float(state.get("motor_balance", MOTOR_START_BALANCE))
    app.demo_positions = list(state.get("demo_positions") or [])
    app.next_position_id = max(1, int(state.get("next_position_id", 1)))
    app.trade_history = list(state.get("trade_history") or [])
    for key, value in (state.get("metrics") or {}).items():
        if key in app.metrics:
            app.metrics[key] = value
    app.trade_percent = min(100.0, max(1.0, float(state.get("trade_percent", 20.0))))
    app.leverage = min(10, max(1, int(state.get("leverage", 1))))
    app.symbol_cooldowns = dict(state.get("symbol_cooldowns") or {})
    app.selected_position_id = app.demo_positions[0].get("id") if app.demo_positions else None


def main():
    PythonService = autoclass("org.kivy.android.PythonService")
    service = PythonService.mService
    try:
        service.setAutoRestartService(True)
    except Exception:
        pass
    Context = autoclass("android.content.Context")
    PowerManager = autoclass("android.os.PowerManager")
    pm = service.getSystemService(Context.POWER_SERVICE)
    wake_lock = pm.newWakeLock(PowerManager.PARTIAL_WAKE_LOCK, "Wallex7V86:PositionGuard")

    # Context.getFilesDir() is the same app-private directory used by
    # PythonActivity.getFilesDir() in main.py.
    data_dir = str(service.getFilesDir().getAbsolutePath())
    os.makedirs(data_dir, exist_ok=True)
    state_path = os.path.join(data_dir, STATE_NAME)
    stop_path = os.path.join(data_dir, STOP_NAME)
    paused_path = os.path.join(data_dir, PAUSED_NAME)
    resume_request_path = os.path.join(data_dir, "wallex7_v86_resume.request")
    resume_ack_path = os.path.join(data_dir, "wallex7_v86_resume.ack")

    app = Wallex7App.__new__(Wallex7App)
    app._v86_running_in_service = True
    app.data = MarketDataEngine(app)
    app.risk = RiskEngine(app)
    app.demo_positions = []
    app.motor_balance = MOTOR_START_BALANCE
    app.next_position_id = 1
    app.trade_history = []
    app.trade_percent = 20.0
    app.leverage = 1
    app.symbol_cooldowns = {}
    app.selected_position_id = None
    app.cooldown_until = 0.0
    app.last_auto_action = "ANDROID POSITION GUARD"
    app.metrics = {
        "entries": 0, "exits": 0, "wins": 0, "losses": 0,
        "net_pnl": 0.0, "peak_balance": MOTOR_START_BALANCE,
        "max_drawdown": 0.0,
    }
    app.live_price = lambda symbol: app.data.price(symbol)
    # UI callbacks are intentionally no-ops in this headless service process.
    app.update_auto_label = lambda *a, **k: None
    app.update_position_display = lambda *a, **k: None
    app.update_balance = lambda *a, **k: None
    app.update_history = lambda *a, **k: None
    app.update_mode_buttons = lambda *a, **k: None
    # close_demo_position() calls this after the last position is closed.
    # The service owns its own lifecycle and exits the guard loop below, so
    # this UI-side service-stop hook must be a safe no-op in the service process.
    app._stop_position_guard = lambda *a, **k: None
    app._paper_state_path = lambda: state_path
    app._save_paper_state = lambda *a, **k: atomic_json(state_path, state_payload(app))

    latest = read_state(state_path)
    if latest:
        apply_state(app, latest)

    wake_held = False
    try:
        while True:
            if os.path.exists(stop_path):
                break

            # Handshake: finish any in-flight risk pass and save it before the
            # UI resumes its own RiskEngine, preventing concurrent close actions.
            if os.path.exists(resume_request_path):
                try:
                    with open(resume_ack_path, "w", encoding="utf-8") as handle:
                        handle.write(str(time.time()))
                    if os.path.exists(paused_path):
                        os.remove(paused_path)
                    os.remove(resume_request_path)
                except Exception:
                    pass

            # Read UI changes (TP/SL, account state, manual close) before managing.
            latest = read_state(state_path)
            if latest:
                apply_state(app, latest)

            should_guard = bool(app.demo_positions) and os.path.exists(paused_path)
            if should_guard and not wake_held:
                wake_lock.acquire()
                wake_held = True
            elif not should_guard and wake_held:
                wake_lock.release()
                wake_held = False

            if should_guard:
                try:
                    app.data.fetch()
                    app.risk.manage()
                    app._save_paper_state()
                    if not app.demo_positions:
                        break
                except Exception:
                    # API/data errors must never be interpreted as a close signal.
                    # Preserve the last valid position snapshot and retry shortly.
                    pass
                time.sleep(3.0)
            else:
                time.sleep(2.0)
    finally:
        try:
            # Keep auto-restart enabled after an unexpected failure while a
            # position remains open; disable it only for deliberate shutdown.
            if os.path.exists(stop_path) or not app.demo_positions:
                service.setAutoRestartService(False)
        except Exception:
            pass
        try:
            if wake_held and wake_lock.isHeld():
                wake_lock.release()
        except Exception:
            pass
        try:
            service.stopSelf()
        except Exception:
            pass


if __name__ == "__main__":
    try:
        main()
    except Exception:
        try:
            path = os.path.join(os.environ.get("ANDROID_PRIVATE", "."), "wallex7_v86_service_error.txt")
            with open(path, "a", encoding="utf-8") as handle:
                handle.write("\n" + traceback.format_exc())
        except Exception:
            pass
