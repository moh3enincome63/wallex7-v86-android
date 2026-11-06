# WALLEX 7 - V86 ANDROID PACKAGE | BASE: V85 PC-TESTED SOURCE
# Based on V83. Preserves V15/V9 direction and V74/V77 decision-point gates.
# Fixes: structural calculation exceptions are no longer silently swallowed;
# diagnostics record exact gate/error per market; timing is re-evaluated even
# when the worker has no newly confirmed candidate. DEMO / PAPER TRADING ONLY.
# V48 fixes the V47 entry-worker blocker: progressive gate thresholds are now defined locally in best_candidate()
# before evaluation. V15/V9 direction logic is preserved. V46/V47 profit protection and UI/bootstrap are preserved.
# V47 fixes the V46 startup data-flow bug: the UI now performs an initial market fetch before rendering the 17 TMN rows, and REST refreshes keep the market map current.
# V44 keeps the proven V15/V9 direction formula, fixes history warm-up,
# removes slow pre-entry depth/candle fan-out, and runs entry scanning in a worker thread.
# Inspired by modular controller/risk-engine architecture used in advanced algo-trading systems.
# DEMO ONLY - NO REAL ORDERS ARE SENT TO WALLEX.

import json
import os
import time
import threading
import math
from bisect import bisect_right
from statistics import mean, median, pstdev

import requests
import websocket
from kivy.app import App
from kivy.clock import Clock
from kivy.core.window import Window
from kivy.uix.boxlayout import BoxLayout
from kivy.uix.scatter import Scatter
from kivy.uix.gridlayout import GridLayout
from kivy.uix.label import Label
from kivy.uix.button import Button
from kivy.uix.scrollview import ScrollView
from kivy.uix.slider import Slider
from kivy.uix.spinner import Spinner
from kivy.uix.textinput import TextInput
from kivy.graphics import Color, Rectangle

API_URL = "https://api.wallex.ir/v1/markets"
REFRESH_SECONDS = 10
FAST_PRICE_SECONDS = 2.5
LIVE_PRICE_MAX_AGE_SECONDS = 15.0  # stale WebSocket values fall back to REST
WEBSOCKET_URL = "wss://api.wallex.ir/ws"
ITEMS_PER_PAGE = 17
VISIBLE_COINS = 17
MAX_POSITIONS = 1
# V61: exactly one automatic/demo position for clean entry diagnosis.

# V46: later positions require progressively stronger independent quality.
POSITION_QUALITY_GATES = {
    0: (4, 55, 50),
    1: (5, 58, 54),
    2: (6, 61, 58),
    3: (7, 64, 62),
    4: (8, 67, 66),
}

# V46: peak-profit protection; percentages are price/P&L percentages, not fixed Toman.
PROFIT_PROTECT_ACTIVATION_PCT = 1.25
PROFIT_RETRACE_EXIT_PCT = 0.55
PROFIT_FLOOR_PCT = 0.35
PROFIT_PROTECT_CONFIRMATIONS = 3
VISIBLE_COIN_ORDER = [
    "USDT", "ETH", "USOON", "XRP", "BTC", "PEPE", "DOGE", "SOL", "BNB",
    "ADA", "SLVON", "CAKE", "SHIB", "COPXON", "ARB", "DOT", "A"
]
MOTOR_START_BALANCE = 10_000_000.0
DEFAULT_TRADE_PERCENT = 20.0
FEE_PERCENT_PER_SIDE = 0.2

# Entry rules: V9 remains the primary signal/ranking engine.
ENTRY_MIN_SCORE = 4
ENTRY_MIN_CONFIRMATIONS = 2
CONFIDENCE_THRESHOLD = 55
ENTRY_STABILITY_CONFIRMATIONS = 2
MAX_SAME_SIDE_AUTO = 5
SYMBOL_COOLDOWN_SECONDS = 120

# New Market Quality layer: gate only; V9 Score remains primary.
MARKET_QUALITY_THRESHOLD = 50
DEPTH_CACHE_SECONDS = 30
CANDLE_CACHE_SECONDS = 60
DEPTH_LEVELS = 8
CANDLE_LOOKBACK_SECONDS = 2 * 60 * 60
QUALITY_SHORTLIST_SIZE = 17
ENTRY_CANDLE_LOOKBACK_SECONDS = 2 * 60 * 60
ENTRY_CANDLE_CACHE_SECONDS = 30
ENTRY_WORKER_INTERVAL = 5
ENTRY_MAX_SPREAD_PCT = 1.50
ENTRY_MAX_OPPOSITE_1M_PCT = 0.70
ENTRY_MAX_CHASE_1M_PCT = 1.50
ENTRY_MAX_CHASE_3M_PCT = 3.00
ENTRY_MAX_FINAL_PRICE_DRIFT_PCT = 0.45

# V79 DYNAMIC ENTRY TIMING WINDOW: after the V77 setup survives its two-scan
# confirmation, wait briefly for a calmer/retest entry instead of opening
# immediately. The window is deliberately short so valid opportunities are
# not blocked for hours. At the end of the window, a still-valid setup may
# enter under the normal final-price drift and safety rules.
V79_TIMING_MIN_WAIT_SECONDS = 20.0
V79_TIMING_MAX_WAIT_SECONDS = 90.0
V79_TIMING_MAX_ADVERSE_PCT = 0.60
V79_TIMING_MAX_FAVORABLE_PCT = 0.25
V79_TIMING_REBOUND_1M_PCT = 0.05
# V61 direction-quality gate:
# A BUY/SELL is not accepted from one strong timeframe alone.
# Require broad multi-timeframe agreement and two consecutive scan confirmations.
MIN_ALIGNED_TIMEFRAMES = 2
REQUIRED_MID_TF_CONFIRMATIONS = 1   # 15m + 30m must agree with the side

# V61 explicit entry framework: structure -> zone/range -> direction -> volume -> timing.
ENTRY_STRUCTURE_LOOKBACK_1H = 72
ENTRY_STRUCTURE_CACHE_SECONDS = 60
ENTRY_ZONE_EDGE_PCT = 40.0
ENTRY_REQUIRE_DIRECTIONAL_VOLUME = True

# V61 SMART RANGE OVERRIDE
# RANGE MIDDLE is no longer an absolute veto. A strong directional breakout
# candidate may pass the range gate when the independent entry evidence is
# already strong. Ordinary/marginal RANGE-MIDDLE candidates remain blocked.
V61_RANGE_BREAKOUT_MIN_SCORE = 6
V61_RANGE_BREAKOUT_MIN_CONFIDENCE = 65
V61_RANGE_BREAKOUT_MIN_ALIGNED_TF = 2
V61_RANGE_BREAKOUT_MIN_MID_TF = 1
V61_RANGE_BREAKOUT_BUFFER_PCT = 0.05
V61_REQUIRE_BREAKOUT_CONFIRMATION = True
V61_REQUIRE_BREAKOUT_PULLBACK_OR_TRIGGER = True
# V74 ENTRY-TIMING FIX
# Do not enter at the top/bottom of a fast move. A strong 3m directional move
# must cool off/retest before entry when price is still sitting on the extreme.
V61_REQUIRE_PULLBACK_ON_RANGE_BREAKOUT = False
V61_EXTENSION_MOVE_3M_PCT = 1.50
V61_EXTENSION_EDGE_PCT = 0.15

# V61 MULTI-PATH ENTRY:
# A candidate can qualify through ONE of three independent paths.
V61_TREND_PULLBACK_MIN_SCORE = 4
V61_TREND_PULLBACK_MIN_CONFIDENCE = 55
V61_TREND_PULLBACK_ZONE_PCT = 40.0
V61_BREAKOUT_MIN_SCORE = 6
V61_BREAKOUT_MIN_CONFIDENCE = 65
V61_STRONG_TRIGGER_MIN_SCORE = 7
V61_STRONG_TRIGGER_MIN_CONFIDENCE = 70
V61_STRONG_TRIGGER_MIN_ALIGNED = 3

# V65 CONTROLLED OPPORTUNITY ENTRY
# Goal: avoid the V61/V62 over-filtering chain while keeping four hard protections:
# 1) correct direction/structure, 2) abnormal spread, 3) severe chase/opposite move,
# 4) clearly contradictory volume pressure. Entry paths are alternatives.
V65_TREND_MIN_SCORE = 4
V65_TREND_MIN_CONFIDENCE = 55
V65_RANGE_MIN_SCORE = 3
V65_RANGE_MIN_CONFIDENCE = 50
V65_BREAKOUT_MIN_SCORE = 5
V65_BREAKOUT_MIN_CONFIDENCE = 58
V65_BREAKOUT_MIN_ALIGNED = 1
V65_MAX_OPPOSITE_VOLUME = 0.30
V65_MAX_1M_CHASE = 1.50
V65_MAX_3M_CHASE = 3.00
V65_FINAL_DRIFT_PCT = 0.45
V65_STABILITY_SCANS = 1
V65_DIRECT_MIN_SCORE = 5
V65_DIRECT_MIN_CONFIDENCE = 60
V65_DIRECT_STRONG_SCORE = 7
V65_DIRECT_STRONG_CONFIDENCE = 70

# V74 MARKET DECISION POINT ENTRY ENGINE
# V74 keeps V65's anti-blocker philosophy but removes the low-quality DIRECT_V9
# escape path. An automatic entry must have independent direction/structure,
# timing/volume evidence, and two consecutive qualifying scans.
V74_MIN_ALIGNED_TF = 2
V74_MIN_MID_ALIGNED = 1
V74_MIN_MARKET_QUALITY = 52
V74_MIN_DIRECTIONAL_VOLUME = 0.03
V74_TREND_MIN_SCORE = 4
V74_TREND_MIN_CONFIDENCE = 55
V74_RANGE_MIN_SCORE = 3
V74_RANGE_MIN_CONFIDENCE = 50
V74_BREAKOUT_MIN_SCORE = 5
V74_BREAKOUT_MIN_CONFIDENCE = 58
V74_BREAKOUT_MIN_ALIGNED = 1
V74_CONFIRMATION_SCANS = 2
V74_CONFIRMATION_MAX_AGE = 45
V74_SCORE_DEGRADATION_MAX = 2
# V84: confirmation is tracked independently per market/side/path, not just for
# the current top-ranked candidate. A brief rank change therefore cannot erase
# another still-valid candidate's confirmation history.
V84_CONFIRMATION_MAX_AGE = 45.0
V84_CONFIRMATION_MAX_GAP = max(ENTRY_WORKER_INTERVAL * 3.0, 15.0)
V84_TIMING_INVALID_SCANS_TO_CANCEL = 2



# V13 position management:
# STOP LOSS = market structure + ATR breathing room.
# PROFIT MANAGEMENT = ONLY 4H trend + 1H zone + breakout/pullback + 15m trigger.
ATR_PERIOD = 14
SL_ATR_BUFFER = 0.35
STRUCTURE_LOOKBACK_1H = 72
STRUCTURE_LOOKBACK_4H = 60
STRUCTURE_LOOKBACK_15M = 48
SWING_LEFT = 2
SWING_RIGHT = 2
BREAKOUT_BUFFER_PCT = 0.05
ZONE_TOLERANCE_PCT = 0.15
PROFIT_INVALIDATION_CONFIRMATIONS = 2
STRUCTURE_REFRESH_SECONDS = 60

HISTORY_SECONDS = 7 * 24 * 3600
HISTORY_SAMPLE_SECONDS = 55


class Background(BoxLayout):
    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        with self.canvas.before:
            Color(0.25, 0.25, 0.25, 1)
            self.rect = Rectangle(pos=self.pos, size=self.size)
        self.bind(pos=self.update_rect, size=self.update_rect)

    def update_rect(self, *args):
        self.rect.pos = self.pos
        self.rect.size = self.size


class MarketDataEngine:
    """Fetches and stores market data. No trading decisions are made here."""

    def __init__(self, app):
        self.app = app
        self.symbols = {}
        self.history = {}
        self.last_sample = {}
        self.depth_cache = {}
        self.candle_cache = {}

    def fetch(self):
        response = requests.get(API_URL, timeout=10)
        response.raise_for_status()
        data = response.json()
        symbols = data.get("result", {}).get("symbols", {})
        if not isinstance(symbols, dict):
            raise ValueError("Unexpected Wallex API symbols format")
        self.symbols = symbols
        self.record_history()
        return symbols

    def number(self, value):
        try:
            return float(value)
        except (TypeError, ValueError):
            return 0.0

    def stats(self, symbol):
        return (self.symbols.get(symbol, {}) or {}).get("stats", {}) or {}

    def price(self, symbol):
        value = self.stats(symbol).get("lastPrice")
        try:
            value = float(value)
            return value if value > 0 else None
        except (TypeError, ValueError):
            return None

    def record_history(self):
        now = time.time()
        cutoff = now - HISTORY_SECONDS
        for symbol in self.symbols:
            px = self.price(symbol)
            if px is None:
                continue
            hist = self.history.setdefault(symbol, [])
            last = self.last_sample.get(symbol, 0.0)
            if now - last < HISTORY_SAMPLE_SECONDS:
                continue
            hist.append((now, px))
            self.last_sample[symbol] = now
            while hist and hist[0][0] < cutoff:
                hist.pop(0)
            if len(hist) > 12000:
                del hist[:-12000]

    def historical_price(self, symbol, seconds_ago):
        hist = self.history.get(symbol, [])
        if not hist:
            return None
        target = time.time() - seconds_ago
        idx = bisect_right(hist, (target, float("inf"))) - 1
        if idx < 0:
            return None
        return hist[idx][1]

    def _candle_close_ago(self, symbol, minutes):
        data = self.fetch_candles_1m(symbol)
        try:
            closes = [float(x) for x in data.get("c", []) if float(x) > 0]
            if len(closes) <= minutes:
                return None
            value = closes[-1 - minutes]
            return value if value > 0 else None
        except (AttributeError, TypeError, ValueError):
            return None

    def recent_change(self, symbol, seconds_ago):
        current = self.price(symbol)
        if current is None:
            return None
        # Prefer the live/local history once it has warmed up. For a fresh launch,
        # fall back to real 1m UDF candles so 5m/15m/30m/1h/2h are available immediately.
        old = self.historical_price(symbol, seconds_ago)
        if old is None and seconds_ago in (300, 900, 1800, 3600, 7200):
            old = self._candle_close_ago(symbol, int(seconds_ago // 60))
        if old is None or old <= 0:
            return None
        return (current - old) / old * 100.0

    def available_window(self, symbol, seconds_ago):
        hist = self.history.get(symbol, [])
        if hist:
            age = time.time() - hist[0][0]
            return min(seconds_ago, max(0.0, age))
        # UDF 1m candles provide the warm-up window without pretending it is 7D history.
        if seconds_ago in (300, 900, 1800, 3600, 7200):
            data = self.fetch_candles_1m(symbol)
            try:
                count = len(data.get("c", []))
                return min(seconds_ago, max(0.0, (count - 1) * 60.0))
            except (AttributeError, TypeError):
                pass
        return 0.0

    def prefetch_entry_candles(self, symbols, workers=4):
        """Warm the 1m cache for the exact 17 entry markets in parallel.
        This removes the launch-time dead zone caused by an empty local history.
        """
        symbols = [s for s in symbols if s]
        if not symbols:
            return
        try:
            from concurrent.futures import ThreadPoolExecutor, as_completed
            with ThreadPoolExecutor(max_workers=max(1, min(int(workers), len(symbols)))) as pool:
                futures = [pool.submit(self.fetch_candles_1m, s) for s in symbols]
                for future in as_completed(futures):
                    try:
                        future.result()
                    except Exception:
                        pass
        except Exception:
            for symbol in symbols:
                try:
                    self.fetch_candles_1m(symbol)
                except Exception:
                    pass


    def ohlcv(self, symbol, resolution_minutes, lookback_seconds):
        """Fetch OHLCV candles for structural risk management."""
        now = int(time.time())
        try:
            resolution = int(resolution_minutes)
            lookback = max(900, int(lookback_seconds))
        except (TypeError, ValueError):
            resolution, lookback = 1, 3600
        params = {
            "symbol": symbol,
            "resolution": str(resolution),
            "from": max(0, now - lookback),
            "to": now,
        }
        try:
            response = requests.get("https://api.wallex.ir/v1/udf/history", params=params, timeout=5)
            response.raise_for_status()
            payload = response.json()
            if not isinstance(payload, dict) or payload.get("s") != "ok":
                return []
            t = payload.get("t", []) or []
            o = payload.get("o", []) or []
            h = payload.get("h", []) or []
            l = payload.get("l", []) or []
            c = payload.get("c", []) or []
            v = payload.get("v", []) or []
            n = min(len(t), len(o), len(h), len(l), len(c))
            rows = []
            for i in range(n):
                try:
                    rows.append({
                        "t": float(t[i]), "o": float(o[i]), "h": float(h[i]),
                        "l": float(l[i]), "c": float(c[i]),
                        "v": float(v[i]) if i < len(v) else 0.0,
                    })
                except (TypeError, ValueError):
                    continue
            return rows
        except Exception:
            return []

    def atr(self, rows, period=ATR_PERIOD):
        if not rows:
            return None
        try:
            period = max(2, int(period))
        except (TypeError, ValueError):
            period = 14
        if len(rows) < period + 1:
            return None
        trs = []
        for i in range(1, len(rows)):
            try:
                high = float(rows[i]["h"]); low = float(rows[i]["l"])
                prev_close = float(rows[i-1]["c"])
                trs.append(max(high - low, abs(high - prev_close), abs(low - prev_close)))
            except (KeyError, TypeError, ValueError):
                continue
        if len(trs) < period:
            return None
        return mean(trs[-period:])

    def swing_levels(self, rows):
        highs = []
        lows = []
        if not rows:
            return highs, lows
        left = max(1, int(SWING_LEFT))
        right = max(1, int(SWING_RIGHT))
        if len(rows) < left + right + 1:
            return highs, lows
        for i in range(left, len(rows) - right):
            try:
                hi = float(rows[i]["h"])
                lo = float(rows[i]["l"])
                left_highs = [float(rows[j]["h"]) for j in range(i-left, i)]
                right_highs = [float(rows[j]["h"]) for j in range(i+1, i+right+1)]
                left_lows = [float(rows[j]["l"]) for j in range(i-left, i)]
                right_lows = [float(rows[j]["l"]) for j in range(i+1, i+right+1)]
                if hi >= max(left_highs) and hi >= max(right_highs):
                    highs.append((i, hi))
                if lo <= min(left_lows) and lo <= min(right_lows):
                    lows.append((i, lo))
            except (KeyError, TypeError, ValueError):
                continue
        return highs, lows

    def fetch_depth(self, symbol):
        """Fetch a small cached order-book snapshot. Never used for real orders."""
        now = time.time()
        cached = self.depth_cache.get(symbol)
        if cached and now - cached.get("time", 0.0) < DEPTH_CACHE_SECONDS:
            return cached.get("data")
        try:
            response = requests.get("https://api.wallex.ir/v1/depth", params={"symbol": symbol}, timeout=5)
            response.raise_for_status()
            payload = response.json()
            data = payload.get("result", {}) if isinstance(payload, dict) else {}
            if not isinstance(data, dict):
                data = {}
            self.depth_cache[symbol] = {"time": now, "data": data}
            return data
        except Exception:
            self.depth_cache[symbol] = {"time": now, "data": None}
            return None

    def fetch_candles_1m(self, symbol):
        """Fetch recent 1-minute OHLCV candles for volume/volatility checks."""
        now = time.time()
        cached = self.candle_cache.get(symbol)
        if cached and now - cached.get("time", 0.0) < ENTRY_CANDLE_CACHE_SECONDS:
            return cached.get("data")
        params = {
            "symbol": symbol,
            "resolution": "1",
            "from": int(now - CANDLE_LOOKBACK_SECONDS),
            "to": int(now),
        }
        try:
            response = requests.get("https://api.wallex.ir/v1/udf/history", params=params, timeout=4)
            response.raise_for_status()
            payload = response.json()
            if not isinstance(payload, dict) or payload.get("s") != "ok":
                data = None
            else:
                data = payload
            self.candle_cache[symbol] = {"time": now, "data": data}
            return data
        except Exception:
            self.candle_cache[symbol] = {"time": now, "data": None}
            return None

    def orderbook_metrics(self, symbol):
        stats = self.stats(symbol)
        depth = self.fetch_depth(symbol)
        bids = depth.get("bid", []) if isinstance(depth, dict) else []
        asks = depth.get("ask", []) if isinstance(depth, dict) else []
        bids = bids[:DEPTH_LEVELS] if isinstance(bids, list) else []
        asks = asks[:DEPTH_LEVELS] if isinstance(asks, list) else []

        def level_notional(level):
            try:
                if level.get("sum") is not None:
                    return abs(float(level.get("sum")))
                return abs(float(level.get("price"))) * abs(float(level.get("quantity")))
            except (TypeError, ValueError, AttributeError):
                return 0.0

        bid_depth = sum(level_notional(x) for x in bids)
        ask_depth = sum(level_notional(x) for x in asks)
        if bid_depth <= 0:
            bid_depth = self.number(stats.get("bidVolume")) * self.number(stats.get("bidPrice"))
        if ask_depth <= 0:
            ask_depth = self.number(stats.get("askVolume")) * self.number(stats.get("askPrice"))

        bid_price = None
        ask_price = None
        try:
            if bids:
                bid_price = float(bids[0].get("price"))
        except (TypeError, ValueError, AttributeError):
            pass
        try:
            if asks:
                ask_price = float(asks[0].get("price"))
        except (TypeError, ValueError, AttributeError):
            pass
        if bid_price is None:
            bid_price = self.number(stats.get("bidPrice"))
        if ask_price is None:
            ask_price = self.number(stats.get("askPrice"))
        mid = (bid_price + ask_price) / 2.0 if bid_price > 0 and ask_price > 0 else 0.0
        spread_pct = ((ask_price - bid_price) / mid * 100.0) if mid > 0 else None
        depth_ratio = bid_depth / ask_depth if ask_depth > 0 else 0.0
        return {
            "bid_depth": bid_depth,
            "ask_depth": ask_depth,
            "depth_ratio": depth_ratio,
            "spread_pct": spread_pct,
            "bid_levels": len(bids),
            "ask_levels": len(asks),
            "has_depth": bool(bids and asks),
        }

    def candle_metrics(self, symbol):
        data = self.fetch_candles_1m(symbol)
        if not data:
            return {"rvol": None, "volatility": None, "range_pct": None, "has_candles": False}
        try:
            closes = [float(x) for x in data.get("c", []) if float(x) > 0]
            highs = [float(x) for x in data.get("h", []) if float(x) > 0]
            lows = [float(x) for x in data.get("l", []) if float(x) > 0]
            volumes = [max(0.0, float(x)) for x in data.get("v", [])]
        except (TypeError, ValueError):
            return {"rvol": None, "volatility": None, "range_pct": None, "has_candles": False}
        if len(closes) < 20 or len(volumes) < 20:
            return {"rvol": None, "volatility": None, "range_pct": None, "has_candles": False}

        recent_count = min(15, len(volumes) // 2)
        recent = volumes[-recent_count:]
        previous = volumes[-2 * recent_count:-recent_count]
        prev_avg = mean(previous) if previous else 0.0
        rvol = (mean(recent) / prev_avg) if prev_avg > 0 else None

        returns = []
        for a, b in zip(closes[-61:-1], closes[-60:]):
            if a > 0 and b > 0:
                returns.append((b - a) / a * 100.0)
        volatility = pstdev(returns) if len(returns) >= 10 else None

        pairs = []
        for h, l, c in zip(highs[-30:], lows[-30:], closes[-30:]):
            if c > 0:
                pairs.append((h - l) / c * 100.0)
        range_pct = mean(pairs) if pairs else None
        return {"rvol": rvol, "volatility": volatility, "range_pct": range_pct, "has_candles": True}

    def market_quality(self, symbol, side, peer_quote_median=None):
        stats = self.stats(symbol)
        book = self.orderbook_metrics(symbol)
        candles = self.candle_metrics(symbol)
        score = 50.0

        spread = book.get("spread_pct")
        if spread is not None:
            if spread <= 0.10: score += 10
            elif spread <= 0.25: score += 8
            elif spread <= 0.50: score += 4
            elif spread <= 1.00: score -= 3
            else: score -= 10

        depth_ratio = book.get("depth_ratio") or 0.0
        directional = depth_ratio if side == "BUY" else (1.0 / depth_ratio if depth_ratio > 0 else 0.0)
        if directional >= 1.30: score += 14
        elif directional >= 1.05: score += 7
        elif directional >= 0.85: score += 2
        elif directional > 0: score -= 10

        quote24 = self.number(stats.get("24h_quoteVolume"))
        if peer_quote_median and peer_quote_median > 0:
            rel_quote = quote24 / peer_quote_median
            if rel_quote >= 1.50: score += 8
            elif rel_quote >= 1.00: score += 5
            elif rel_quote >= 0.50: score += 1
            else: score -= 7
        else:
            rel_quote = None

        rvol = candles.get("rvol")
        if rvol is not None:
            if 0.80 <= rvol <= 2.50: score += 8
            elif 0.50 <= rvol < 0.80: score += 2
            elif 2.50 < rvol <= 4.00: score -= 2
            elif rvol < 0.50: score -= 7
            else: score -= 4

        vol = candles.get("volatility")
        if vol is not None:
            if 0.03 <= vol <= 0.50: score += 8
            elif 0.01 <= vol < 0.03 or 0.50 < vol <= 1.00: score += 3
            elif vol < 0.01: score -= 4
            elif vol > 1.50: score -= 8

        bid_count = self.number(stats.get("bidCount"))
        ask_count = self.number(stats.get("askCount"))
        count_total = bid_count + ask_count
        if count_total >= 500: score += 5
        elif count_total >= 100: score += 2
        elif 0 < count_total < 20: score -= 4

        quality = int(max(0, min(100, round(score))))
        status = "READY" if quality >= MARKET_QUALITY_THRESHOLD else "WEAK"
        if not book.get("has_depth") or not candles.get("has_candles"):
            status = "PARTIAL-{}".format(status)
        return {
            "market_quality": quality,
            "quality_status": status,
            "spread_pct": spread,
            "depth_ratio": depth_ratio,
            "directional_depth": directional,
            "rvol": rvol,
            "volatility": vol,
            "range_pct": candles.get("range_pct"),
            "rel_quote_volume": rel_quote,
        }


class DecisionEngine:
    """V9-style scoring is kept primary. Confidence filters; it does not re-rank strong signals."""

    def __init__(self, app):
        self.app = app
        self.cache = {}
        self.confirmation_state = {}

    def clear_cache(self):
        self.cache = {}

    def recent_consistency(self, symbol):
        vals = []
        for ago in (300, 900, 1800, 3600, 7200):
            c = self.app.data.recent_change(symbol, ago)
            if c is not None:
                vals.append(1 if c > 0.05 else -1 if c < -0.05 else 0)
        return sum(vals)

    def acceleration_score(self, symbol):
        vals = [self.app.data.recent_change(symbol, ago) for ago in (300, 900, 1800, 3600, 7200)]
        if any(x is None for x in vals):
            return 0
        short_avg = sum(vals[:3]) / 3.0
        long_avg = sum(vals[3:]) / 2.0
        if short_avg > long_avg + 0.10 and short_avg > 0:
            return 1
        if short_avg < long_avg - 0.10 and short_avg < 0:
            return -1
        return 0

    def reversal_score(self, symbol, side):
        score = 0
        for ago in (300, 900, 1800, 3600, 7200):
            c = self.app.data.recent_change(symbol, ago)
            if c is None:
                continue
            if side == "BUY":
                score += -1 if c <= -0.15 else 1 if c >= 0.15 else 0
            else:
                score += 1 if c >= 0.15 else -1 if c <= -0.15 else 0
        return score

    def analyze(self, symbol):
        if symbol in self.cache:
            return self.cache[symbol]
        stats = self.app.data.stats(symbol)
        if not stats:
            result = {"signal": "HOLD", "power": "WEAK", "score": 0, "confidence": 0, "quality": "NO DATA"}
            self.cache[symbol] = result
            return result

        periods = ((300, 1.0), (900, 1.5), (1800, 1.75), (3600, 1.5), (7200, 1.25))
        changes = []
        for seconds, weight in periods:
            value = self.app.data.recent_change(symbol, seconds)
            if value is not None:
                changes.append((seconds, value, weight))

        trend = 0.0
        momentum = 0.0
        confirmations_buy = 0
        confirmations_sell = 0
        for _, value, weight in changes:
            if value >= 0.30:
                trend += weight
                momentum += min(1.0, value / 0.30) * 0.5
                confirmations_buy += 1
            elif value >= 0.10:
                trend += weight * 0.45
                momentum += 0.2
            elif value <= -0.30:
                trend -= weight
                momentum -= min(1.0, abs(value) / 0.30) * 0.5
                confirmations_sell += 1
            elif value <= -0.10:
                trend -= weight * 0.45
                momentum -= 0.2

        bid = self.app.data.number(stats.get("bidVolume", 0))
        ask = self.app.data.number(stats.get("askVolume", 0))
        direction = stats.get("direction", {}) or {}
        buys = self.app.data.number(direction.get("BUY", 0))
        sells = self.app.data.number(direction.get("SELL", 0))
        last_side = str(stats.get("lastTradeSide", "")).upper()

        pressure = 0.0
        if bid > 0 and ask > 0:
            ratio = bid / ask
            if ratio >= 1.20:
                pressure += 2.0
            elif ratio >= 1.05:
                pressure += 0.75
            elif ratio <= 0.833:
                pressure -= 2.0
            elif ratio <= 0.952:
                pressure -= 0.75
        if buys > sells + 5:
            pressure += 1.5
        elif buys > sells + 2:
            pressure += 0.75
        elif sells > buys + 5:
            pressure -= 1.5
        elif sells > buys + 2:
            pressure -= 0.75
        if last_side == "BUY":
            pressure += 0.5
        elif last_side == "SELL":
            pressure -= 0.5

        acceleration = self.acceleration_score(symbol)
        consistency = self.recent_consistency(symbol)

        # V61 diagnostic volume model:
        # use bid/ask volume plus trade-side volume as confirmation, not as a
        # standalone signal.  This keeps the V15/V9 direction engine intact.
        total_book = bid + ask
        book_imbalance = ((bid - ask) / total_book) if total_book > 0 else 0.0
        total_trades = buys + sells
        trade_imbalance = ((buys - sells) / total_trades) if total_trades > 0 else 0.0
        volume_pressure = max(-1.0, min(1.0, 0.65 * book_imbalance + 0.35 * trade_imbalance))
        volume_buy_confirm = volume_pressure >= 0.08
        volume_sell_confirm = volume_pressure <= -0.08

        buy_score = trend + momentum + max(0.0, pressure) + max(0, consistency) * 0.45 + max(0, acceleration) * 0.75
        sell_score = -trend - momentum + max(0.0, -pressure) + max(0, -consistency) * 0.45 + max(0, -acceleration) * 0.75

        # Small volume confirmation bonus/penalty. Strong contradiction is
        # handled later as an entry safety blocker, so one noisy volume sample
        # cannot completely rewrite the primary V9/V15 direction score.
        buy_score += 0.75 if volume_buy_confirm else -0.35 if volume_sell_confirm else 0.0
        sell_score += 0.75 if volume_sell_confirm else -0.35 if volume_buy_confirm else 0.0
        direction_score = buy_score - sell_score

        min_confirm = ENTRY_MIN_CONFIRMATIONS
        if abs(direction_score) < 1.25:
            signal, score = "HOLD", int(round(direction_score))
            power = "CONFLICT"
        elif direction_score > 0 and confirmations_buy >= min_confirm:
            score = int(round(min(12, buy_score)))
            signal = "BUY" if score >= 4 else "HOLD"
            power = "VERY STRONG" if score >= 9 else "STRONG" if score >= 6 else "MEDIUM" if score >= 4 else "WEAK"
        elif direction_score < 0 and confirmations_sell >= min_confirm:
            score = -int(round(min(12, sell_score)))
            signal = "SELL" if score <= -4 else "HOLD"
            power = "VERY STRONG" if score <= -9 else "STRONG" if score <= -6 else "MEDIUM" if score <= -4 else "WEAK"
        else:
            signal, score, power = "HOLD", int(round(direction_score)), "NO CONFIRM"

        # V61: explicit multi-timeframe direction map.  A high score is not
        # enough when the short/medium/long windows disagree.
        tf_map = {seconds: value for seconds, value, _ in changes}
        side_for_alignment = signal if signal in ("BUY", "SELL") else None
        aligned_tfs = 0
        mid_aligned = 0
        if side_for_alignment:
            side_sign = 1 if side_for_alignment == "BUY" else -1
            for seconds in (300, 900, 1800, 3600, 7200):
                value = tf_map.get(seconds)
                if value is not None and value * side_sign > 0.05:
                    aligned_tfs += 1
            for seconds in (900, 1800):
                value = tf_map.get(seconds)
                if value is not None and value * side_sign > 0.05:
                    mid_aligned += 1

        confidence = self.confidence(symbol, signal, score, changes, pressure, acceleration, consistency, confirmations_buy, confirmations_sell)
        quality = "READY" if confidence >= CONFIDENCE_THRESHOLD else "WAIT"
        result = {
            "signal": signal, "power": power, "score": score,
            "confidence": confidence, "quality": quality,
            "tf_map": tf_map,
            "aligned_tfs": aligned_tfs,
            "mid_aligned": mid_aligned,
            "volume_pressure": volume_pressure,
            "buy_volume_confirm": volume_buy_confirm,
            "sell_volume_confirm": volume_sell_confirm,
            "bid_volume": bid, "ask_volume": ask,
            "buy_trades": buys, "sell_trades": sells,
        }
        self.cache[symbol] = result
        return result

    def confidence(self, symbol, signal, score, changes, pressure, acceleration, consistency, cb, cs):
        if signal not in ("BUY", "SELL"):
            base = 35.0
        else:
            side = 1 if signal == "BUY" else -1
            tf_values = [v for _, v, _ in changes]
            if tf_values:
                aligned = sum(1 for v in tf_values if v * side > 0.05) / len(tf_values)
            else:
                aligned = 0.0
            base = 35.0 + aligned * 25.0
            base += min(15.0, abs(score) / 12.0 * 15.0)
            pressure_alignment = 1.0 if pressure * side > 0.75 else 0.5 if pressure * side > 0 else 0.0
            base += pressure_alignment * 10.0
            accel_alignment = 1.0 if acceleration * side > 0 else 0.0
            base += accel_alignment * 7.0
            consistency_alignment = min(1.0, max(0.0, consistency * side) / 5.0)
            base += consistency_alignment * 8.0
            base += min(5.0, abs(side * (cb - cs)))

            # 24h and 7d are context only; never fake 7d when data is unavailable.
            ch24 = self.app.data.stats(symbol).get("24h_ch")
            try:
                ch24 = float(ch24)
            except (TypeError, ValueError):
                ch24 = 0.0
            if ch24 * side > 0:
                base += 2.0
            ch7 = self.app.data.recent_change(symbol, 7 * 24 * 3600)
            if ch7 is not None and ch7 * side > 0:
                base += 3.0
            elif self.app.data.available_window(symbol, 7 * 24 * 3600) < 6 * 3600:
                base -= 2.0  # data-quality penalty: we do not pretend to have 7D evidence
        return int(max(0, min(100, round(base))))

    def entry_structure(self, symbol):
        """V61 entry structure gate from confirmed 1H swing structure.

        Rules: HH+HL -> BUY side; LH+LL -> SELL side; mixed structure -> RANGE.
        In RANGE, only the support/resistance edges are tradable; the middle is blocked.
        Results are cached to avoid 1H HTTP fan-out on every 5-second worker cycle.
        """
        now = time.time()
        cached = getattr(self, "entry_structure_cache", {}).get(symbol)
        if cached and now - cached.get("time", 0.0) < ENTRY_STRUCTURE_CACHE_SECONDS:
            return cached.get("data", {})
        data = {"ready": False, "trend": "UNKNOWN", "near_support": False,
                "near_resistance": False, "middle_range": False,
                "support": None, "resistance": None, "range_pct": None,
                "reason": "NO STRUCTURE"}
        try:
            rows = self.app.data.ohlcv(symbol, 60, ENTRY_STRUCTURE_LOOKBACK_1H * 3600)
            if len(rows) >= 20:
                highs, lows = self.app.data.swing_levels(rows)
                price = self.app.data.price(symbol)
                if price and len(highs) >= 2 and len(lows) >= 2:
                    h1, h2 = highs[-1][1], highs[-2][1]
                    l1, l2 = lows[-1][1], lows[-2][1]
                    if h1 > h2 and l1 > l2:
                        trend = "BULLISH"
                    elif h1 < h2 and l1 < l2:
                        trend = "BEARISH"
                    else:
                        trend = "RANGE"
                    support = max((v for _, v in lows if v <= price), default=min(v for _, v in lows))
                    resistance = min((v for _, v in highs if v >= price), default=max(v for _, v in highs))
                    width = max(0.0, resistance - support)
                    if width > 0:
                        from_support = max(0.0, (price - support) / width * 100.0)
                        from_resistance = max(0.0, (resistance - price) / width * 100.0)
                    else:
                        from_support = from_resistance = 100.0
                    near_support = from_support <= ENTRY_ZONE_EDGE_PCT
                    near_resistance = from_resistance <= ENTRY_ZONE_EDGE_PCT
                    middle = (not near_support and not near_resistance)
                    data = {"ready": True, "trend": trend, "near_support": near_support,
                            "near_resistance": near_resistance, "middle_range": middle,
                            "support": support, "resistance": resistance,
                            "range_pct": (width / price * 100.0) if price > 0 else None,
                            "reason": "HH+HL" if trend == "BULLISH" else "LH+LL" if trend == "BEARISH" else "RANGE"}
        except Exception as exc:
            data["reason"] = "STRUCT ERR {}".format(str(exc)[:35])
        if not hasattr(self, "entry_structure_cache"):
            self.entry_structure_cache = {}
        self.entry_structure_cache[symbol] = {"time": now, "data": data}
        return data

    def stable_entry(self, symbol, result):
        # V61 FIX: exact score matching was too strict. A healthy signal can
        # move from S4 to S5 or S6 between scans while keeping the same
        # direction. Stability therefore means same BUY/SELL direction and
        # same score family, not an identical integer score.
        signal = result.get("signal")
        score = int(result.get("score", 0) or 0)
        if signal not in ("BUY", "SELL"):
            self.confirmation_state.pop(symbol, None)
            self.confirmation_state.pop((symbol, "count"), None)
            return False
        score_family = abs(score) // 2
        key = (signal, score_family)
        previous = self.confirmation_state.get(symbol)
        count = 1 if previous != key else self.confirmation_state.get((symbol, "count"), 0) + 1
        self.confirmation_state[symbol] = key
        self.confirmation_state[(symbol, "count")] = count
        return count >= ENTRY_STABILITY_CONFIRMATIONS


class RiskEngine:
    """V13 structure-based stop and four-factor profit management."""

    def __init__(self, app):
        self.app = app
        self._structure_cache = {}

    def current_pnl_percent(self, position, current_price):
        entry = position["entry"]
        if position["side"] == "BUY":
            return ((current_price - entry) / entry) * 100.0
        return ((entry - current_price) / entry) * 100.0

    def user_exit_hit(self, position, current_price):
        tp = position.get("user_tp_price")
        sl = position.get("user_sl_price")
        if position["side"] == "BUY":
            if tp and current_price >= tp:
                return "USER TP PRICE"
            if sl and current_price <= sl:
                return "USER SL PRICE"
        else:
            if tp and current_price <= tp:
                return "USER TP PRICE"
            if sl and current_price >= sl:
                return "USER SL PRICE"
        return None

    def structure_snapshot(self, symbol):
        now = time.time()
        item = self._structure_cache.get(symbol)
        if item and now - item["time"] < STRUCTURE_REFRESH_SECONDS:
            return item["data"]

        h4 = self.app.data.ohlcv(symbol, 240, STRUCTURE_LOOKBACK_4H * 4 * 3600)
        h1 = self.app.data.ohlcv(symbol, 60, STRUCTURE_LOOKBACK_1H * 3600)
        m15 = self.app.data.ohlcv(symbol, 15, STRUCTURE_LOOKBACK_15M * 900)

        if len(h4) < 10 or len(h1) < 10 or len(m15) < 10:
            data = {"ready": False, "reason": "NO STRUCTURE DATA"}
        else:
            data = {
                "ready": True,
                "h4": h4,
                "h1": h1,
                "m15": m15,
                "h4_trend": self.h4_trend(h4),
                "h1_zone": self.h1_zone(h1),
                "atr1h": self.app.data.atr(h1),
            }
        self._structure_cache[symbol] = {"time": now, "data": data}
        return data

    def h4_trend(self, rows):
        highs, lows = self.app.data.swing_levels(rows)
        if len(highs) < 2 or len(lows) < 2:
            return "NEUTRAL"
        if highs[-1][1] > highs[-2][1] and lows[-1][1] > lows[-2][1]:
            return "BULLISH"
        if highs[-1][1] < highs[-2][1] and lows[-1][1] < lows[-2][1]:
            return "BEARISH"
        return "NEUTRAL"

    def h1_zone(self, rows):
        highs, lows = self.app.data.swing_levels(rows)
        if not highs or not lows:
            return None
        last_close = rows[-1]["c"]
        support = max((v for _, v in lows if v <= last_close), default=lows[-1][1])
        resistance = min((v for _, v in highs if v >= last_close), default=highs[-1][1])
        return {"support": support, "resistance": resistance}

    def structural_stop(self, position, snap):
        h1 = snap.get("h1", [])
        atr = snap.get("atr1h")
        if not h1 or atr is None or atr <= 0:
            return None
        highs, lows = self.app.data.swing_levels(h1)
        if position["side"] == "BUY":
            levels = [v for i, v in lows if i < len(h1) - SWING_RIGHT]
            if not levels:
                return None
            stop = levels[-1] - atr * SL_ATR_BUFFER
            return stop if stop < position["entry"] else None
        levels = [v for i, v in highs if i < len(h1) - SWING_RIGHT]
        if not levels:
            return None
        stop = levels[-1] + atr * SL_ATR_BUFFER
        return stop if stop > position["entry"] else None

    def breakout_pullback(self, rows, zone, side):
        if not rows or not zone:
            return {"breakout": False, "pullback": False, "state": "NO ZONE"}
        tol = ZONE_TOLERANCE_PCT / 100.0
        buffer = BREAKOUT_BUFFER_PCT / 100.0
        recent = rows[-min(8, len(rows)):]
        if side == "BUY":
            boundary = zone["resistance"]
            breakout = recent[-1]["c"] > boundary * (1.0 + buffer)
            pullback = breakout and any(
                r["l"] <= boundary * (1.0 + tol) and r["c"] >= boundary for r in recent
            )
        else:
            boundary = zone["support"]
            breakout = recent[-1]["c"] < boundary * (1.0 - buffer)
            pullback = breakout and any(
                r["h"] >= boundary * (1.0 - tol) and r["c"] <= boundary for r in recent
            )
        return {
            "breakout": breakout,
            "pullback": pullback,
            "state": "PULLBACK" if pullback else "BREAKOUT" if breakout else "WAIT"
        }

    def trigger_15m(self, rows, side):
        if len(rows) < 3:
            return False
        prev, cur = rows[-2], rows[-1]
        if side == "BUY":
            return cur["c"] > cur["o"] and cur["c"] > prev["h"]
        return cur["c"] < cur["o"] and cur["c"] < prev["l"]

    def profit_chain(self, position, snap):
        side = position["side"]
        trend = snap.get("h4_trend", "NEUTRAL")
        zone = snap.get("h1_zone")
        if trend == "NEUTRAL" or not zone:
            return {"hold": False, "state": "WAIT 4H/1H", "trend": trend}
        aligned = (side == "BUY" and trend == "BULLISH") or (side == "SELL" and trend == "BEARISH")
        if not aligned:
            return {"hold": False, "state": "4H INVALID", "trend": trend, "zone": zone}
        bp = self.breakout_pullback(snap["h1"], zone, side)
        trigger = self.trigger_15m(snap["m15"], side)
        hold = bp["pullback"] and trigger
        return {
            "hold": hold,
            "state": "HOLD 4H+1H+PB+15M" if hold else "WAIT 15M TRIGGER",
            "trend": trend,
            "zone": zone,
            "breakout": bp["breakout"],
            "pullback": bp["pullback"],
            "trigger15m": trigger
        }

    def _profit_protection(self, position, net, chain):
        peak = max(float(position.get("peak_net_pnl_pct", 0.0)), float(net))
        position["peak_net_pnl_pct"] = peak
        if peak >= PROFIT_PROTECT_ACTIVATION_PCT:
            position["profit_protect_active"] = True
        if not position.get("profit_protect_active"):
            position["profit_protect_confirmations"] = 0
            return None
        retracement = max(0.0, peak - net)
        if retracement >= peak * PROFIT_RETRACE_EXIT_PCT and not chain.get("hold") and net > PROFIT_FLOOR_PCT:
            position["profit_protect_confirmations"] = position.get("profit_protect_confirmations", 0) + 1
        elif net <= PROFIT_FLOOR_PCT and peak >= PROFIT_PROTECT_ACTIVATION_PCT:
            position["profit_protect_confirmations"] = position.get("profit_protect_confirmations", 0) + 1
        else:
            position["profit_protect_confirmations"] = 0
        if position.get("profit_protect_confirmations", 0) >= PROFIT_PROTECT_CONFIRMATIONS:
            return "V46 PEAK PROFIT PROTECTION" if net > 0 else "V46 PEAK PROFIT FLOOR"
        return None

    def manage(self):
        for position in list(self.app.demo_positions):
            current = self.app.live_price(position["symbol"])
            if current is None:
                continue
            raw = self.current_pnl_percent(position, current)
            net = raw - FEE_PERCENT_PER_SIDE * 2.0
            position["last_net_pnl_pct"] = net

            reason = self.user_exit_hit(position, current)
            if reason:
                self.app.close_demo_position(position, current, raw, reason)
                continue

            snap = self.structure_snapshot(position["symbol"])
            if not snap.get("ready"):
                position["risk_state"] = "WAIT | NO STRUCTURE"
                continue

            # Structural SL: it can tighten, but never move farther from the trade.
            new_sl = self.structural_stop(position, snap)
            old_sl = position.get("structural_sl_price")
            if new_sl is not None:
                if old_sl is None:
                    position["structural_sl_price"] = new_sl
                elif position["side"] == "BUY":
                    position["structural_sl_price"] = max(old_sl, new_sl)
                else:
                    position["structural_sl_price"] = min(old_sl, new_sl)

            sl = position.get("structural_sl_price")
            if sl is not None:
                hit = (position["side"] == "BUY" and current <= sl) or (position["side"] == "SELL" and current >= sl)
                if hit:
                    self.app.close_demo_position(position, current, raw, "STRUCTURE STOP LOSS")
                    continue

            chain = self.profit_chain(position, snap)
            position["profit_state"] = chain.get("state", "WAIT")
            position["h4_trend"] = chain.get("trend", "NEUTRAL")
            position["h1_zone"] = chain.get("zone")
            position["breakout_ok"] = chain.get("breakout", False)
            position["pullback_ok"] = chain.get("pullback", False)
            position["trigger15m_ok"] = chain.get("trigger15m", False)

            # V74: profit protection is deliberately patient.
            # A small temporary loss of the profit-chain confirmation is NOT enough
            # to close a profitable position. Exit protection requires either:
            # 1) a meaningful peak-profit retracement confirmed 3 scans, or
            # 2) a real structure stop, or
            # 3) the user-defined TP/SL.
            protection_reason = self._profit_protection(position, net, chain)
            if protection_reason:
                self.app.close_demo_position(position, current, raw, protection_reason)
                continue

            # V74 REMOVES the old fast "PROFIT STRUCTURE INVALID" exit.
            # Losing one/two 15m confirmations while price is still healthy must
            # not prematurely close a profitable position. Keep it open and wait
            # for structure/trend confirmation to recover or for peak protection.
            position["profit_invalidations"] = 0

            position["risk_state"] = "{} | SL {}".format(
                position.get("profit_state", "WAIT"),
                "N/A" if sl is None else "{:,.2f}".format(sl)
            )


class Wallex7App(App):
    # V86 Android lifecycle support. The UI and PythonService use the same
    # application-private files directory so the foreground service can
    # continue managing the exact V85 paper position after the UI is paused.
    def _shared_private_dir(self):
        if hasattr(self, "_v86_private_dir_cache"):
            return self._v86_private_dir_cache
        try:
            from jnius import autoclass
            PythonActivity = autoclass("org.kivy.android.PythonActivity")
            activity = PythonActivity.mActivity
            path = str(activity.getFilesDir().getAbsolutePath())
            if path:
                self._v86_private_dir_cache = path
                return path
        except Exception:
            pass
        path = self.user_data_dir
        self._v86_private_dir_cache = path
        return path

    def _paper_state_path(self):
        return os.path.join(self._shared_private_dir(), "wallex7_v85_paper_state.json")

    def _v86_control_path(self, filename):
        return os.path.join(self._shared_private_dir(), filename)

    def _start_position_guard(self):
        if not self.demo_positions:
            return False
        try:
            from kivy.utils import platform
            if platform != "android":
                return False
            stop_path = self._v86_control_path("wallex7_v86_service.stop")
            if os.path.exists(stop_path):
                os.remove(stop_path)
            from jnius import autoclass
            activity = autoclass("org.kivy.android.PythonActivity").mActivity
            service_name = str(activity.getPackageName()) + ".ServicePositionGuard"
            self._position_guard_service = autoclass(service_name)
            self._position_guard_service.start(activity, "position-guard")
            return True
        except Exception as error:
            try:
                self.engine_worker_error = "ANDROID GUARD START ERROR: {}".format(error)[:180]
            except Exception:
                pass
            return False

    def _stop_position_guard(self):
        if getattr(self, "_v86_running_in_service", False):
            return
        try:
            from kivy.utils import platform
            if platform != "android":
                return
        except Exception:
            return
        try:
            stop_path = self._v86_control_path("wallex7_v86_service.stop")
            with open(stop_path, "w", encoding="utf-8") as handle:
                handle.write(str(time.time()))
        except Exception:
            pass
        try:
            for filename in ("wallex7_v86_ui_paused.flag", "wallex7_v86_resume.request", "wallex7_v86_resume.ack"):
                path = self._v86_control_path(filename)
                if os.path.exists(path):
                    os.remove(path)
        except Exception:
            pass
        try:
            from jnius import autoclass
            activity = autoclass("org.kivy.android.PythonActivity").mActivity
            service_class = getattr(self, "_position_guard_service", None)
            if service_class is None:
                service_class = autoclass(str(activity.getPackageName()) + ".ServicePositionGuard")
            Intent = autoclass("android.content.Intent")
            intent = Intent(activity, service_class)
            activity.stopService(intent)
        except Exception:
            pass
        self._position_guard_service = None

    def _save_paper_state(self, *_):
        try:
            state = {
                "version": 1,
                "saved_at": time.time(),
                "motor_balance": float(self.motor_balance),
                "demo_positions": self.demo_positions,
                "next_position_id": int(self.next_position_id),
                "trade_history": self.trade_history,
                "metrics": self.metrics,
                "trade_percent": float(self.trade_percent),
                "leverage": int(self.leverage),
                "symbol_cooldowns": self.symbol_cooldowns,
            }
            path = self._paper_state_path()
            os.makedirs(os.path.dirname(path), exist_ok=True)
            temp = path + ".tmp"
            with open(temp, "w", encoding="utf-8") as handle:
                json.dump(state, handle, ensure_ascii=False, separators=(",", ":"))
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(temp, path)
            return True
        except Exception as error:
            try:
                self.engine_worker_error = "PAPER SAVE ERROR: {}".format(error)[:180]
            except Exception:
                pass
            return False

    def _restore_paper_state(self):
        try:
            path = self._paper_state_path()
            if not os.path.isfile(path):
                return False
            with open(path, "r", encoding="utf-8") as handle:
                state = json.load(handle)
            if state.get("version") != 1:
                return False
            self.motor_balance = float(state.get("motor_balance", MOTOR_START_BALANCE))
            self.demo_positions = list(state.get("demo_positions") or [])
            self.next_position_id = max(int(state.get("next_position_id", 1)), 1)
            self.trade_history = list(state.get("trade_history") or [])
            restored_metrics = state.get("metrics") or {}
            for key in self.metrics:
                if key in restored_metrics:
                    self.metrics[key] = restored_metrics[key]
            self.trade_percent = min(100.0, max(1.0, float(state.get("trade_percent", DEFAULT_TRADE_PERCENT))))
            self.leverage = min(10, max(1, int(state.get("leverage", 1))))
            self.symbol_cooldowns = dict(state.get("symbol_cooldowns") or {})
            # Safety: never resume AUTO or entry-arm from a saved session.
            self.auto_running = False
            self.manual_mode = True
            self.auto_entry_armed = False
            self.v79_timing = None
            self.selected_position_id = self.demo_positions[0].get("id") if self.demo_positions else None
            return True
        except Exception as error:
            self.engine_worker_error = "PAPER RESTORE ERROR: {}".format(error)[:180]
            return False

    def _sync_service_state(self):
        """Adopt service-updated paper data without resetting AUTO controls."""
        try:
            path = self._paper_state_path()
            if not os.path.isfile(path):
                return False
            with open(path, "r", encoding="utf-8") as handle:
                state = json.load(handle)
            if state.get("version") != 1:
                return False
            self.motor_balance = float(state.get("motor_balance", self.motor_balance))
            self.demo_positions = list(state.get("demo_positions") or [])
            self.next_position_id = max(1, int(state.get("next_position_id", self.next_position_id)))
            self.trade_history = list(state.get("trade_history") or [])
            for key, value in (state.get("metrics") or {}).items():
                if key in self.metrics:
                    self.metrics[key] = value
            self.trade_percent = min(100.0, max(1.0, float(state.get("trade_percent", self.trade_percent))))
            self.leverage = min(10, max(1, int(state.get("leverage", self.leverage))))
            self.symbol_cooldowns = dict(state.get("symbol_cooldowns") or {})
            if not any(p.get("id") == self.selected_position_id for p in self.demo_positions):
                self.selected_position_id = self.demo_positions[0].get("id") if self.demo_positions else None
            return True
        except Exception as error:
            self.engine_worker_error = "SERVICE SYNC ERROR: {}".format(error)[:180]
            return False

    def exit_app(self, *_):
        self.stop_auto()
        self.fast_price_running = False
        self.websocket_running = False
        self.engine_worker_running = False
        self._save_paper_state()
        self._stop_position_guard()
        App.get_running_app().stop()

    def build(self):
        Window.borderless = False
        Window.title = "WALLEX 7 | V86 ANDROID | V85 ENGINE"
        self.data = MarketDataEngine(self)
        self.decision = DecisionEngine(self)
        self.risk = RiskEngine(self)
        self.coins = []
        self.display_coins = []
        self.ranked_markets = []
        self.page = 0
        self.motor_balance = MOTOR_START_BALANCE
        self.demo_positions = []
        self.next_position_id = 1
        self.trade_history = []
        self.auto_running = False
        self.manual_mode = True
        self.trade_percent = DEFAULT_TRADE_PERCENT
        self.last_auto_action = "Waiting"
        self.selected_position_id = None
        self.cooldown_until = 0.0
        self.symbol_cooldowns = {}
        self.auto_entry_armed = False
        self.v79_timing = None
        self.live_prices = {}
        self.live_price_times = {}
        self.last_ws_price_time = 0.0
        self.last_rest_price_time = 0.0
        self.ws_price_updates = 0
        self.leverage = 1
        self.metrics = {"entries": 0, "exits": 0, "wins": 0, "losses": 0, "net_pnl": 0.0, "peak_balance": MOTOR_START_BALANCE, "max_drawdown": 0.0}
        self.last_engine_update = 0.0
        self.fast_price_running = True
        # Background scanner: the Kivy UI thread never performs entry-market HTTP fan-out.
        self.engine_worker_running = False
        self.engine_worker_error = ""
        self.worker_cycles = 0
        self.worker_host = Wallex7App.__new__(Wallex7App)
        self.worker_host.data = MarketDataEngine(self.worker_host)
        self.worker_host.decision = DecisionEngine(self.worker_host)
        self.worker_host.risk = RiskEngine(self.worker_host)
        self.worker_host.live_prices = {}
        # V84 FIX: the background worker uses live_price_detail(), which reads
        # these fields. The worker host is created with __new__ and does not
        # inherit the main app's __init__ values automatically.
        self.worker_host.live_price_times = {}
        self.worker_host.last_ws_price_time = 0.0
        self.worker_host.last_rest_price_time = 0.0
        self.worker_host.ws_price_updates = 0
        self.worker_host.coins = []
        self.worker_host.display_coins = []
        self.worker_host.ranked_markets = []
        self.worker_host.demo_positions = []
        self.worker_host.symbol_cooldowns = {}
        self.worker_host.entry_diagnostic = "V79 WAIT | worker starting"
        self.worker_host.entry_diagnostic_full = self.worker_host.entry_diagnostic
        self.worker_host._v83_pending_entries = {}
        self.worker_host.worker_mode = True
        self.worker_host.engine_label = type("_WorkerLabel", (), {"text": ""})()

        self._restore_paper_state()
        if self.demo_positions:
            Clock.schedule_once(lambda dt: self._start_position_guard(), 2)
        root = Background(orientation="vertical", padding=4, spacing=1)
        root.add_widget(Label(text="##########  WALLEX 7  |  V86  ##########", font_size=17, bold=True, size_hint_y=None, height=29))
        root.add_widget(Label(text="V86 ANDROID  |  V85 TESTED ENGINE  |  PINCH ZOOM  |  BACKGROUND POSITION GUARD", font_size=9, bold=True, size_hint_y=None, height=19))
        root.add_widget(Label(text="DEMO / PAPER TRADING", font_size=10, size_hint_y=None, height=18))
        self.status_label = Label(text="CONNECTING...", font_size=10, size_hint_y=None, height=19)
        root.add_widget(self.status_label)
        self.summary_label = Label(text="BTC: --- | ETH: --- | SOL: ---", font_size=9, size_hint_y=None, height=20)
        root.add_widget(self.summary_label)
        self.engine_label = Label(text="CONTROLLER: WAITING...", font_size=9, size_hint_y=None, height=27)
        root.add_widget(self.engine_label)

        capital_row = BoxLayout(size_hint_y=None, height=31, spacing=3)
        capital_row.add_widget(Label(text="CAPITAL", font_size=9, size_hint_x=None, width=58))
        self.capital_slider = Slider(min=1, max=100, value=DEFAULT_TRADE_PERCENT, step=1)
        self.capital_slider.bind(value=self.on_capital_change)
        capital_row.add_widget(self.capital_slider)
        self.capital_label = Label(text="20%", font_size=9, size_hint_x=None, width=42)
        capital_row.add_widget(self.capital_label)
        root.add_widget(capital_row)

        mode_row = BoxLayout(size_hint_y=None, height=31, spacing=2)
        self.auto_button = Button(text="AUTO", font_size=9)
        self.manual_button = Button(text="MANUAL", font_size=9)
        self.start_button = Button(text="START AUTO", font_size=9)
        self.stop_button = Button(text="STOP AUTO", font_size=9)
        self.auto_button.bind(on_press=self.set_auto_mode)
        self.manual_button.bind(on_press=self.set_manual_mode)
        self.start_button.bind(on_press=self.start_auto)
        self.stop_button.bind(on_press=self.stop_auto)
        for w in (self.auto_button, self.manual_button, self.start_button, self.stop_button):
            mode_row.add_widget(w)
        root.add_widget(mode_row)

        config_row = BoxLayout(size_hint_y=None, height=31, spacing=2)
        config_row.add_widget(Label(text="LEV", font_size=9, size_hint_x=None, width=34))
        self.leverage_spinner = Spinner(text="1x", values=tuple("{}x".format(i) for i in range(1, 11)), font_size=9, size_hint_x=None, width=53)
        self.leverage_spinner.bind(text=self.on_leverage_change)
        config_row.add_widget(self.leverage_spinner)
        self.auto_entry_button = Button(text="ARM ENTRY OFF", font_size=8)
        self.auto_entry_button.bind(on_press=self.arm_auto_entry)
        config_row.add_widget(self.auto_entry_button)
        self.refresh_now_button = Button(text="REFRESH", font_size=8, size_hint_x=None, width=62)
        self.refresh_now_button.bind(on_press=lambda *_: self.refresh(0))
        config_row.add_widget(self.refresh_now_button)
        self.exit_button = Button(text="EXIT", font_size=8, size_hint_x=None, width=48)
        self.exit_button.bind(on_press=self.exit_app)
        config_row.add_widget(self.exit_button)
        root.add_widget(config_row)

        self.auto_label = Label(text="MODE: MANUAL | AUTO STOPPED | ENTRY ARM OFF", font_size=7, size_hint_y=None, height=18)
        root.add_widget(self.auto_label)

        manual_row = BoxLayout(size_hint_y=None, height=32, spacing=2)
        manual_row.add_widget(Label(text="SELECT", font_size=8, size_hint_x=None, width=45))
        # V76: keep the compact V72 manual selector layout, but preload all 17 TMN coins.
        manual_values = ("BEST", "USDT", "ETH", "USOON", "XRP", "BTC", "PEPE", "DOGE", "SOL", "BNB", "ADA", "SLVON", "CAKE", "SHIB", "COPXON", "ARB", "DOT", "A")
        self.coin_spinner = Spinner(text="BEST", values=manual_values, font_size=8)
        self.coin_spinner.bind(text=self.on_coin_selected)
        manual_row.add_widget(self.coin_spinner)
        self.buy_button = Button(text="BUY", font_size=8)
        self.sell_button = Button(text="SELL", font_size=8)
        self.close_button = Button(text="CLOSE", font_size=8)
        self.buy_button.bind(on_press=self.manual_buy)
        self.sell_button.bind(on_press=self.manual_sell)
        self.close_button.bind(on_press=self.manual_close)
        manual_row.add_widget(self.buy_button)
        manual_row.add_widget(self.sell_button)
        manual_row.add_widget(self.close_button)
        root.add_widget(manual_row)
        self.manual_hint_label = Label(text="MANUAL: select a coin above, then press BUY or SELL", font_size=9, bold=True, size_hint_y=None, height=20)
        root.add_widget(self.manual_hint_label)

        pos_row = BoxLayout(size_hint_y=None, height=30, spacing=2)
        pos_row.add_widget(Label(text="POSITION", font_size=8, size_hint_x=None, width=58))
        self.position_spinner = Spinner(text="NONE", values=("NONE",), font_size=8)
        self.position_spinner.bind(text=self.on_position_selected)
        pos_row.add_widget(self.position_spinner)
        root.add_widget(pos_row)

        exit_row = BoxLayout(size_hint_y=None, height=31, spacing=2)
        self.tp_input = TextInput(hint_text="TP PRICE TOMAN", multiline=False, font_size=9)
        self.sl_input = TextInput(hint_text="SL PRICE TOMAN", multiline=False, font_size=9)
        self.tp_button = Button(text="SET TP", font_size=8, size_hint_x=None, width=52)
        self.sl_button = Button(text="SET SL", font_size=8, size_hint_x=None, width=52)
        self.clear_exit_button = Button(text="CLEAR", font_size=8, size_hint_x=None, width=52)
        self.tp_button.bind(on_press=self.set_user_tp)
        self.sl_button.bind(on_press=self.set_user_sl)
        self.clear_exit_button.bind(on_press=self.clear_user_exits)
        exit_row.add_widget(self.tp_input)
        exit_row.add_widget(self.sl_input)
        exit_row.add_widget(self.tp_button)
        exit_row.add_widget(self.sl_button)
        exit_row.add_widget(self.clear_exit_button)
        root.add_widget(exit_row)

        self.position_label = Label(text="POSITIONS: NONE", font_size=10, halign="left", valign="middle", size_hint_y=None, height=78)
        self.position_label.bind(size=lambda i, v: setattr(i, "text_size", v))
        root.add_widget(self.position_label)
        self.entry_label = Label(text="ENTRY: ---", font_size=11, size_hint_y=None, height=20)
        root.add_widget(self.entry_label)
        self.current_label = Label(text="CURRENT: ---", font_size=11, size_hint_y=None, height=20)
        root.add_widget(self.current_label)
        self.pl_label = Label(text="P/L: ---", font_size=15, size_hint_y=None, height=29)
        root.add_widget(self.pl_label)
        self.last_closed_label = Label(text="LAST CLOSED: ---", font_size=10, halign="left", valign="middle", size_hint_y=None, height=38)
        self.last_closed_label.bind(size=lambda i, v: setattr(i, "text_size", v))
        root.add_widget(self.last_closed_label)

        header = GridLayout(cols=17, size_hint_y=None, height=23)
        for item in ["COIN", "USDT", "TMN", "5M", "15M", "30M", "1H", "2H", "SIGNAL", "PWR", "SCORE", "CONF", "Q", "SPRD", "DEPTH", "RVOL", "SIDE"]:
            header.add_widget(Label(text=item, font_size=6))
        root.add_widget(header)

        self.scroll = ScrollView(do_scroll_x=False, do_scroll_y=True, bar_width=10)
        self.market_grid = GridLayout(cols=17, spacing=1, padding=1, size_hint_y=None, row_default_height=23, row_force_default=True)
        self.market_grid.bind(minimum_height=self.market_grid.setter("height"))
        self.scroll.add_widget(self.market_grid)
        root.add_widget(self.scroll)

        navigation = BoxLayout(size_hint_y=None, height=28, spacing=2)
        self.previous_button = Button(text="<< PREV", font_size=8)
        self.page_label = Label(text="PAGE 1", font_size=8)
        self.next_button = Button(text="NEXT >>", font_size=8)
        self.previous_button.bind(on_press=self.previous_page)
        self.next_button.bind(on_press=self.next_page)
        navigation.add_widget(self.previous_button)
        navigation.add_widget(self.page_label)
        navigation.add_widget(self.next_button)
        root.add_widget(navigation)

        self.balance_label = Label(text="MOTOR BALANCE: 10,000,000 TOMAN | CAPITAL 20%", font_size=8, size_hint_y=None, height=18)
        root.add_widget(self.balance_label)
        self.history_label = Label(text="TRADES: 0 | HISTORY: ---", font_size=7, halign="left", valign="middle", size_hint_y=None, height=58)
        self.history_label.bind(size=lambda i, v: setattr(i, "text_size", v))
        root.add_widget(self.history_label)
        self.info_label = Label(text="DEMO ONLY | V80 LIVE PRICE SYNC + WS/REST AGE DIAGNOSTICS | V79 ENTRY PRESERVED | MAX 1", font_size=7, size_hint_y=None, height=18)
        root.add_widget(self.info_label)

        self.update_mode_buttons()
        self.update_position_display()
        Clock.schedule_once(self.refresh, 1)
        Clock.schedule_interval(self.refresh, REFRESH_SECONDS)
        Clock.schedule_interval(self._save_paper_state, 15)
        self.fast_price_running = True
        self.websocket_running = True
        self.live_prices = {}
        self.live_price_times = {}
        threading.Thread(target=self.fast_price_loop, daemon=True).start()
        threading.Thread(target=self.websocket_price_loop, daemon=True).start()
        # Scatter provides native two-finger pinch zoom; one-finger translation
        # and rotation are disabled so the interface stays anchored.
        # Keep the content canvas synchronized with the actual window size.
        # On desktop, the OS can maximize the window after Kivy's initial
        # 800x600 size was assigned; without this binding the Scatter child
        # remains narrow and the unused part of the window shows black.
        root.size_hint = (None, None)
        root.size = Window.size
        zoom_view = Scatter(do_translation=False, do_rotation=False, do_scale=True,
                            scale_min=0.65, scale_max=2.50,
                            size_hint=(None, None), size=Window.size)
        zoom_view.add_widget(root)

        def _sync_viewport(_window, new_size):
            # Resize the unscaled content and the viewport together. This does
            # not alter any trading engine or decision/risk logic.
            root.size = new_size
            zoom_view.size = new_size

        Window.bind(size=_sync_viewport)
        return zoom_view

    # ---------- Data helpers ----------
    def make_coin_list(self):
        grouped = {}
        for symbol in self.data.symbols:
            name = str(symbol).upper().replace("/", "").replace("-", "")
            if name.endswith("USDT"):
                coin = name[:-4]
                if coin:
                    grouped.setdefault(coin, {})["USDT"] = symbol
            elif name.endswith("TMN"):
                coin = name[:-3]
                if coin:
                    grouped.setdefault(coin, {})["TMN"] = symbol
        self.coins = [{"coin": c, "USDT": grouped.get(c, {}).get("USDT"), "TMN": grouped.get(c, {}).get("TMN")} for c in VISIBLE_COIN_ORDER]
        self.display_coins = list(self.coins)
        vals = ["BEST"] + [x["coin"] for x in self.coins]
        if hasattr(self, "coin_spinner"):
            self.coin_spinner.values = tuple(vals)
            if self.coin_spinner.text not in vals:
                self.coin_spinner.text = "BEST"

    def market_coin_name(self, symbol):
        name = str(symbol).upper().replace("/", "").replace("-", "")
        return name[:-4] if name.endswith("USDT") else name[:-3] if name.endswith("TMN") else name

    def allowed_market(self, item):
        return bool(item and item.get("coin") in VISIBLE_COIN_ORDER and str(item.get("symbol", "")).upper().replace("/", "").replace("-", "").endswith("TMN"))

    # ---------- Scan / entry ----------
    def _peer_quote_median(self):
        vals = []
        for item in self.coins:
            symbol = item.get("TMN")
            if symbol:
                q = self.data.number(self.data.stats(symbol).get("24h_quoteVolume"))
                if q > 0:
                    vals.append(q)
        return median(vals) if vals else None

    def quick_market_quality(self, item, peer_median=None):
        """Fast entry quality from already-fetched market stats + cached 1m candles.
        No depth/HTTP fan-out is allowed in the pre-entry path.
        """
        symbol = item.get("symbol")
        signal = item.get("signal")
        stats = self.data.stats(symbol)
        quality = 50.0
        bid = self.data.number(stats.get("bidVolume")); ask = self.data.number(stats.get("askVolume"))
        if bid > 0 and ask > 0 and signal in ("BUY", "SELL"):
            ratio = bid / ask
            directional = ratio if signal == "BUY" else (1.0 / ratio if ratio > 0 else 0.0)
            if directional >= 1.20: quality += 12
            elif directional >= 1.05: quality += 6
            elif directional < 0.80: quality -= 10
        bp = self.data.number(stats.get("bidPrice")); ap = self.data.number(stats.get("askPrice"))
        spread = None
        if bp > 0 and ap > 0:
            mid = (bp + ap) / 2.0
            if mid > 0: spread = max(0.0, (ap - bp) / mid * 100.0)
            if spread is not None:
                if spread <= 0.20: quality += 8
                elif spread <= 0.50: quality += 4
                elif spread > 1.00: quality -= 8
        q = self.data.number(stats.get("24h_quoteVolume"))
        if peer_median and peer_median > 0 and q > 0:
            rel = q / peer_median
            if rel >= 1.50: quality += 6
            elif rel >= 1.00: quality += 3
            elif rel < 0.50: quality -= 5
        candle = self.data.fetch_candles_1m(symbol)
        rvol = None
        if candle:
            try:
                vols = [max(0.0, float(x)) for x in candle.get("v", [])]
                if len(vols) >= 12:
                    prior = mean(vols[-12:-3]); recent = mean(vols[-3:])
                    rvol = recent / prior if prior > 0 else None
                    if rvol is not None:
                        if 0.80 <= rvol <= 3.0: quality += 5
                        elif rvol < 0.50: quality -= 4
            except (TypeError, ValueError):
                rvol = None
        return {"market_quality": int(max(0, min(100, round(quality)))), "spread_pct": spread, "rvol": rvol}

    def enrich_market_quality(self, ranked):
        allowed = [x for x in ranked if self.allowed_market(x) and x.get("signal") in ("BUY", "SELL")]
        peer_median = self._peer_quote_median()
        for item in allowed:
            item.update(self.quick_market_quality(item, peer_median))
        for item in ranked:
            item.setdefault("market_quality", 50)
            item.setdefault("spread_pct", None)
            item.setdefault("rvol", None)

    def scan_market(self):
        ranked = []
        target_symbols = [x.get("TMN") for x in self.coins if x.get("TMN")]
        for symbol in target_symbols:
            a = self.decision.analyze(symbol)
            stats = self.data.stats(symbol)
            ranked.append({
                "coin": self.market_coin_name(symbol), "symbol": symbol,
                "signal": a["signal"], "power": a["power"], "score": a["score"],
                "confidence": a["confidence"], "change": self.data.number(stats.get("24h_ch", 0)),
                "volume_pressure": a.get("volume_pressure", 0.0),
                "buy_volume_confirm": a.get("buy_volume_confirm", False),
                "sell_volume_confirm": a.get("sell_volume_confirm", False),
                "aligned_tfs": a.get("aligned_tfs", 0),
                "mid_aligned": a.get("mid_aligned", 0),
                "tf_map": a.get("tf_map", {}),
                "structure": self.decision.entry_structure(symbol),
            })
        ranked.sort(key=lambda x: (abs(x["score"]), x["confidence"]), reverse=True)
        self.ranked_markets = ranked
        self.enrich_market_quality(ranked)
        allowed = [x for x in ranked if self.allowed_market(x)]
        buys = [x for x in allowed if x["signal"] == "BUY" and x["score"] >= ENTRY_MIN_SCORE]
        sells = [x for x in allowed if x["signal"] == "SELL" and x["score"] <= -ENTRY_MIN_SCORE]
        best_buy = max(buys, key=lambda x: (x["score"], x["confidence"], x.get("market_quality", 50))) if buys else None
        best_sell = min(sells, key=lambda x: (x["score"], -x["confidence"], -x.get("market_quality", 50))) if sells else None
        if best_buy or best_sell:
            self.engine_label.text = "V84 PRICE SYNC | API MARKETS | 17 TMN | BUY {} | SELL {} | {}".format(
                self.opportunity(best_buy), self.opportunity(best_sell), getattr(self, "entry_diagnostic", "SCANNING")
            )[:240]
        else:
            self.engine_label.text = "V84 WAIT | 17 TMN | BUY NONE | SELL NONE | {}".format(getattr(self, "entry_diagnostic", "NO SIGNAL"))[:240]

    def opportunity(self, item):
        if not item:
            return "NONE"
        st = (item.get("structure") or {}).get("trend", "?")
        rb = " RB" if item.get("v58_real_breakout") else ""
        return "{} {} S{} C{} Q{} TF{}/5 ST:{}{}".format(
            item["coin"], item["power"], item["score"], item["confidence"],
            item.get("market_quality", 50), item.get("aligned_tfs", 0), st, rb
        )

    def _entry_safety(self, item):
        """V74 market decision-point entry gate.

        PRIMARY RULE:
        BUY  = real H1 resistance breakout + hold/retest of resistance as support + directional volume.
        SELL = real H1 support breakdown + hold/retest below support + directional volume.

        No automatic entry from a trend trigger alone and no automatic entry in the middle of a range.
        Anti-blocker filters remain moderate so the engine can still find opportunities across 17 TMN markets.
        """
        signal = item.get("signal")
        side = 1 if signal == "BUY" else -1 if signal == "SELL" else 0
        side_name = "BUY" if side > 0 else "SELL"
        if not side:
            return False, "NO DIRECTION"
        symbol = item.get("symbol")
        price = self.data.price(symbol)
        if price is None or price <= 0:
            return False, "NO PRICE"

        spread = item.get("spread_pct")
        try:
            if spread is not None and float(spread) > ENTRY_MAX_SPREAD_PCT:
                return False, "SPREAD>{:.2f}".format(ENTRY_MAX_SPREAD_PCT)
        except (TypeError, ValueError):
            pass

        structure = item.get("structure") or {}
        if not structure.get("ready"):
            return False, "NO STRUCTURE"
        trend = structure.get("trend", "UNKNOWN")
        if trend not in ("BULLISH", "BEARISH", "RANGE"):
            return False, "STRUCT NEUTRAL"

        score = abs(int(item.get("score", 0) or 0))
        confidence = float(item.get("confidence", 0) or 0)
        aligned = int(item.get("aligned_tfs", 0) or 0)
        mid_aligned = int(item.get("mid_aligned", 0) or 0)
        quality = float(item.get("market_quality", 50) or 50)
        vp = float(item.get("volume_pressure", 0.0) or 0.0)

        if aligned < V74_MIN_ALIGNED_TF:
            return False, "MTF<{0}".format(V74_MIN_ALIGNED_TF)
        if mid_aligned < V74_MIN_MID_ALIGNED:
            return False, "MIDTF<{0}".format(V74_MIN_MID_ALIGNED)
        if quality < V74_MIN_MARKET_QUALITY:
            return False, "QUALITY<{0}".format(V74_MIN_MARKET_QUALITY)
        if vp * side < V74_MIN_DIRECTIONAL_VOLUME:
            return False, "WEAKVOL {:.2f}".format(vp)
        if side > 0 and vp <= -V65_MAX_OPPOSITE_VOLUME:
            return False, "SELLVOL {:.2f}".format(vp)
        if side < 0 and vp >= V65_MAX_OPPOSITE_VOLUME:
            return False, "BUYVOL {:.2f}".format(vp)

        # Fresh timing / chase protection.
        m1 = m3 = None
        try:
            fresh = self.data.fetch_candles_1m(symbol) or {}
            closes = [float(x) for x in fresh.get("c", []) if float(x) > 0]
            if len(closes) >= 2:
                m1 = (closes[-1] - closes[-2]) / closes[-2] * 100.0
            if len(closes) >= 4:
                m3 = (closes[-1] - closes[-4]) / closes[-4] * 100.0
        except (TypeError, ValueError, IndexError):
            pass
        if m1 is not None and m1 * side < -ENTRY_MAX_OPPOSITE_1M_PCT:
            return False, "OPPOSITE1M"
        if m1 is not None and abs(m1) > V65_MAX_1M_CHASE:
            return False, "CHASE1M"
        if m3 is not None and abs(m3) > V65_MAX_3M_CHASE:
            return False, "CHASE3M"

        # V77 MULTI-PATH DECISION POINT.
        # Breakout remains the strongest path, but it is no longer mandatory
        # for every setup. Valid TREND_PULLBACK and RANGE_EDGE setups can enter
        # when their own structural/volume/timing evidence is present.
        breakout_ok = False
        breakout_pullback = False
        breakout_trigger = False
        boundary = None
        try:
            snap = self.risk.structure_snapshot(symbol)
            zone = snap.get("h1_zone") if snap else None
            h1_rows = snap.get("h1", []) if snap else []
            m15_rows = snap.get("m15", []) if snap else []
            if zone:
                boundary = zone.get("resistance" if side > 0 else "support")
            bp = self.risk.breakout_pullback(h1_rows, zone, side_name)
            breakout_ok = bool(bp.get("breakout"))
            breakout_pullback = bool(bp.get("pullback"))
            breakout_trigger = bool(self.risk.trigger_15m(m15_rows, side_name))
        except Exception as error:
            # V83 silently swallowed this failure, making a broken structure
            # calculation look like an ordinary lack of breakout/trigger.
            item["entry_exception"] = "STRUCTURE {}: {}".format(type(error).__name__, str(error)[:140])
            item["v73_breakout_boundary"] = boundary
            item["v73_breakout"] = False
            item["v73_hold_retest"] = False
            item["v73_trigger15m"] = False
            item["entry_1m_change"] = m1
            item["entry_3m_change"] = m3
            return False, "STRUCT ERROR {}".format(type(error).__name__)

        item.pop("entry_exception", None)
        item["v73_breakout_boundary"] = boundary
        item["v73_breakout"] = breakout_ok
        item["v73_hold_retest"] = breakout_pullback
        item["v73_trigger15m"] = breakout_trigger
        item["entry_1m_change"] = m1
        item["entry_3m_change"] = m3

        # Never trade against the confirmed 1H structure. RANGE has no
        # directional permission by itself; it may trade only at an edge.
        if trend == "BULLISH" and side < 0:
            return False, "STRUCT BUY ONLY"
        if trend == "BEARISH" and side > 0:
            return False, "STRUCT SELL ONLY"

        # PATH 1: DECISION-POINT BREAKOUT.
        # This is still the preferred/highest-quality setup.
        if breakout_ok and breakout_pullback:
            if score < V74_BREAKOUT_MIN_SCORE:
                return False, "SCORE<{0}".format(V74_BREAKOUT_MIN_SCORE)
            if confidence < V74_BREAKOUT_MIN_CONFIDENCE:
                return False, "CONF<{0}".format(V74_BREAKOUT_MIN_CONFIDENCE)
            if aligned < V74_BREAKOUT_MIN_ALIGNED:
                return False, "BREAKTF<{0}".format(V74_BREAKOUT_MIN_ALIGNED)
            item["entry_path"] = "DECISION_POINT_BREAKOUT"
            item["v73_mode"] = "DECISION_POINT"
            return True, "PASS V77 BREAKOUT"

        # PATH 2: TREND PULLBACK.
        # BUY = bullish HH/HL structure + pullback toward H1 support.
        # SELL = bearish LH/LL structure + pullback toward H1 resistance.
        # A 15m directional trigger is required so we do not buy/sell a falling
        # knife merely because price is near a structural zone.
        trend_pullback = False
        if trend == "BULLISH" and side > 0:
            trend_pullback = bool(structure.get("near_support"))
        elif trend == "BEARISH" and side < 0:
            trend_pullback = bool(structure.get("near_resistance"))

        if trend_pullback:
            if score < V74_TREND_MIN_SCORE:
                return False, "PULLBACK SCORE<{0}".format(V74_TREND_MIN_SCORE)
            if confidence < V74_TREND_MIN_CONFIDENCE:
                return False, "PULLBACK CONF<{0}".format(V74_TREND_MIN_CONFIDENCE)
            if not breakout_trigger:
                return False, "PULLBACK WAIT15M"
            item["entry_path"] = "TREND_PULLBACK"
            item["v73_mode"] = "TREND_PULLBACK"
            return True, "PASS V77 TREND PULLBACK"

        # PATH 3: RANGE EDGE.
        # Middle of the range remains explicitly forbidden. Only support BUY
        # or resistance SELL is permitted, with a fresh 15m trigger.
        if trend == "RANGE":
            at_edge = ((side > 0 and structure.get("near_support")) or
                       (side < 0 and structure.get("near_resistance")))
            if not at_edge:
                return False, "RANGE MIDDLE"
            if score < V74_RANGE_MIN_SCORE:
                return False, "RANGE SCORE<{0}".format(V74_RANGE_MIN_SCORE)
            if confidence < V74_RANGE_MIN_CONFIDENCE:
                return False, "RANGE CONF<{0}".format(V74_RANGE_MIN_CONFIDENCE)
            if not breakout_trigger:
                return False, "RANGE WAIT15M"
            item["entry_path"] = "RANGE_EDGE"
            item["v73_mode"] = "RANGE_EDGE"
            return True, "PASS V77 RANGE EDGE"

        return False, "WAIT VALID ENTRY PATH"

    def best_candidate(self, signal=None, exclude_symbols=None):
        """V84: maintain confirmation state per candidate across rank changes.

        A candidate must still pass all safety checks in the current scan.
        Confirmation belongs to (symbol, side, entry path), not to the current
        overall winner. Old states expire; a temporary winner flip doesn't
        reset every other valid candidate.
        """
        exclude = set(exclude_symbols or [])
        candidates = []
        blockers = []
        now = time.time()
        pending_map = getattr(self, "_v83_pending_entries", None)
        if not isinstance(pending_map, dict):
            pending_map = {}
            self._v83_pending_entries = pending_map

        for x in self.ranked_markets:
            if not self.allowed_market(x) or x.get("symbol") in exclude:
                continue
            if signal and x.get("signal") != signal:
                x["entry_gate"] = "FILTERED-SIGNAL"
                continue
            side = x.get("signal")
            if side not in ("BUY", "SELL"):
                x["entry_gate"] = "NO-DIR"
                blockers.append("{} NO-DIR".format(x.get("coin", "?")))
                continue
            if self.symbol_cooldowns.get(x.get("symbol"), 0) > now:
                x["entry_gate"] = "COOLDOWN"
                blockers.append("{} COOLDOWN".format(x.get("coin", "?")))
                continue
            if abs(int(x.get("score", 0) or 0)) < V74_RANGE_MIN_SCORE:
                x["entry_gate"] = "SCORE<{}".format(V74_RANGE_MIN_SCORE)
                blockers.append("{} S<{}".format(x.get("coin", "?"), V74_RANGE_MIN_SCORE))
                continue

            safe, reason = self._entry_safety(x)
            x["entry_gate"] = reason
            if not safe:
                blockers.append("{} {}".format(x.get("coin", "?"), reason))
                continue

            x["candidate_price"] = self.live_price(x.get("symbol")) or self.data.price(x.get("symbol"))
            if not x["candidate_price"] or float(x["candidate_price"]) <= 0:
                x["entry_gate"] = "NO-LIVE-PRICE"
                blockers.append("{} NO-LIVE-PRICE".format(x.get("coin", "?")))
                continue
            x["candidate_price"] = float(x["candidate_price"])
            self.live_prices[x.get("symbol")] = x["candidate_price"]
            candidates.append(x)

        # Expire stale candidate histories. Keep other candidates' confirmations
        # when rank changes, but never reuse a very old confirmation.
        for old_key, old_state in list(pending_map.items()):
            age = now - float(old_state.get("last_seen", old_state.get("time", 0)) or 0)
            if age > V84_CONFIRMATION_MAX_AGE:
                pending_map.pop(old_key, None)

        if not candidates:
            # Do not wipe all confirmation state on one empty scan. States age
            # out naturally and only count again if the candidate passes gates.
            self.entry_diagnostic = "V84 WAIT | 17 TMN | BLOCK {}".format(
                ";".join(blockers[:10]) if blockers else "NO-SIGNAL")
            self.entry_diagnostic_full = "V84 WAIT | " + ("; ".join(blockers) if blockers else "NO-SIGNAL")
            return None

        def rank_key(x):
            path_bonus = {"DECISION_POINT_BREAKOUT": 5.0, "BREAKOUT_CONFIRM": 3.0,
                          "TREND_PULLBACK": 2.0, "RANGE_EDGE": 1.0}.get(x.get("entry_path"), 0.0)
            return (path_bonus, abs(int(x.get("score", 0) or 0)),
                    float(x.get("confidence", 0) or 0),
                    float(x.get("market_quality", 50) or 50),
                    abs(float(x.get("volume_pressure", 0.0) or 0.0)))

        # Update confirmation for EVERY currently valid candidate, not only
        # the current winner. A key can progress while another market ranks first.
        for item in candidates:
            key = (item.get("symbol"), item.get("signal"), item.get("entry_path"))
            score = abs(int(item.get("score", 0) or 0))
            confidence = float(item.get("confidence", 0) or 0)
            state = pending_map.get(key)
            if (not state or now - float(state.get("last_seen", 0) or 0) > V84_CONFIRMATION_MAX_GAP
                    or score + V74_SCORE_DEGRADATION_MAX < int(state.get("anchor_score", state.get("score", score)))):
                state = {"key": key, "score": score, "anchor_score": score, "confidence": confidence,
                         "first_seen": now, "last_seen": now, "count": 1}
                pending_map[key] = state
            else:
                state["count"] = int(state.get("count", 1)) + 1
                state["last_seen"] = now
                state["score"] = score
                state["confidence"] = confidence
            item["v83_confirmations"] = int(state.get("count", 1))

        winner = max(candidates, key=rank_key)
        key = (winner.get("symbol"), winner.get("signal"), winner.get("entry_path"))
        state = pending_map.get(key, {})
        count = int(state.get("count", 1))
        detail = "{} {} {} S{} C{} Q{} CONF {}/{}".format(
            winner.get("coin", "?"), winner.get("signal", "?"), winner.get("entry_path", "?"),
            abs(int(winner.get("score", 0) or 0)), winner.get("confidence", 0),
            winner.get("market_quality", 50), count, V74_CONFIRMATION_SCANS)
        if count < V74_CONFIRMATION_SCANS:
            self.entry_diagnostic = "V84 CONFIRM | " + detail
            self.entry_diagnostic_full = self.entry_diagnostic + " | BLOCK " + "; ".join(blockers)
            return None

        # Remove only the confirmed candidate's state so it must be freshly
        # observed again if it is not handed off / timing is cancelled.
        pending_map.pop(key, None)
        self.entry_diagnostic = "V84 ENTRY READY | " + detail
        self.entry_diagnostic_full = self.entry_diagnostic + " | BLOCK " + "; ".join(blockers)
        return winner

    def write_entry_diagnostics(self):
        """Write a compact, full-universe diagnostic snapshot for offline review."""
        try:
            path = os.path.join(os.getcwd(), "V84_ENTRY_DIAGNOSTICS.txt")
            stamp = time.strftime("%Y-%m-%d %H:%M:%S")
            rows = ["WALLEX 7 V84 ENTRY DIAGNOSTICS", "TIME: " + stamp,
                    "SUMMARY: " + str(getattr(self, "entry_diagnostic_full",
                                               getattr(self, "entry_diagnostic", "NO DIAGNOSTIC"))),
                    "MARKET_COUNT: {}".format(len(getattr(self, "ranked_markets", []))), ""]
            for item in getattr(self, "ranked_markets", []):
                structure = item.get("structure") or {}
                rows.append(
                    "{coin:8} {symbol:12} {signal:4} score={score:>3} conf={conf:>5} "
                    "quality={quality:>5} volume={volume:>6} tf={tf} mid={mid} "
                    "trend={trend:9} structure_ready={ready} brk={brk} retest={retest} trig15={trig} "
                    "path={path:24} gate={gate} error={error}".format(
                        coin=str(item.get("coin", "?")), symbol=str(item.get("symbol", "?")),
                        signal=str(item.get("signal", "?")), score=str(item.get("score", "?")),
                        conf=str(item.get("confidence", "?")), quality=str(item.get("market_quality", "?")),
                        volume=str(item.get("volume_pressure", "?")), tf=str(item.get("aligned_tfs", "?")),
                        mid=str(item.get("mid_aligned", "?")), trend=str(structure.get("trend", "?")),
                        ready=str(structure.get("ready", False)), brk=str(item.get("v73_breakout", "?")),
                        retest=str(item.get("v73_hold_retest", "?")), trig=str(item.get("v73_trigger15m", "?")),
                        path=str(item.get("entry_path", "-")), gate=str(item.get("entry_gate", "NOT-EVALUATED")),
                        error=str(item.get("entry_exception", "-"))))
            with open(path, "w", encoding="utf-8") as handle:
                handle.write("\n".join(rows) + "\n")
        except Exception as error:
            # Keep the worker alive but surface the reason the report could not be written.
            self.entry_diagnostics_write_error = "DIAGNOSTICS WRITE {}: {}".format(type(error).__name__, str(error)[:160])

    def selected_market(self):
        if self.coin_spinner.text != "BEST":
            coin = self.coin_spinner.text
            item = next((x for x in self.coins if x["coin"] == coin), None)
            if not item or not item.get("TMN"):
                return None
            a = self.decision.analyze(item["TMN"])
            return {"coin": coin, "symbol": item["TMN"], **a}
        return self.best_candidate(exclude_symbols={p["symbol"] for p in self.demo_positions})

    def _v56_stage_status(self, stage, detail=""):
        self.entry_diagnostic = "V79 WAIT | " + str(stage) + (" | " + str(detail) if detail else "")
        try:
            self.update_auto_label()
        except Exception:
            pass

    def auto_trade_cycle(self, candidate_override=None):
        if not self.auto_running or not self.auto_entry_armed or len(self.demo_positions) >= MAX_POSITIONS:
            return
        if time.time() < self.cooldown_until or self.motor_balance <= 0:
            return

        # V79: once a candidate enters the timing window, do NOT run the old
        # two-scan gate again. Re-evaluate all currently safe candidates on
        # every worker cycle so the market can change its mind during 20-90s.
        timing_state = getattr(self, "v79_timing", None)
        if timing_state:
            exclude = {p["symbol"] for p in self.demo_positions}
            live_candidates = []
            for x in self.ranked_markets:
                if not self.allowed_market(x) or x.get("symbol") in exclude:
                    continue
                if x.get("signal") not in ("BUY", "SELL"):
                    continue
                if self.symbol_cooldowns.get(x.get("symbol"), 0) > time.time():
                    continue
                safe, reason = self._entry_safety(x)
                x["entry_gate"] = reason
                if not safe:
                    continue
                px = self.live_price(x.get("symbol")) or self.data.price(x.get("symbol"))
                if px is None or float(px) <= 0:
                    continue
                x["candidate_price"] = float(px)
                live_candidates.append(x)

            # V84: timing belongs to the same setup that started the window.
            # Do not switch to a new top-ranked market mid-window and restart
            # its clock merely because rankings fluctuate.
            timing_key = timing_state.get("key")
            candidate = next((x for x in live_candidates
                              if (x.get("symbol"), x.get("signal"), x.get("entry_path")) == timing_key), None)
            if candidate is None:
                timing_state["invalid_scans"] = int(timing_state.get("invalid_scans", 0)) + 1
            else:
                timing_state["invalid_scans"] = 0
        else:
            # V84 FIX: use the candidate already confirmed by the background worker.
            # Re-running best_candidate() on the UI thread created a separate confirmation
            # counter and could keep resetting the two-scan gate forever.
            candidate = candidate_override or self.best_candidate(
                exclude_symbols={p["symbol"] for p in self.demo_positions}
            )

        if not candidate:
            active_timing = getattr(self, "v79_timing", None)
            if active_timing:
                invalid_scans = int(active_timing.get("invalid_scans", 0))
                if invalid_scans < V84_TIMING_INVALID_SCANS_TO_CANCEL:
                    self.entry_diagnostic = "V84 TIMING HOLD | {} | SETUP TEMPORARILY NOT SAFE {}/{}".format(
                        active_timing.get("key", ("?",))[0], invalid_scans,
                        V84_TIMING_INVALID_SCANS_TO_CANCEL)
                    self.last_auto_action = self.entry_diagnostic
                    self.update_auto_label()
                    return
                self.v79_timing = None
                self.entry_diagnostic = "V84 TIMING CANCEL | SETUP INVALID IN {} SCANS | RESCAN 17 TMN".format(invalid_scans)
                self.last_auto_action = self.entry_diagnostic
                self.update_auto_label()
                return
            self.last_auto_action = self.entry_diagnostic or "V84 WAIT | 17 TMN | SCANNING"
            self.update_auto_label()
            return

        active_timing = getattr(self, "v79_timing", None)
        if active_timing and time.time() - float(active_timing.get("started", time.time())) >= V79_TIMING_MAX_WAIT_SECONDS:
            expired_key = active_timing.get("key", ("?", "?", "?"))
            self.v79_timing = None
            self.entry_diagnostic = "V84 TIMING EXPIRED | {} {} {} | FRESH CONFIRMATION REQUIRED".format(
                expired_key[0], expired_key[1], expired_key[2])
            self.last_auto_action = self.entry_diagnostic
            self.update_auto_label()
            return

        symbol = candidate.get("symbol")
        side = candidate.get("signal")
        path = candidate.get("entry_path", "?")
        live_now = self.live_price(symbol) or self.data.price(symbol)
        approved = candidate.get("candidate_price")
        if live_now is None or approved is None or float(approved) <= 0:
            active = getattr(self, "v79_timing", None)
            if active and time.time() - float(active.get("started", time.time())) >= V79_TIMING_MAX_WAIT_SECONDS:
                self.v79_timing = None
                self.entry_diagnostic = "V84 TIMING EXPIRED | NO FRESH PRICE | RESCAN 17 TMN"
            else:
                self._v56_stage_status("V84 FINAL LIVE PRICE", "BLOCK")
            return

        now = time.time()
        key = (symbol, side, path)
        timing = self.v79_timing
        if not timing or timing.get("key") != key:
            timing = {
                "key": key,
                "started": now,
                "baseline": float(approved),
                "last_price": float(live_now),
                "scans": 1,
                "best_timing": None,
                "invalid_scans": 0,
            }
            self.v79_timing = timing
            self.entry_diagnostic = "V84 TIMING START | {} {} {} | WINDOW {}-{}s".format(
                candidate.get("coin", "?"), side, path,
                int(V79_TIMING_MIN_WAIT_SECONDS), int(V79_TIMING_MAX_WAIT_SECONDS))
            self.last_auto_action = self.entry_diagnostic
            self.update_auto_label()
            return

        timing["last_price"] = float(live_now)
        timing["scans"] = int(timing.get("scans", 0)) + 1
        elapsed = now - float(timing.get("started", now))
        baseline = float(timing.get("baseline", live_now))
        move = (float(live_now) - baseline) / baseline * 100.0 if baseline > 0 else 0.0
        m1 = candidate.get("entry_1m_change")
        try:
            m1 = float(m1) if m1 is not None else None
        except (TypeError, ValueError):
            m1 = None

        # V79 dynamic timing: a BUY wants a calm/retest or rebound after the
        # initial setup; a SELL wants the symmetric condition. A fast adverse
        # move invalidates the timing window rather than forcing an entry.
        if side == "BUY":
            adverse = move < -V79_TIMING_MAX_ADVERSE_PCT
            chased = move > V79_TIMING_MAX_FAVORABLE_PCT
            rebound = m1 is not None and m1 >= -V79_TIMING_REBOUND_1M_PCT
            timing_score = (1 if rebound else 0) + (1 if not chased else 0) + (1 if abs(move) <= V79_TIMING_MAX_FAVORABLE_PCT else 0)
        else:
            adverse = move > V79_TIMING_MAX_ADVERSE_PCT
            chased = move < -V79_TIMING_MAX_FAVORABLE_PCT
            rebound = m1 is not None and m1 <= V79_TIMING_REBOUND_1M_PCT
            timing_score = (1 if rebound else 0) + (1 if not chased else 0) + (1 if abs(move) <= V79_TIMING_MAX_FAVORABLE_PCT else 0)

        if adverse:
            self.v79_timing = None
            self.entry_diagnostic = "V84 TIMING RESET | {} {} | MOVE {:+.2f}% | STRUCT/PRICE CHANGED".format(candidate.get("coin", "?"), side, move)
            self.last_auto_action = self.entry_diagnostic
            self.update_auto_label()
            return

        final_drift = abs(float(live_now) - float(approved)) / float(approved) * 100.0
        if final_drift > ENTRY_MAX_FINAL_PRICE_DRIFT_PCT:
            if elapsed >= V79_TIMING_MAX_WAIT_SECONDS:
                self.v79_timing = None
                self.entry_diagnostic = "V84 TIMING EXPIRED | {} | DRIFT {:.2f}% > {:.2f}% | RESCAN 17 TMN".format(
                    candidate.get("coin", "?"), final_drift, ENTRY_MAX_FINAL_PRICE_DRIFT_PCT)
            else:
                self.entry_diagnostic = "V84 TIMING BLOCK | {} | DRIFT {:.2f}% | {:.0f}/{:.0f}s".format(
                    candidate.get("coin", "?"), final_drift, elapsed, V79_TIMING_MAX_WAIT_SECONDS)
            self.last_auto_action = self.entry_diagnostic
            self.update_auto_label()
            return

        timing_good = (elapsed >= V79_TIMING_MIN_WAIT_SECONDS and timing_score >= 2)
        if timing_good:
            timing["best_timing"] = {"time": now, "score": timing_score, "move": move}

        if elapsed < V79_TIMING_MIN_WAIT_SECONDS:
            self.entry_diagnostic = "V84 TIMING WAIT | {} {} | {:.0f}/{:.0f}s | MOVE {:+.2f}% M1 {} SCORE {}/3".format(
                candidate.get("coin", "?"), side, elapsed, V79_TIMING_MIN_WAIT_SECONDS, move,
                "---" if m1 is None else "{:+.2f}%".format(m1), timing_score)
            self.last_auto_action = self.entry_diagnostic
            self.update_auto_label()
            return

        # V79 does not blindly enter at 90s. It needs a fresh favorable timing
        # point plus the already-qualified structure/volume/quality candidate.
        # If the window expires without that point, abandon the setup safely.
        if timing_good:
            if self.open_demo_position(candidate):
                self.v79_timing = None
                self.auto_entry_armed = False
                self.last_auto_action = "V84 ENTRY #{} {} {} S{} C{} | TIMING {:.0f}s | DYNAMIC CONFIRMED".format(
                    self.next_position_id - 1, candidate["coin"], candidate["signal"],
                    candidate["score"], candidate["confidence"], elapsed)
                self.entry_diagnostic = "V84 OPEN | {} | MOVE {:+.2f}% | TIMING SCORE {}/3".format(path, move, timing_score)
                self.update_auto_label(); self.update_mode_buttons()
            return

        if elapsed < V79_TIMING_MAX_WAIT_SECONDS:
            self.entry_diagnostic = "V84 TIMING SEARCH | {} {} | {:.0f}/{:.0f}s | MOVE {:+.2f}% M1 {} SCORE {}/3".format(
                candidate.get("coin", "?"), side, elapsed, V79_TIMING_MAX_WAIT_SECONDS, move,
                "---" if m1 is None else "{:+.2f}%".format(m1), timing_score)
            self.last_auto_action = self.entry_diagnostic
            self.update_auto_label()
            return

        self.v79_timing = None
        self.entry_diagnostic = "V84 TIMING EXPIRED | {} {} | 90s WITHOUT SAFE MOMENT | RESCAN 17 TMN".format(candidate.get("coin", "?"), side)
        self.last_auto_action = self.entry_diagnostic
        self.update_auto_label()

    # ---------- Modes ----------
    def on_leverage_change(self, spinner, text):
        try:
            self.leverage = max(1, min(10, int(str(text).replace("x", ""))))
        except (TypeError, ValueError):
            self.leverage = 1

    def on_capital_change(self, instance, value):
        self.trade_percent = int(round(value))
        self.capital_label.text = "{}%".format(self.trade_percent)
        self.update_balance()

    def set_auto_mode(self, *_):
        self.manual_mode = False
        self.auto_running = True
        self.last_auto_action = "AUTO mode"
        self.update_auto_label(); self.update_mode_buttons()

    def set_manual_mode(self, *_):
        self.manual_mode = True
        self.auto_running = False
        self.auto_entry_armed = False
        self.v79_timing = None
        self.last_auto_action = "MANUAL mode | SELECT COIN"
        self.update_auto_label(); self.update_mode_buttons()
        # V76 FIX: pressing MANUAL immediately opens the V72-style coin list.
        try:
            Clock.schedule_once(lambda dt: self.coin_spinner.trigger_action(duration=0), 0)
        except Exception:
            pass

    def start_auto(self, *_):
        self.manual_mode = False
        self.auto_running = True
        # START AUTO authorizes exactly ONE automatic entry.
        # Additional positions still require the user to press ARM ENTRY again.
        self.auto_entry_armed = (len(self.demo_positions) < MAX_POSITIONS)
        self.v79_timing = None
        self.last_auto_action = "STARTED | ONE ENTRY ARMED" if self.auto_entry_armed else "STARTED | NO SLOT"
        self.update_auto_label(); self.update_mode_buttons()

    def stop_auto(self, *_):
        self.auto_running = False
        self.manual_mode = True
        self.auto_entry_armed = False
        self.v79_timing = None
        self.last_auto_action = "STOPPED | OPEN POSITIONS REMAIN ACTIVE"
        self.update_auto_label(); self.update_mode_buttons()

    def arm_auto_entry(self, *_):
        if not self.auto_running or self.manual_mode or len(self.demo_positions) >= MAX_POSITIONS:
            self.last_auto_action = "START AUTO first / slot available"
        else:
            self.auto_entry_armed = not self.auto_entry_armed
            self.last_auto_action = "ONE ENTRY ARMED" if self.auto_entry_armed else "ENTRY DISARMED"
        self.update_auto_label(); self.update_mode_buttons()

    def update_auto_label(self):
        mode = "AUTO" if not self.manual_mode else "MANUAL"
        run = "RUNNING" if self.auto_running else "STOPPED"
        arm = "ON" if self.auto_entry_armed else "OFF"
        self.auto_label.text = "MODE {} | {} | ARM {} | {} | POS {}/{}".format(mode, run, arm, self.last_auto_action, len(self.demo_positions), MAX_POSITIONS)

    def update_mode_buttons(self):
        self.start_button.disabled = self.auto_running
        self.stop_button.disabled = not self.auto_running
        self.auto_entry_button.disabled = (not self.auto_running) or self.manual_mode or len(self.demo_positions) >= MAX_POSITIONS
        self.auto_entry_button.text = "ARM ENTRY ON" if self.auto_entry_armed else "ARM ENTRY OFF"
        slots = len(self.demo_positions) >= MAX_POSITIONS
        self.buy_button.disabled = (not self.manual_mode) or slots
        self.sell_button.disabled = (not self.manual_mode) or slots
        self.close_button.disabled = not bool(self.demo_positions)
        self.tp_button.disabled = not bool(self.demo_positions)
        self.sl_button.disabled = not bool(self.demo_positions)
        self.clear_exit_button.disabled = not bool(self.demo_positions)

    # ---------- Position operations ----------
    def get_position_by_id(self, pid):
        return next((p for p in self.demo_positions if p["id"] == pid), None)

    def open_position_for_symbol(self, symbol):
        return next((p for p in self.demo_positions if p["symbol"] == symbol), None)

    def open_demo_position(self, item):
        if not item or len(self.demo_positions) >= MAX_POSITIONS:
            return False
        symbol = item.get("symbol")
        side = item.get("signal")
        if not symbol or side not in ("BUY", "SELL") or self.open_position_for_symbol(symbol):
            return False
        entry = self.live_price(symbol)
        if entry is None or self.motor_balance <= 0:
            return False
        # V61: automatic entries must carry a structural stop from the same
        # structure engine before capital is committed. No entry with SL=None.
        entry_structural_sl = item.get("entry_structural_sl")
        if not self.manual_mode and self.auto_running:
            try:
                snap = self.risk.structure_snapshot(symbol)
                if not snap.get("ready"):
                    return False
                temp_position = {"side": side, "entry": float(entry)}
                entry_structural_sl = self.risk.structural_stop(temp_position, snap)
                # V61 could reject an otherwise valid entry solely because the
                # latest swing-stop was not usable. V61 uses the confirmed H1
                # zone as a fallback; the risk engine will tighten/replace it.
                if entry_structural_sl is None:
                    zone = snap.get("h1_zone") or {}
                    if side == "BUY":
                        support = zone.get("support")
                        if support and support < float(entry):
                            entry_structural_sl = float(support)
                    else:
                        resistance = zone.get("resistance")
                        if resistance and resistance > float(entry):
                            entry_structural_sl = float(resistance)
            except Exception:
                entry_structural_sl = None
            # A structure-qualified candidate may open without a precomputed
            # SL; RiskEngine will establish the structural stop on its next pass.
        margin = min(self.motor_balance * self.trade_percent / 100.0, self.motor_balance)
        exposure = margin * self.leverage
        if margin <= 0:
            return False
        self.motor_balance -= margin
        position = {
            "id": self.next_position_id, "coin": item.get("coin", self.market_coin_name(symbol)), "symbol": symbol,
            "side": side, "entry": entry, "amount": margin, "margin": margin, "exposure": exposure,
            "leverage": self.leverage, "score": item.get("score", 0), "confidence": item.get("confidence", 0),
            "opened_at": time.time(), "peak_net_pnl_pct": 0.0, "trailing_active": False,
            "reversal_confirmations": 0, "last_reversal_score": 0, "user_tp_price": None, "user_sl_price": None, "structural_sl_price": entry_structural_sl, "profit_state": "WAIT", "risk_state": "WAIT", "profit_invalidations": 0, "h4_trend": "NEUTRAL", "h1_zone": None, "breakout_ok": False, "pullback_ok": False, "trigger15m_ok": False,
        }
        self.next_position_id += 1
        self.demo_positions.append(position)
        self.selected_position_id = position["id"]
        self.metrics["entries"] += 1
        self.update_balance(); self.update_position_display(); self.update_position_spinner()
        self._save_paper_state()
        self._start_position_guard()
        return True

    def manual_buy(self, *_):
        if not self.manual_mode:
            return
        item = self.selected_market()
        if item:
            item["signal"] = "BUY"
            self.open_demo_position(item)

    def manual_sell(self, *_):
        if not self.manual_mode:
            return
        item = self.selected_market()
        if item:
            item["signal"] = "SELL"
            self.open_demo_position(item)

    def manual_close(self, *_):
        p = self.get_position_by_id(self.selected_position_id) or (self.demo_positions[0] if self.demo_positions else None)
        if not p:
            return
        current = self.live_price(p["symbol"])
        if current is None:
            return
        self.close_demo_position(p, current, self.risk.current_pnl_percent(p, current), "MANUAL CLOSE")

    # ---------- User price exits ----------
    def parse_price(self, text):
        try:
            raw = str(text).replace(",", "").strip()
            value = float(raw)
            return value if value > 0 else None
        except (TypeError, ValueError):
            return None

    def set_user_tp(self, *_):
        p = self.get_position_by_id(self.selected_position_id)
        value = self.parse_price(self.tp_input.text)
        if p and value:
            p["user_tp_price"] = value
            self.last_auto_action = "USER TP SET {:,.2f} TOMAN".format(value)
            self.update_position_display(); self.update_auto_label()

    def set_user_sl(self, *_):
        p = self.get_position_by_id(self.selected_position_id)
        value = self.parse_price(self.sl_input.text)
        if p and value:
            p["user_sl_price"] = value
            self.last_auto_action = "USER SL SET {:,.2f} TOMAN".format(value)
            self.update_position_display(); self.update_auto_label()

    def clear_user_exits(self, *_):
        p = self.get_position_by_id(self.selected_position_id)
        if p:
            p["user_tp_price"] = None
            p["user_sl_price"] = None
            self.tp_input.text = ""
            self.sl_input.text = ""
            self.last_auto_action = "USER TP/SL CLEARED"
            self.update_position_display(); self.update_auto_label()

    # ---------- Selection ----------
    def on_coin_selected(self, spinner, text):
        return

    def on_position_selected(self, spinner, text):
        self.selected_position_id = None
        if text and text != "NONE":
            try:
                self.selected_position_id = int(str(text).split(" ", 1)[0].lstrip("#"))
            except (TypeError, ValueError):
                self.selected_position_id = None
        p = self.get_position_by_id(self.selected_position_id)
        if p:
            self.tp_input.text = "" if p.get("user_tp_price") is None else self.format_price(p["user_tp_price"])
            self.sl_input.text = "" if p.get("user_sl_price") is None else self.format_price(p["user_sl_price"])
        self.update_position_display()

    # ---------- Close / history ----------
    def close_demo_position(self, position, current, raw_pnl_pct, reason):
        if position not in self.demo_positions:
            return
        net_pct = raw_pnl_pct - FEE_PERCENT_PER_SIDE * 2.0
        pnl = position.get("exposure", position["amount"]) * net_pct / 100.0
        returned = max(0.0, position["margin"] + pnl)
        self.motor_balance += returned
        self.trade_history.append({
            "id": position["id"], "coin": position["coin"], "side": position["side"], "entry": position["entry"], "exit": current,
            "margin": position["margin"], "exposure": position["exposure"], "leverage": position["leverage"],
            "opened_at": position["opened_at"], "closed_at": time.time(), "pnl": pnl, "net_pnl_pct": net_pct,
            "reason": reason, "confidence": position.get("confidence", 0), "tp": position.get("user_tp_price"), "sl": position.get("user_sl_price")
        })
        self.demo_positions.remove(position)
        self.symbol_cooldowns[position["symbol"]] = time.time() + SYMBOL_COOLDOWN_SECONDS
        self.metrics["exits"] += 1
        self.metrics["net_pnl"] += pnl
        if pnl >= 0:
            self.metrics["wins"] += 1
        else:
            self.metrics["losses"] += 1
        self.metrics["peak_balance"] = max(self.metrics["peak_balance"], self.motor_balance)
        drawdown = self.metrics["peak_balance"] - self.motor_balance
        self.metrics["max_drawdown"] = max(self.metrics["max_drawdown"], drawdown)
        if self.selected_position_id == position["id"]:
            self.selected_position_id = self.demo_positions[0]["id"] if self.demo_positions else None
        self.cooldown_until = time.time() + REFRESH_SECONDS + 2
        self.last_auto_action = "CLOSED #{} {} {} {:+,.0f} | {}".format(position["id"], position["coin"], reason, pnl, len(self.demo_positions))
        self.update_auto_label(); self.update_position_display(); self.update_balance(); self.update_history(); self.update_mode_buttons()
        self._save_paper_state()
        if not self.demo_positions:
            self._stop_position_guard()

    # ---------- Display ----------
    def format_price(self, value):
        if value is None:
            return "---"
        if value >= 1000:
            return "{:,.2f}".format(value)
        if value >= 1:
            return "{:,.4f}".format(value)
        return "{:,.8f}".format(value)

    def format_tmn(self, value):
        return "---" if value is None else "{:,.0f}".format(value)

    def update_balance(self):
        self.balance_label.text = "BAL {:,.0f} TOMAN | CAP {}% | OPEN {}/{} | DD {:,.0f}".format(self.motor_balance, self.trade_percent, len(self.demo_positions), MAX_POSITIONS, self.metrics["max_drawdown"])

    def update_position_spinner(self):
        values = ["NONE"]
        for p in self.demo_positions:
            values.append("#{} {} {} | {}".format(p["id"], p["side"], p["coin"], self.format_price(p["entry"])))
        self.position_spinner.values = tuple(values)
        selected = next((v for v in values if v.startswith("#{} ".format(self.selected_position_id))), None)
        if selected is None and self.demo_positions:
            selected = values[1]
            self.selected_position_id = self.demo_positions[0]["id"]
        self.position_spinner.text = selected if selected else "NONE"

    def update_position_display(self):
        if not self.demo_positions:
            self.position_label.text = "POSITIONS: NONE"
            self.entry_label.text = "ENTRY: ---"
            self.current_label.text = "CURRENT: ---"
            self.pl_label.text = "P/L: ---"
            self._update_last_closed_label()
            self.update_position_spinner()
            return
        lines = []
        total = 0.0
        for p in self.demo_positions:
            current = self.live_price(p["symbol"]) or self.data.price(p["symbol"])
            if current is None:
                net = 0.0; pnl_value = 0.0; net_text = "---"
            else:
                raw = self.risk.current_pnl_percent(p, current)
                net = raw - FEE_PERCENT_PER_SIDE * 2.0
                pnl_value = p["exposure"] * net / 100.0
                net_text = "{:+.2f}%".format(net)
                total += pnl_value
            peak = p.get("peak_net_pnl_pct", 0.0)
            trail = "ON" if p.get("trailing_active") else "WAIT"
            lines.append("#{} {} {} E{} C{} P/L{:+,.0f} N{} SL{} | {}".format(p["id"], p["side"], p["coin"], self.format_price(p["entry"]), current and self.format_price(current) or "---", pnl_value, net_text, p.get("structural_sl_price") and self.format_price(p["structural_sl_price"]) or "-", p.get("profit_state", "WAIT")))
        self.position_label.text = "TOTAL OPEN P/L {:+,.0f} TOMAN | ".format(total) + "\n".join(lines)
        selected = self.get_position_by_id(self.selected_position_id) or self.demo_positions[0]
        self.selected_position_id = selected["id"]
        current = self.live_price(selected["symbol"]) or self.data.price(selected["symbol"])
        self.entry_label.text = "SELECT #{} {} {} | E {} | M {:,.0f} | {}x | C{}".format(selected["id"], selected["side"], selected["coin"], self.format_price(selected["entry"]), selected["margin"], selected["leverage"], selected.get("confidence", 0))
        if current is None:
            self.current_label.text = "CURRENT --- | {}".format(selected["symbol"])
            self.pl_label.text = "P/L ---"
        else:
            raw = self.risk.current_pnl_percent(selected, current)
            net = raw - FEE_PERCENT_PER_SIDE * 2.0
            pnl = selected["exposure"] * net / 100.0
            _, price_source, price_age = self.live_price_detail(selected["symbol"])
            age_text = "?" if price_age is None else "{:.1f}s".format(price_age)
            self.current_label.text = "CURRENT {} {} | {} | SRC {} AGE {} | WS#{} | t={}".format(
                self.format_price(current), selected["symbol"], selected["symbol"], price_source,
                age_text, getattr(self, "ws_price_updates", 0), time.strftime("%H:%M:%S"))
            self.pl_label.text = "#{} NET {:+,.0f} TOMAN | {:+.2f}% | PEAK {:+.2f}% | {}".format(selected["id"], pnl, net, selected.get("peak_net_pnl_pct", 0.0), "TRAIL ON" if selected.get("trailing_active") else "TRAIL WAIT")
        self.update_position_spinner()

    def _update_last_closed_label(self):
        if not getattr(self, "last_closed_label", None):
            return
        if not self.trade_history:
            self.last_closed_label.text = "LAST CLOSED: ---"
            return
        item = self.trade_history[-1]
        self.last_closed_label.text = (
            "LAST CLOSED #{} {} {} | ENTRY {} | EXIT {} | P/L {:+,.0f} TOMAN | {}".format(
                item.get("id", "-"), item.get("side", "-"), item.get("coin", "-"),
                self.format_price(item.get("entry")), self.format_price(item.get("exit")),
                float(item.get("pnl", 0.0) or 0.0), item.get("reason", "")
            )
        )

    def update_history(self):
        self._update_last_closed_label()
        if not self.trade_history:
            self.history_label.text = "TRADES 0 | ENGINE: V9 score primary / confidence filter"
            return
        wins = self.metrics["wins"]; losses = self.metrics["losses"]; net = self.metrics["net_pnl"]
        lines = ["TRADES {} | W{} L{} | NET {:+,.0f} | DD {:,.0f}".format(len(self.trade_history), wins, losses, net, self.metrics["max_drawdown"])]
        for item in self.trade_history[-3:][::-1]:
            lines.append(">>> CLOSED #{} {} {} | {} -> {} | P/L {:+,.0f} | {}".format(item["id"], item["side"], item["coin"], self.format_price(item["entry"]), self.format_price(item["exit"]), item["pnl"], item["reason"]))
        self.history_label.text = "\n".join(lines)

    def show_page(self):
        self.market_grid.clear_widgets()
        total = len(self.display_coins)
        if not total:
            return
        pages = (total + ITEMS_PER_PAGE - 1) // ITEMS_PER_PAGE
        self.page = max(0, min(self.page, pages - 1))
        start = self.page * ITEMS_PER_PAGE
        for item in self.display_coins[start:start + ITEMS_PER_PAGE]:
            symbol = item.get("TMN")
            a = self.decision.analyze(symbol) if symbol else {"signal": "HOLD", "power": "-", "score": 0, "confidence": 0}
            stats = self.data.stats(symbol)
            qm = next((x for x in self.ranked_markets if x.get("symbol") == symbol), {})
            spread_txt = "-" if qm.get("spread_pct") is None else "{:.2f}".format(qm.get("spread_pct"))
            depth_txt = "-" if qm.get("depth_ratio") is None else "{:.2f}".format(qm.get("depth_ratio"))
            rvol_txt = "-" if qm.get("rvol") is None else "{:.2f}".format(qm.get("rvol"))
            vals = [
                item["coin"], self.format_price(self.live_price(item.get("USDT"))), self.format_tmn(self.live_price(symbol)),
                self.change_text(self.data.recent_change(symbol, 300)), self.change_text(self.data.recent_change(symbol, 900)), self.change_text(self.data.recent_change(symbol, 1800)),
                self.change_text(self.data.recent_change(symbol, 3600)), self.change_text(self.data.recent_change(symbol, 7200)), a["signal"], a["power"], str(a["score"]), str(a["confidence"]),
                str(qm.get("market_quality", 50)), spread_txt, depth_txt, rvol_txt, str(stats.get("lastTradeSide", "---"))
            ]
            for value in vals:
                self.market_grid.add_widget(Label(text=str(value), font_size=6, size_hint_y=None, height=23))
        self.page_label.text = "PAGE {}/{} | 17 COINS | Q>={} | API {} | POS {}/{}".format(self.page + 1, pages, MARKET_QUALITY_THRESHOLD, len(self.data.symbols), len(self.demo_positions), MAX_POSITIONS)
        self.previous_button.disabled = self.page == 0
        self.next_button.disabled = self.page >= pages - 1

    def change_text(self, value):
        return "---" if value is None else "{:+.2f}%".format(value)

    def update_summary(self):
        vals = []
        for coin in ("BTC", "ETH", "SOL"):
            item = next((x for x in self.coins if x["coin"] == coin), None)
            usdt_symbol = item.get("USDT") if item else None
            tmn_symbol = item.get("TMN") if item else None
            usdt = self.live_price(usdt_symbol) if usdt_symbol else None
            tmn = self.live_price(tmn_symbol) if tmn_symbol else None
            vals.append("{} | $ {} | TMN {}".format(coin, self.format_price(usdt), self.format_tmn(tmn)))
        self.summary_label.text = "   ".join(vals)


    # ---------- V80 unified live-price resolver ----------
    @staticmethod
    def normalize_symbol_key(symbol):
        return str(symbol or "").upper().replace("/", "").replace("-", "").replace("_", "").replace(" ", "")

    def canonical_symbol(self, symbol):
        """Resolve WebSocket forms such as XRPTMN to the API key XRP/TMN."""
        if not symbol:
            return None
        raw = str(symbol).strip()
        if raw in getattr(self.data, "symbols", {}):
            return raw
        wanted = self.normalize_symbol_key(raw)
        candidates = list(getattr(self.data, "symbols", {}).keys())
        for coin in getattr(self, "coins", []):
            for key in ("TMN", "USDT"):
                value = coin.get(key)
                if value:
                    candidates.append(value)
        for candidate in candidates:
            if self.normalize_symbol_key(candidate) == wanted:
                return candidate
        # Unknown symbols are not silently rewritten; retain raw key for diagnostics.
        return raw

    def apply_live_price(self, symbol, price):
        try:
            px = float(price)
            if px <= 0 or not math.isfinite(px):
                return
            canonical = self.canonical_symbol(symbol)
            if not canonical:
                return
            now = time.time()
            self.live_prices[canonical] = px
            self.live_price_times[canonical] = now
            self.last_ws_price_time = now
            self.ws_price_updates = getattr(self, "ws_price_updates", 0) + 1
            item = self.data.symbols.get(canonical)
            if isinstance(item, dict):
                item.setdefault("stats", {})["lastPrice"] = px
            else:
                self.data.symbols[canonical] = {"symbol": canonical, "stats": {"lastPrice": px}}
        except (TypeError, ValueError):
            return

    def live_price_detail(self, symbol):
        """Return (price, source, age_seconds); stale WebSocket data is never trusted indefinitely."""
        if not symbol:
            return None, "NONE", None
        canonical = self.canonical_symbol(symbol)
        now = time.time()
        px = self.live_prices.get(canonical)
        stamp = self.live_price_times.get(canonical, 0.0)
        if px is not None and stamp and now - stamp <= LIVE_PRICE_MAX_AGE_SECONDS:
            return px, "WS", max(0.0, now - stamp)
        rest_px = self.data.price(canonical) or self.data.price(symbol)
        if rest_px is not None:
            return rest_px, "REST", (max(0.0, now - self.last_rest_price_time) if self.last_rest_price_time else None)
        return None, "NONE", None

    def live_price(self, symbol):
        return self.live_price_detail(symbol)[0]

    def websocket_price_loop(self):
        while getattr(self, "websocket_running", False):
            ws = None
            try:
                symbols = self.websocket_symbols()
                if not symbols:
                    time.sleep(1.0)
                    continue
                ws = websocket.create_connection(WEBSOCKET_URL, timeout=8, enable_multithread=True)
                ws.settimeout(5)
                for symbol in symbols:
                    channel = str(symbol).upper().replace("/", "") + "@marketCap"
                    ws.send(json.dumps(["subscribe", {"channel": channel}]))
                while self.websocket_running:
                    try:
                        raw = ws.recv()
                        if not raw:
                            break
                        payload = json.loads(raw)
                        if not isinstance(payload, list) or len(payload) < 2:
                            continue
                        channel, data = payload[0], payload[1]
                        if not isinstance(channel, str) or not channel.endswith("@marketCap") or not isinstance(data, dict):
                            continue
                        symbol = data.get("symbol") or channel.split("@", 1)[0]
                        price = data.get("lastPrice")
                        if price is not None:
                            self.apply_live_price(symbol, price)
                            Clock.schedule_once(self.fast_price_ui_update, 0)
                    except websocket.WebSocketTimeoutException:
                        continue
                    except (websocket.WebSocketConnectionClosedException, ConnectionError, OSError):
                        break
                    except Exception:
                        continue
            except Exception:
                time.sleep(2)
            finally:
                try:
                    if ws is not None:
                        ws.close()
                except Exception:
                    pass
            if self.websocket_running:
                time.sleep(1)

    # ---------- Fast fallback REST price loop ----------
    def fast_price_fetch(self):
        try:
            response = requests.get(API_URL, timeout=2.5)
            response.raise_for_status()
            data = response.json()
            symbols = data.get("result", {}).get("symbols", {})
            if isinstance(symbols, dict) and symbols:
                # Keep the complete API market map current. WebSocket prices are
                # overlaid afterward by apply_live_price(), so this does not
                # sacrifice V15 live-price behavior.
                self.data.symbols = symbols
                now = time.time()
                self.last_rest_price_time = now
                for live_symbol, live_px in list(self.live_prices.items()):
                    stamp = self.live_price_times.get(live_symbol, 0.0)
                    if stamp and now - stamp <= LIVE_PRICE_MAX_AGE_SECONDS:
                        item = self.data.symbols.get(live_symbol)
                        if isinstance(item, dict):
                            item.setdefault("stats", {})["lastPrice"] = live_px
                self.make_coin_list()
                Clock.schedule_once(self.fast_price_ui_update, 0)
        except Exception:
            pass

    def fast_price_loop(self):
        while getattr(self, "fast_price_running", False):
            started = time.time()
            self.fast_price_fetch()
            elapsed = time.time() - started
            time.sleep(max(0.5, FAST_PRICE_SECONDS - elapsed))

    def fast_price_ui_update(self, dt):
        if not getattr(self, "data", None):
            return
        try:
            self.update_summary()
            self.update_position_display()
            self.update_balance()
        except Exception as error:
            try:
                self.status_label.text = "V84 PRICE/UI WARNING | {}".format(error)[:220]
            except Exception:
                pass

    # ---------- V44 background entry worker ----------
    def start_engine_worker(self, *_):
        if self.engine_worker_running:
            return
        self.engine_worker_running = True
        self.worker_cycles += 1
        self.worker_last_started = time.time()
        threading.Thread(target=self._engine_worker, daemon=True).start()

    def _engine_worker(self):
        host = self.worker_host
        try:
            host.symbol_cooldowns = dict(self.symbol_cooldowns)
            host.demo_positions = [dict(p) for p in self.demo_positions]
            host.data.fetch()
            host.make_coin_list()
            target = [x.get("TMN") for x in host.coins if x.get("TMN")]
            host.data.prefetch_entry_candles(target, workers=4)
            host.decision.clear_cache()
            host.scan_market()
            candidate = host.best_candidate(exclude_symbols={p["symbol"] for p in host.demo_positions})
            host.write_entry_diagnostics()
            symbols_snapshot = dict(host.data.symbols)
            history_snapshot = {k: list(v) for k, v in host.data.history.items()}
            last_sample_snapshot = dict(host.data.last_sample)
            candle_snapshot = {k: dict(v) for k, v in host.data.candle_cache.items()}
            ranked_snapshot = [dict(x) for x in host.ranked_markets]
            coins_snapshot = [dict(x) for x in host.coins]
            diagnostic = getattr(host, "entry_diagnostic", "V84 WAIT")
            base_engine_text = getattr(host.engine_label, "text", "")
            engine_text = (base_engine_text + " | " + diagnostic)[:240] if base_engine_text else diagnostic[:240]
            def apply_result(dt):
                self._apply_engine_result(symbols_snapshot, history_snapshot, last_sample_snapshot, candle_snapshot, ranked_snapshot, coins_snapshot, candidate, diagnostic, engine_text)
            Clock.schedule_once(apply_result, 0)
        except Exception as error:
            msg = str(error)[:180]
            def apply_error(dt):
                self.engine_worker_error = msg
                self.status_label.text = "V85 WORKER ERROR | {}".format(msg)[:240]
                self.last_auto_action = "WORKER ERROR | {}".format(msg)
                self.update_auto_label()
            Clock.schedule_once(apply_error, 0)
        finally:
            self.engine_worker_running = False

    def _apply_engine_result(self, symbols, history, last_sample, candle_cache, ranked, coins, candidate, diagnostic, engine_text):
        try:
            self.data.symbols = symbols
            self.data.history = history
            self.data.last_sample = last_sample
            self.data.candle_cache = candle_cache
            self.decision.clear_cache()
            self.ranked_markets = ranked
            self.coins = coins
            self.display_coins = list(coins)
            self.entry_diagnostic = diagnostic or "V79 WAIT | TREND -> RANGE EDGE -> BREAKOUT | safety blocks only"
            vals = ["BEST"] + [x["coin"] for x in self.coins]
            self.coin_spinner.values = tuple(vals)
            if self.coin_spinner.text not in vals:
                self.coin_spinner.text = "USDT"
            if engine_text:
                self.engine_label.text = engine_text[:240]
            if self.auto_running and self.auto_entry_armed and candidate:
                # Worker-confirmed candidate enters/advances the timing gate.
                Clock.schedule_once(lambda dt, c=candidate: self.auto_trade_cycle(c), 0)
            elif self.auto_running and self.auto_entry_armed and self.v79_timing:
                # V83 bug: when a timing window was active but the worker did not
                # produce a freshly confirmed candidate, no cycle ran at all.
                # Re-evaluate the existing timing setup; do not run best_candidate
                # on the UI thread or create a second confirmation counter.
                Clock.schedule_once(lambda dt: self.auto_trade_cycle(None), 0)
            elif self.auto_running:
                self.last_auto_action = self.entry_diagnostic
                self.update_auto_label()
            self.show_page(); self.update_summary(); self.update_balance(); self.update_history(); self.update_position_display(); self.update_mode_buttons()
            self.status_label.text = "CONNECTED | API {} | V86 ANDROID GUARD | 17 TMN | DEMO ONLY | POS {}/{}".format(len(self.data.symbols), len(self.demo_positions), MAX_POSITIONS)
            self.last_engine_update = time.time()
        except Exception as error:
            self.status_label.text = "V65 APPLY ERROR | {}".format(error)[:240]

    # ---------- Refresh ----------
    def refresh(self, dt):
        # V47 FIX: V46 only fetched markets inside the AUTO worker. That meant
        # a fresh/manual launch had an empty market map, so the BTC/ETH/SOL
        # summary and all 17 TMN rows stayed blank. Bootstrap the API map once
        # before rendering, then the fast REST/WebSocket loops maintain prices.
        if not self.data.symbols:
            try:
                self.data.fetch()
                self.make_coin_list()
            except Exception as error:
                self.status_label.text = "V47 API BOOTSTRAP ERROR | {}".format(error)[:240]
        if self.auto_running and not self.engine_worker_running:
            self.start_engine_worker()
        if self.demo_positions and not getattr(self, "_v86_resume_sync_pending", False):
            try:
                self.risk.manage()
            except Exception as error:
                self.status_label.text = "V47 RISK WARNING | {}".format(error)[:240]
        try:
            self.show_page(); self.update_summary(); self.update_balance(); self.update_history(); self.update_position_display(); self.update_mode_buttons()
        except Exception as error:
            self.status_label.text = "V47 UI WARNING | {}".format(error)[:240]

    def previous_page(self, *_):
        if self.page > 0:
            self.page -= 1
            self.show_page()

    def next_page(self, *_):
        pages = (len(self.display_coins) + ITEMS_PER_PAGE - 1) // ITEMS_PER_PAGE
        if self.page < pages - 1:
            self.page += 1
            self.show_page()

    def _poll_v86_service_resume(self, dt):
        ack_path = self._v86_control_path("wallex7_v86_resume.ack")
        acknowledged = os.path.exists(ack_path)
        timed_out = time.time() >= getattr(self, "_v86_resume_sync_deadline", 0)
        if not acknowledged and not timed_out:
            return True
        try:
            if os.path.exists(ack_path):
                os.remove(ack_path)
            paused_path = self._v86_control_path("wallex7_v86_ui_paused.flag")
            if os.path.exists(paused_path):
                os.remove(paused_path)
            request_path = self._v86_control_path("wallex7_v86_resume.request")
            if os.path.exists(request_path):
                os.remove(request_path)
        except Exception:
            pass
        self._sync_service_state()
        self.update_position_display()
        self.update_balance()
        self.update_history()
        self.update_mode_buttons()
        self._v86_resume_sync_pending = False
        if not acknowledged:
            try:
                self.status_label.text = "SERVICE SYNC TIMEOUT | UI RISK MANAGEMENT RESUMED"
            except Exception:
                pass
        if not self.demo_positions:
            self._stop_position_guard()
        return False

    def on_pause(self):
        self._save_paper_state()
        if self.demo_positions:
            try:
                for filename in ("wallex7_v86_resume.request", "wallex7_v86_resume.ack"):
                    path = self._v86_control_path(filename)
                    if os.path.exists(path):
                        os.remove(path)
                paused_path = self._v86_control_path("wallex7_v86_ui_paused.flag")
                with open(paused_path, "w", encoding="utf-8") as handle:
                    handle.write(str(time.time()))
            except Exception:
                pass
            self._start_position_guard()
        return True

    def on_resume(self):
        try:
            if self.demo_positions:
                # Ask the service to finish its current risk pass and acknowledge
                # before the UI resumes risk management, avoiding concurrent closes.
                self._v86_resume_sync_pending = True
                self._start_position_guard()
                request_path = self._v86_control_path("wallex7_v86_resume.request")
                with open(request_path, "w", encoding="utf-8") as handle:
                    handle.write(str(time.time()))
                self._v86_resume_sync_deadline = time.time() + 30.0
                Clock.schedule_interval(self._poll_v86_service_resume, 0.5)
            else:
                paused_path = self._v86_control_path("wallex7_v86_ui_paused.flag")
                if os.path.exists(paused_path):
                    os.remove(paused_path)
                self._sync_service_state()
        except Exception:
            self._v86_resume_sync_pending = False
        return True

    def on_stop(self):
        self._save_paper_state()
        # Do not stop the foreground service here: Android may destroy the UI
        # process while the user expects an open position to remain protected.
        self.fast_price_running = False
        self.websocket_running = False
        self.engine_worker_running = False


if __name__ == "__main__":
    Wallex7App().run()
