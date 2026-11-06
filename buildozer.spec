[app]
title = Wallex 7 V86 Demo
package.name = wallex7v86demo
package.domain = org.wallex7
source.dir = .
source.include_exts = py,kv,png,jpg,atlas,json,txt
version = 86.0.0
requirements = python3,kivy==2.3.1,requests,websocket-client,pyjnius
orientation = portrait
fullscreen = 0
icon.filename = %(source.dir)s/icon.png

# Android foreground service: protects existing PAPER positions while UI is paused.
services = PositionGuard:services/position_guard.py:foreground:sticky

# Network, foreground-service notification, and CPU wake lock permissions.
android.permissions = INTERNET,ACCESS_NETWORK_STATE,FOREGROUND_SERVICE,WAKE_LOCK,POST_NOTIFICATIONS
android.api = 33
android.minapi = 23
android.ndk = 25b
android.archs = arm64-v8a, armeabi-v7a
android.accept_sdk_license = True

[buildozer]
log_level = 2
warn_on_root = 1
