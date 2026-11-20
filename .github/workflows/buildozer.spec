[app]
title = Wallex 7 V86 Diagnostic No Service
package.name = wallex7v86diagnostic
package.domain = org.wallex7
source.dir = .
source.include_exts = py,kv,png,jpg,atlas,json,txt
version = 86.0.1
requirements = python3,kivy==2.3.1,requests,websocket-client
orientation = portrait
fullscreen = 0
icon.filename = %(source.dir)s/icon.png


# Network permissions only; no Android foreground service in this diagnostic build.
android.permissions = INTERNET,ACCESS_NETWORK_STATE
android.api = 33
android.minapi = 23
android.ndk = 25b
android.archs = arm64-v8a, armeabi-v7a
android.accept_sdk_license = True

[buildozer]
log_level = 2
warn_on_root = 1
