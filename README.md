# UltraCalc

Calculator, equation validator (`1+1=11` → ✘ Wrong) and grapher (y = f(x), polar, parametric, GPU 3D).

## Run from source

```
pip install -r requirements.txt
python main.py                    # the app
python main.py "2^10" "5!=120"    # terminal mode
```

## Standalone builds

Ready-made Windows `.exe`, macOS `.app` and Linux `.AppImage` files come from the **Build** workflow
(Actions tab → Build → Run workflow, or push a `v*` tag to publish a Release).
To build for your own OS: `pip install -r requirements.txt pyinstaller && python packaging/build.py`.
