"""Build a standalone UltraCalc for the current OS.

    pip install -r requirements.txt pyinstaller
    python packaging/build.py

Output (in dist/, which is not committed):
    Windows  ->  UltraCalc.exe                 single file
    macOS    ->  UltraCalc.app + UltraCalc-macOS.zip
    Linux    ->  UltraCalc-x86_64.AppImage     needs appimagetool on PATH (or $APPIMAGETOOL)

PyInstaller can't cross-compile, so each OS builds its own binary; .github/workflows/build.yml
runs this script on Windows, macOS and Linux.
"""
import os
import platform
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PKG, DIST, BUILD = ROOT / "packaging", ROOT / "dist", ROOT / "build"
NAME = "UltraCalc"


def pyinstaller(onefile, icon):
    subprocess.run([
        sys.executable, "-m", "PyInstaller", str(ROOT / "main.py"),
        "--name", NAME, "--noconfirm", "--clean", "--windowed", "--icon", str(icon),
        "--onefile" if onefile else "--onedir",
        "--distpath", str(DIST), "--workpath", str(BUILD), "--specpath", str(BUILD),
        # loaded dynamically, so PyInstaller's import scan can't see them:
        "--collect-data", "customtkinter",                   # themes and fonts
        "--collect-all", "vispy",                            # shaders, fonts, the Tk backend
        "--hidden-import", "pyopengltk",
        "--hidden-import", "matplotlib.backends.backend_tkagg",
    ], check=True)


def build_windows():
    pyinstaller(onefile=True, icon=PKG / "icon.ico")
    return DIST / f"{NAME}.exe"


def build_macos():
    pyinstaller(onefile=False, icon=PKG / "icon.icns")
    shutil.rmtree(DIST / NAME, ignore_errors=True)  # the loose folder; the .app is what matters
    archive = DIST / f"{NAME}-macOS.zip"
    subprocess.run(["ditto", "-c", "-k", "--keepParent", str(DIST / f"{NAME}.app"), str(archive)], check=True)
    return archive


def build_linux():
    pyinstaller(onefile=False, icon=PKG / "icon.png")
    appdir = BUILD / "AppDir"
    shutil.rmtree(appdir, ignore_errors=True)
    (appdir / "usr" / "bin").mkdir(parents=True)
    shutil.move(str(DIST / NAME), appdir / "usr" / "bin" / NAME)
    apprun = appdir / "AppRun"
    apprun.write_text('#!/bin/sh\nHERE="$(dirname "$(readlink -f "$0")")"\n'
                      f'exec "$HERE/usr/bin/{NAME}/{NAME}" "$@"\n')
    apprun.chmod(0o755)
    (appdir / "ultracalc.desktop").write_text(
        "[Desktop Entry]\nType=Application\nName=UltraCalc\nComment=Calculator, equation validator and grapher\n"
        "Exec=UltraCalc\nIcon=ultracalc\nCategories=Utility;Calculator;Education;Math;\nTerminal=false\n")
    shutil.copy(PKG / "icon.png", appdir / "ultracalc.png")
    tool = os.environ.get("APPIMAGETOOL") or shutil.which("appimagetool")
    if not tool:
        sys.exit("appimagetool not found: put it on PATH or set APPIMAGETOOL")
    arch = platform.machine()
    image = DIST / f"{NAME}-{arch}.AppImage"
    subprocess.run([tool, "--no-appstream", str(appdir), str(image)], check=True, env={**os.environ, "ARCH": arch})
    return image


if __name__ == "__main__":
    builders = {"win32": build_windows, "darwin": build_macos}
    result = builders.get(sys.platform, build_linux)()
    print(f"\nBuilt {result.relative_to(ROOT)} ({result.stat().st_size / 1e6:.0f} MB)")
