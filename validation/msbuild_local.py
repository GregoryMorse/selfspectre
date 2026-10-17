"""Build the whole Visual Studio solution (vs/selfspectre.sln) in Debug/Release x Win32/x64; output goes to build/msbuild.
Usage: python validation/msbuild_local.py [Debug|Win32 ...]  (default: all four). Build only: the harnesses are run by CMake/ctest."""
import subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
vc = Path(r"C:\Program Files\Microsoft Visual Studio\18\Enterprise\VC\Auxiliary\Build\vcvarsall.bat")
if not vc.exists():
    out = subprocess.run([r"C:\Program Files (x86)\Microsoft Visual Studio\Installer\vswhere.exe", "-latest", "-property", "installationPath"],
                         capture_output=True, text=True, stdin=subprocess.DEVNULL).stdout.strip()
    vc = Path(out) / r"VC\Auxiliary\Build\vcvarsall.bat"
rc = 0
for cfg in sys.argv[1:] or ["Debug|Win32", "Release|Win32", "Debug|x64", "Release|x64"]:
    conf, plat = cfg.split("|"); arch = "x86" if plat == "Win32" else "x64"
    cmd = f'call "{vc}" {arch} >nul && msbuild vs\\selfspectre.sln /nologo /v:m /m:1 /p:Configuration={conf} /p:Platform={arch}'
    r = subprocess.run('cmd /s /c "' + cmd + '"', cwd=ROOT, capture_output=True, text=True, errors="replace", stdin=subprocess.DEVNULL, timeout=3000)
    print(cfg, "exit", r.returncode)
    if r.returncode: print((r.stdout + r.stderr)[-2500:])
    rc |= r.returncode
sys.exit(rc)
