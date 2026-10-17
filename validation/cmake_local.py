"""Configure, build and test the CMake project with MSVC on Windows (x86 and x64) from this checkout:
python validation/limited_run.py -- python validation/cmake_local.py [x86|x64] [ctest args...]"""
import subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
vc = Path(r"C:\Program Files\Microsoft Visual Studio\18\Enterprise\VC\Auxiliary\Build\vcvarsall.bat")
if not vc.exists():
    out = subprocess.run([r"C:\Program Files (x86)\Microsoft Visual Studio\Installer\vswhere.exe", "-latest", "-property", "installationPath"],
                         capture_output=True, text=True, stdin=subprocess.DEVNULL).stdout.strip()
    vc = Path(out) / r"VC\Auxiliary\Build\vcvarsall.bat"
arch = sys.argv[1] if len(sys.argv) > 1 else "x64"
ctest = " ".join(sys.argv[2:]) or "-R \"code_vectors|edge_vectors\""
build = ROOT / "build" / f"msvc-{arch}"
plat = {"x86": "Win32", "x64": "x64"}[arch]
# The Visual Studio generator locates the toolset itself (no vcvarsall needed).
sdk = Path(r"C:\Program Files (x86)\Windows Kitsin.0.26100.0d")  # rc.exe for the linker
cmd = (rf'call "{vc}" {arch} >nul && set "PATH={sdk};%PATH%" && cd /d "{ROOT}" && cmake -S . -B "{build}" -A {plat} && '
       rf'cmake --build "{build}" --config Release && cd /d "{build}" && ctest -C Release --output-on-failure {ctest}')
r = subprocess.run('cmd /s /c "' + cmd + '"', capture_output=True, text=True, errors="replace", stdin=subprocess.DEVNULL, timeout=3000)
print(r.stdout[-6000:], r.stderr[-1500:])
sys.exit(r.returncode)
