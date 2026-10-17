"""Build the standalone cache-timing diagnostic into validation/.build."""
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
VC = Path(r"C:\Program Files\Microsoft Visual Studio\18\Enterprise\VC\Auxiliary\Build\vcvarsall.bat")
if not VC.exists():
    vswhere = Path(r"C:\Program Files (x86)\Microsoft Visual Studio\Installer\vswhere.exe")
    install = subprocess.run([str(vswhere), "-latest", "-property", "installationPath"],
                             capture_output=True, text=True, check=True).stdout.strip()
    VC = Path(install) / "VC/Auxiliary/Build/vcvarsall.bat"
OUT = ROOT / "validation/.build/cache_timing.exe"
OUT.parent.mkdir(parents=True, exist_ok=True)
command = f'call "{VC}" x64 >nul && cl /nologo /O2 /W4 /Fe:"{OUT}" "{ROOT / "validation/native/cache_timing.c"}"'
result = subprocess.run("cmd /s /c \"" + command + "\"", cwd=OUT.parent, text=True,
                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, errors="replace")
print(result.stdout, end="")
sys.exit(result.returncode)
