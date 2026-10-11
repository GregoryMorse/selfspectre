"""Build and run validation/native/code_vectors.c (errata L02, L03 reference functions vs exact vectors)."""
import subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).parent))
vc = Path(r"C:\Program Files\Microsoft Visual Studio\18\Enterprise\VC\Auxiliary\Build\vcvarsall.bat")
d = ROOT / "validation/native"
cmd = rf'call "{vc}" x64 >nul && cd /d "{d}" && cl /nologo /O2 code_vectors.c /Fe:code_vectors.exe /Fo:code_vectors.obj && .\code_vectors.exe'
r = subprocess.run('cmd /s /c "' + cmd + '"', capture_output=True, text=True, errors="replace", stdin=subprocess.DEVNULL, timeout=600)
print(r.stdout[-1500:], r.stderr[-500:]); print("exit", r.returncode); sys.exit(r.returncode)
