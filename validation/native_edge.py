"""Assemble writeexc.asm (x86 and x64) and run validation/native/edge_vectors.c against it (errata/limitations: evidence, not proof)."""
import subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
vc = Path(r"C:\Program Files\Microsoft Visual Studio\18\Enterprise\VC\Auxiliary\Build\vcvarsall.bat")
if not vc.exists():
    out = subprocess.run([r"C:\Program Files (x86)\Microsoft Visual Studio\Installer\vswhere.exe", "-latest", "-property", "installationPath"],
                         capture_output=True, text=True, stdin=subprocess.DEVNULL).stdout.strip()
    vc = Path(out) / r"VC\Auxiliary\Build\vcvarsall.bat"
d = ROOT / "validation/native"
rc = 0
for arch, ml, flag in (("x86", "ml /nologo /c", ""), ("x64", "ml64 /nologo /c /DX64", "")):
    cmd = (rf'call "{vc}" {arch} >nul && cd /d "{d}" && {ml} /Fo we_{arch}.obj ..\..\writeexc.asm && '
           rf'cl /nologo /O2 /Fe:edge_{arch}.exe /Fo.\ edge_vectors.c ..\..\spectreopt.c we_{arch}.obj /link /SECTION:.text,ERW && .\edge_{arch}.exe')
    r = subprocess.run('cmd /s /c "' + cmd + '"', capture_output=True, text=True, errors="replace", stdin=subprocess.DEVNULL, timeout=900)
    print(arch, "exit", r.returncode); print(r.stdout[-1200:], r.stderr[-400:])
    rc |= r.returncode
sys.exit(rc)
