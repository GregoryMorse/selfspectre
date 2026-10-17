"""Build the AES and RSA demos without touching the Defender-blocked PoC."""
from pathlib import Path
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
VC = Path(r"C:\Program Files\Microsoft Visual Studio\18\Enterprise\VC\Auxiliary\Build\vcvarsall.bat")
if not VC.exists():
    vswhere = Path(r"C:\Program Files (x86)\Microsoft Visual Studio\Installer\vswhere.exe")
    install = subprocess.run([str(vswhere), "-latest", "-property", "installationPath"],
                             capture_output=True, text=True, check=True).stdout.strip()
    VC = Path(install) / "VC/Auxiliary/Build/vcvarsall.bat"
ARCH = sys.argv[1] if len(sys.argv) > 1 else "x64"
if ARCH not in ("x64", "x86"):
    sys.exit("usage: build_native_demos.py [x64|x86]")
OUT = ROOT / "build/native" / ARCH / "Release"
OUT.mkdir(parents=True, exist_ok=True)

def run(command):
    result = subprocess.run('cmd /s /c "call "' + str(VC) + '" ' + ARCH + ' >nul && ' + command + '"',
                            cwd=ROOT, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, errors="replace")
    print(result.stdout, end="")
    if result.returncode:
        sys.exit(result.returncode)

timer_probe = OUT / "cpu_timer_features.exe"
run(f'cl /nologo /O2 /Fe:"{timer_probe}" '
    f'"{ROOT / "validation/native/cpu_timer_features.c"}"')
timer_code = subprocess.run([str(timer_probe)], cwd=ROOT).returncode
if timer_code not in (0, 3):
    sys.exit("CPU lacks the RDTSC/RDTSCP timing features required by these demos")
use_rdtsc = timer_code == 3 or os.environ.get("WE_FORCE_RDTSC") == "1"
timer_flags = " /DNORDTSCP" if use_rdtsc else ""
print("Timer build: " + ("RDTSC+LFENCE" if use_rdtsc else "RDTSCP"))

for name, source in (("selfspectre", "spectreaes"), ("spectrersa", "spectrersa")):
    obj = OUT / f"{source}.obj"
    core = OUT / "spectreopt.obj"
    run(f'cl /nologo /O2 /Gy /Oi /Qspectre-{timer_flags} /I"{ROOT / "src"}" /c '
        f'/Fo:"{obj}" "{ROOT / "src" / (source + ".c")}"')
    run(f'cl /nologo /O2 /Gy /Oi /Qspectre- /I"{ROOT / "src"}" /c '
        f'/Fo:"{core}" "{ROOT / "src/spectreopt.c"}"')
    asm = ""
    if name == "spectrersa":
        asm_obj = OUT / "spectrecode.obj"
        assembler = "ml64 /DX64" if ARCH == "x64" else "ml /safeseh"
        run(f'{assembler} /nologo /Fo"{asm_obj}" /c "{ROOT / "src/spectrecode.asm"}"')
        asm = f' "{asm_obj}"'
    exe = OUT / f"{name}.exe"
    safeseh = "" if ARCH == "x64" else " /SAFESEH:NO"
    run(f'link /nologo /SECTION:.text,ERW{safeseh} /OUT:"{exe}" "{obj}" "{core}"{asm}')
    print(exe)

vectors = OUT / "code_vectors.exe"
run(f'cl /nologo /O2 /I"{ROOT / "src"}" /Fe:"{vectors}" '
    f'"{ROOT / "validation/native/code_vectors.c"}"')
print(vectors)
