"""Build and run the legacy writeexec harness in Debug/Release x Win32/x64.
Pass = build succeeds and the exe prints no mismatch line (it prints only on mismatch, then timings).
Usage: python validation/native.py [--toolset v143] [--configs Debug|x64 ...] [--no-run]"""
import argparse, json, subprocess, sys, time
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
VS = Path(r"C:\Program Files\Microsoft Visual Studio\18\Enterprise")
def vcvars(): 
    p = VS / r"VC\Auxiliary\Build\vcvarsall.bat"
    if not p.exists():
        out = subprocess.run([r"C:\Program Files (x86)\Microsoft Visual Studio\Installer\vswhere.exe", "-latest", "-property", "installationPath"], capture_output=True, text=True).stdout.strip()
        p = Path(out) / r"VC\Auxiliary\Build\vcvarsall.bat"
    return p
def main():
    ap = argparse.ArgumentParser(); ap.add_argument("--toolset"); ap.add_argument("--no-run", action="store_true")
    ap.add_argument("--project", default="writeexec"); ap.add_argument("--configs", nargs="*", default=["Debug|Win32", "Release|Win32", "Debug|x64", "Release|x64"])
    a = ap.parse_args(); results = {}
    for cfg in a.configs:
        conf, plat = cfg.split("|"); arch = "x86" if plat == "Win32" else "x64"
        ts = f" /p:PlatformToolset={a.toolset}" if a.toolset else ""
        outdir = ROOT / "build" / "msbuild" / plat / conf
        cmd = f'call "{vcvars()}" {arch} >nul && msbuild vs/{a.project}/{a.project}.vcxproj /nologo /v:m /p:Configuration={conf} /p:Platform={plat}{ts}'
        start = time.time(); t = start; b = subprocess.run('cmd /s /c "' + cmd + '"', cwd=ROOT, capture_output=True, text=True, errors="replace")
        rec = {"build_ok": b.returncode == 0, "build_seconds": round(time.time() - t)}
        if b.returncode: rec["build_tail"] = (b.stdout + b.stderr)[-1500:]
        elif not a.no_run:
            exe = next(iter(sorted(outdir.glob(a.project + ".exe"))), None)
            if exe is None or exe.stat().st_mtime < max((ROOT / 'src' / f).stat().st_mtime for f in ('writeexc.asm', 'writeexec.c', 'spectreopt.c')):
                rec.update(build_ok=False, build_tail="exe missing or stale: " + str(exe)); results[cfg] = rec; print(cfg, json.dumps(rec), flush=True); continue
            rec["exe"] = str(exe)
            t = time.time(); r = subprocess.run([str(exe)], cwd=outdir, capture_output=True, text=True, errors="replace", timeout=3000)
            lines = [l for l in r.stdout.splitlines() if l.strip()]
            mism = [l for l in lines if not l.startswith("Time:")]
            rec.update(exit=r.returncode, run_seconds=round(time.time() - t), mismatch_output=mism[:5], pass_=(r.returncode == 0 and not mism))
        results[cfg] = rec; print(cfg, json.dumps(rec), flush=True)
    sys.exit(0 if all(v.get("pass_", v["build_ok"] and a.no_run) for v in results.values()) else 1)
main()
