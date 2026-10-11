@echo off
call "C:\Program Files\Microsoft Visual Studio\18\Enterprise\VC\Auxiliary\Build\vcvarsall.bat" x64 >nul
cd /d %~dp0
cl /nologo /O2 code_vectors.c /Fe:code_vectors.exe /Fo:code_vectors.obj > build.log 2>&1
if errorlevel 1 (type build.log & exit /b 1)
code_vectors.exe
exit /b %errorlevel%
