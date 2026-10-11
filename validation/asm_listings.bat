@echo off
call "C:\Program Files\Microsoft Visual Studio\18\Enterprise\VC\Auxiliary\Build\vcvarsall.bat" x86 >nul
ml /nologo /c /Fl"x86.lst" /Sa /Fo"x86.obj" writeexc.asm
call "C:\Program Files\Microsoft Visual Studio\18\Enterprise\VC\Auxiliary\Build\vcvarsall.bat" x64 >nul
ml64 /nologo /c /DX64 /Fl"x64.lst" /Sa /Fo"x64.obj" writeexc.asm
