module
import WriteExecute.X86.Fig6Final
import WriteExecute.X86.NotTable
import WriteExecute.Spec.X86
import WriteExecute.X86.LayoutData
meta import WriteExecute.X86.LayoutData
open WriteExecute.X86

/-! Prints the bytes the Lean byte model (`enc`) assigns to table entries and fixed procedure
instructions, at the section offsets of the assembled objects. validation/compare_listings.py compares
them with the `.text` of the COFF objects (published source: x86/x64, corrected source: x86c/x64c). -/

def hex (l : List Nat) : String :=
  String.join (l.map fun b => (if b < 16 then "0" else "") ++ String.ofList (Nat.toDigits 16 b))

def line (tag kind : String) (addr : Nat) (b : List Nat) : IO Unit :=
  IO.println s!"{tag} {kind} {addr} {hex b}"

def dump (tag : String) (mode : Mode) (corr : Bool) (notTab nzTab shlTab : List Nat)
    (notarg notres nzarg nzres shlarg4 shlres4 : Nat) : IO Unit := do
  for j in List.range 256 do
    let E := notTab.getD j 0
    line tag "not" E (enc (.movB (fld mode E 7 (notres + 6)) (255 - j)) ++
      jmpTo (nrT j) (E + 7) notres ++ List.replicate (if corr then tC j else tO j) 0x90)
    let Z := nzTab.getD j 0
    line tag "nz" Z (enc (.movB (fld mode Z 7 (nzres + 6)) (if j = 0 then 0 else 1)) ++
      jmpTo (nrT j) (Z + 7) nzres ++ List.replicate (if corr then tC j else tO j) 0x90)
    let S := shlTab.getD j 0
    line tag "shl4" S (enc (.movW (fld mode S 9 (shlres4 + 7)) (j * 2 ^ 4)) ++ enc (.jmp32 (jrel (S + 9) shlres4)))
  line tag "iX" shlarg4 (enc (.jmp32 (256 * 128)))
  line tag "i3not" (notarg + 27) (enc (.jmp32 (jrel (notarg + 27) shlarg4)))
  line tag "i3nz" (nzarg + 27) (enc (.jmp32 (jrel (nzarg + 27) shlarg4)))
  line tag "iNnot" notres (enc (.movB (fld mode notres 7 (notres + 6)) 0))
  line tag "iNnz" nzres (enc (.movB (fld mode nzres 7 (nzres + 6)) 0))

#eval show IO Unit from do
  dump "x86" .x86 false x86_notres_tab x86_nzres_tab x86_shlres4_tab x86_notarg x86_notres x86_nzarg x86_nzres x86_shlarg4 x86_shlres4
  dump "x64" .x64 false x64_notres_tab x64_nzres_tab x64_shlres4_tab x64_notarg x64_notres x64_nzarg x64_nzres x64_shlarg4 x64_shlres4
  dump "x86c" .x86 true x86c_notres_tab x86c_nzres_tab x86c_shlres4_tab x86c_notarg x86c_notres x86c_nzarg x86c_nzres x86c_shlarg4 x86c_shlres4
  dump "x64c" .x64 true x64c_notres_tab x64c_nzres_tab x64c_shlres4_tab x64c_notarg x64c_notres x64c_nzarg x64c_nzres x64c_shlarg4 x64c_shlres4

/-- Fig. 6: the whole `WriteExecXOR` image at the initial (unpatched, argument bytes `0`) values of the object:
both argument stages with their `SHL5`/`SHL4` tables, the three patches, the copy loop, the table jumps, the
256 group jumps and the 65,536 table entries (first 16 bytes of each, the NOP padding included). -/
def dumpXor (tag : String) (mode : Mode) (is86 : Bool) (A S5 R5 S4 R4 N : Nat) (grp shl5 shl4 : List Nat) :
    IO Unit := do
  let D2 := if is86 then A + 8315 else A + 118
  let J := if is86 then A + 8319 else A + 122
  let T2 := if is86 then A + 112 else A + 115
  line tag "xa1i0" A (enc (.movB (fld mode A 7 (S5 + 2)) 0))
  line tag "xa1i1" (A + 7) (enc (.movD (fld mode (A + 7) 10 (R5 + 3)) (fld mode R5 9 (A + 97))))
  line tag "xa1i2" (A + 17) (enc (.movD (fld mode (A + 17) 10 (R5 + 10)) (jrel (R5 + 9) (A + 32))))
  line tag "xa1i3" (A + 27) (enc (.jmp32 (jrel (A + 27) S5)))
  line tag "xa2i0" (A + 32) (enc (.movB (fld mode (A + 32) 7 (S4 + 2)) 0))
  line tag "xa2i1" (A + 39) (enc (.movD (fld mode (A + 39) 10 (R4 + 3)) (fld mode R4 9 D2)))
  line tag "xa2i2" (A + 49) (enc (.movD (fld mode (A + 49) 10 (R4 + 10)) (jrel (R4 + 9) (A + 64))))
  line tag "xa2i3" (A + 59) (enc (.jmp32 (jrel (A + 59) S4)))
  line tag "xiX5" S5 (enc (.jmp32 (256 * 128)))
  line tag "xp1" (A + 64) (enc (.movD (fld mode (A + 64) 10 (A + 93)) (fld mode (A + 90) 9 J)))
  line tag "xp2" (A + 74) (enc (.movB (fld mode (A + 74) 7 (A + 110)) 228))
  line tag "xp3" (A + 81) (enc (.jmp8 7))
  line tag "xxh" (A + 83) (enc (.movB (fld mode (A + 83) 7 (A + 110)) 0))
  line tag "xh1" (A + 90) (enc (.movW (fld mode (A + 90) 9 J) 32768))
  line tag "xh1b" (A + 99) (enc (.movD (fld mode (A + 99) 10 (A + 93)) (fld mode (A + 90) 9 T2)))
  line tag "xxl" (A + 109) (enc (.jmp8 228))
  if is86 then
    line tag "xjj" (A + 111) (enc (.jmp32 32768))
    line tag "xh2" (A + 8308) (enc (.movW (A + 8323) 32768))
    line tag "xxj" (A + 8317) (enc (.jmp32 (256 * 32768)))
    for i in List.range 256 do
      let E := A + 116 + 32 * i
      line tag "xej" E (enc (.movD (fld mode E 10 (A + 8311)) (A + 8323 + 8192 * i)) ++
        jmpTo (decide (i < 252)) (E + 10) (A + 8308) ++ List.replicate (if i < 252 then 17 else 20) 0x90)
  else
    line tag "xh2" (A + 111) (enc (.movW 6 32768))
    line tag "xxj" (A + 120) (enc (.jmp32 (256 * 32768)))
  for j in List.range 256 do
    let S := shl5.getD j 0
    line tag "shl5" S (enc (.movW (fld mode S 9 (R5 + 7)) (j * 2 ^ 5)) ++ enc (.jmp32 (jrel (S + 9) R5)))
  for i in List.range 256 do
    let G := grp.getD i 0
    line tag "xgj" G (enc (.jmp32 32768))
    let mut bs : List Nat := []
    for j in List.range 255 do
      let E := G + 5 + 16 * j
      bs := bs ++ enc (.movB (fld mode E 7 (N + 6)) (i ^^^ j)) ++ enc (.jmp32 (jrel (E + 7) N)) ++ List.replicate 4 0x90
    line tag "xent" (G + 5) bs
    let E := G + 5 + 16 * 255
    line tag "xent255" E (enc (.movB (fld mode E 7 (N + 6)) (i ^^^ 255)) ++ enc (.jmp32 (jrel (E + 7) N)))
  line tag "xiN" N (enc (.movB (fld mode N 7 (N + 6)) 0))

#eval show IO Unit from do
  dumpXor "x86" .x86 true x86_xorarg1 x86_shlarg5 x86_shlres5 x86_shlarg4 x86_shlres4 x86_xorres x86_xorarg1_tab x86_shlres5_tab x86_shlres4_tab
  dumpXor "x64" .x64 false x64_xorarg1 x64_shlarg5 x64_shlres5 x64_shlarg4 x64_shlres4 x64_xorres x64_xorarg1_tab x64_shlres5_tab x64_shlres4_tab
  dumpXor "x86c" .x86 true x86c_xorarg1 x86c_shlarg5 x86c_shlres5 x86c_shlarg4 x86c_shlres4 x86c_xorres x86c_xorarg1_tab x86c_shlres5_tab x86c_shlres4_tab
  dumpXor "x64c" .x64 false x64c_xorarg1 x64c_shlarg5 x64c_shlres5 x64c_shlarg4 x64c_shlres4 x64c_xorres x64c_xorarg1_tab x64c_shlres5_tab x64c_shlres4_tab
