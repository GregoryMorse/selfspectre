import WriteExecute.X86.Fig5Final
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
