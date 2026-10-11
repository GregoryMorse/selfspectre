module
public import WriteExecute.X86.LayoutData

public section

namespace WriteExecute.X86

/-- C16 (Fig. 5), x86 build of the published `writeexc.asm`: for every argument byte `k`, execution from
`notarg` reaches the return jump target `Dd - 1` after `14` steps (`17` when the lookup lands in the NOP
slide, `k ≥ 248`), having stored `255 - k` at `Dd`; every write is to an instruction field. -/
theorem fig5_x86 (B0 : Nat) (m : Mem) (Dd k d0 w0 r0 : Nat) (hk : k < 256)
    (hDd : B0 + x86_notres + 12 ≤ Dd) (hbig : Dd + 1 < 2 ^ 30)
    (img : NotImg Mode.x86 m (B0 + x86_notarg) (B0 + x86_shlarg4) (B0 + x86_shlres4) (B0 + x86_notres)
      Dd k d0 w0 r0)
    (hEnt : ∀ j, j < 256 → Code m (B0 + x86_notres_tab.getD j 0)
      (enc (.movB (fld Mode.x86 (B0 + x86_notres_tab.getD j 0) 7 (B0 + x86_notres + 6)) ((fun i => 255 - i) j)) ++
        (jmpTo (nrT j) (B0 + x86_notres_tab.getD j 0 + 7) (B0 + x86_notres) ++
          List.replicate (tO j) 0x90))) :
    ∃ mEnd, runN Mode.x86 ((if 248 ≤ k then 3 else 0) + 14) (B0 + x86_notarg, m) = some (Dd - 1, mEnd) ∧
      mEnd Dd = 255 - k ∧
      ∀ x, ¬(x = B0 + x86_shlarg4 + 2 ∨ (B0 + x86_shlres4 + 3 ≤ x ∧ x < B0 + x86_shlres4 + 9) ∨
        (B0 + x86_shlres4 + 10 ≤ x ∧ x < B0 + x86_shlres4 + 14) ∨
        (B0 + x86_notarg + 33 ≤ x ∧ x < B0 + x86_notarg + 35) ∨ x = B0 + x86_notres + 6 ∨ x = Dd) →
        mEnd x = m x := by
  obtain ⟨g1, g2, g3, g4, g5, g6, -⟩ := x86_geometry
  have hE : ∀ j, j < 256 → B0 + x86_notres_tab.getD j 0 = Eo (B0 + x86_notarg + 37) j := by
    intro j hj
    rw [x86_notres_offsets j hj]
    unfold Eo; omega
  exact fig5_original Mode.x86 m (B0 + x86_notarg) (B0 + x86_shlarg4) (B0 + x86_shlres4)
    (B0 + x86_notres) Dd k d0 w0 r0 (fun i => 255 - i) (fun i _ => by omega) hk (by omega) (by omega) (by omega) hDd hbig img
    (fun j hj => by
      have := hEnt j hj
      rw [hE j hj] at this
      exact this)

/-- C16 (Fig. 5), x64 build of the published `writeexc.asm`: for every argument byte `k`, execution from
`notarg` reaches the return jump target `Dd - 1` after `14` steps (`17` when the lookup lands in the NOP
slide, `k ≥ 248`), having stored `255 - k` at `Dd`; every write is to an instruction field. -/
theorem fig5_x64 (B0 : Nat) (m : Mem) (Dd k d0 w0 r0 : Nat) (hk : k < 256)
    (hDd : B0 + x64_notres + 12 ≤ Dd) (hbig : Dd + 1 < 2 ^ 30)
    (img : NotImg Mode.x64 m (B0 + x64_notarg) (B0 + x64_shlarg4) (B0 + x64_shlres4) (B0 + x64_notres)
      Dd k d0 w0 r0)
    (hEnt : ∀ j, j < 256 → Code m (B0 + x64_notres_tab.getD j 0)
      (enc (.movB (fld Mode.x64 (B0 + x64_notres_tab.getD j 0) 7 (B0 + x64_notres + 6)) ((fun i => 255 - i) j)) ++
        (jmpTo (nrT j) (B0 + x64_notres_tab.getD j 0 + 7) (B0 + x64_notres) ++
          List.replicate (tO j) 0x90))) :
    ∃ mEnd, runN Mode.x64 ((if 248 ≤ k then 3 else 0) + 14) (B0 + x64_notarg, m) = some (Dd - 1, mEnd) ∧
      mEnd Dd = 255 - k ∧
      ∀ x, ¬(x = B0 + x64_shlarg4 + 2 ∨ (B0 + x64_shlres4 + 3 ≤ x ∧ x < B0 + x64_shlres4 + 9) ∨
        (B0 + x64_shlres4 + 10 ≤ x ∧ x < B0 + x64_shlres4 + 14) ∨
        (B0 + x64_notarg + 33 ≤ x ∧ x < B0 + x64_notarg + 35) ∨ x = B0 + x64_notres + 6 ∨ x = Dd) →
        mEnd x = m x := by
  obtain ⟨g1, g2, g3, g4, g5, g6, -⟩ := x64_geometry
  have hE : ∀ j, j < 256 → B0 + x64_notres_tab.getD j 0 = Eo (B0 + x64_notarg + 37) j := by
    intro j hj
    rw [x64_notres_offsets j hj]
    unfold Eo; omega
  exact fig5_original Mode.x64 m (B0 + x64_notarg) (B0 + x64_shlarg4) (B0 + x64_shlres4)
    (B0 + x64_notres) Dd k d0 w0 r0 (fun i => 255 - i) (fun i _ => by omega) hk (by omega) (by omega) (by omega) hDd hbig img
    (fun j hj => by
      have := hEnt j hj
      rw [hE j hj] at this
      exact this)

/-! NZ: the same procedure with the table of `(Index NE 0) and 1`. -/

/-- C16 (Fig. 5), x86 build of the published `writeexc.asm`: for every argument byte `k`, execution from
`nzarg` reaches the return jump target `Dd - 1` after `14` steps (`17` when the lookup lands in the NOP
slide, `k ≥ 248`), having stored `(k ≠ 0)` at `Dd`; every write is to an instruction field. -/
theorem fig5_nz_x86 (B0 : Nat) (m : Mem) (Dd k d0 w0 r0 : Nat) (hk : k < 256)
    (hDd : B0 + x86_nzres + 12 ≤ Dd) (hbig : Dd + 1 < 2 ^ 30)
    (img : NotImg Mode.x86 m (B0 + x86_nzarg) (B0 + x86_shlarg4) (B0 + x86_shlres4) (B0 + x86_nzres)
      Dd k d0 w0 r0)
    (hEnt : ∀ j, j < 256 → Code m (B0 + x86_nzres_tab.getD j 0)
      (enc (.movB (fld Mode.x86 (B0 + x86_nzres_tab.getD j 0) 7 (B0 + x86_nzres + 6)) ((fun i => if i = 0 then 0 else 1) j)) ++
        (jmpTo (nrT j) (B0 + x86_nzres_tab.getD j 0 + 7) (B0 + x86_nzres) ++
          List.replicate (tO j) 0x90))) :
    ∃ mEnd, runN Mode.x86 ((if 248 ≤ k then 3 else 0) + 14) (B0 + x86_nzarg, m) = some (Dd - 1, mEnd) ∧
      mEnd Dd = (if k = 0 then 0 else 1) ∧
      ∀ x, ¬(x = B0 + x86_shlarg4 + 2 ∨ (B0 + x86_shlres4 + 3 ≤ x ∧ x < B0 + x86_shlres4 + 9) ∨
        (B0 + x86_shlres4 + 10 ≤ x ∧ x < B0 + x86_shlres4 + 14) ∨
        (B0 + x86_nzarg + 33 ≤ x ∧ x < B0 + x86_nzarg + 35) ∨ x = B0 + x86_nzres + 6 ∨ x = Dd) →
        mEnd x = m x := by
  obtain ⟨-, -, -, -, -, -, g1, g2, g3⟩ := x86_geometry
  have g4 : x86_shlres4 + 14 ≤ x86_nzarg := by decide
  obtain ⟨g5, -, -, -, -, -, -, -, -⟩ := x86_geometry
  have hE : ∀ j, j < 256 → B0 + x86_nzres_tab.getD j 0 = Eo (B0 + x86_nzarg + 37) j := by
    intro j hj
    rw [x86_nzres_offsets j hj]
    unfold Eo; omega
  exact fig5_original Mode.x86 m (B0 + x86_nzarg) (B0 + x86_shlarg4) (B0 + x86_shlres4)
    (B0 + x86_nzres) Dd k d0 w0 r0 (fun i => if i = 0 then 0 else 1) (fun i _ => by split <;> omega) hk (by omega) (by omega) (by omega) hDd hbig img
    (fun j hj => by
      have := hEnt j hj
      rw [hE j hj] at this
      exact this)

/-- C16 (Fig. 5), x64 build of the published `writeexc.asm`: for every argument byte `k`, execution from
`nzarg` reaches the return jump target `Dd - 1` after `14` steps (`17` when the lookup lands in the NOP
slide, `k ≥ 248`), having stored `(k ≠ 0)` at `Dd`; every write is to an instruction field. -/
theorem fig5_nz_x64 (B0 : Nat) (m : Mem) (Dd k d0 w0 r0 : Nat) (hk : k < 256)
    (hDd : B0 + x64_nzres + 12 ≤ Dd) (hbig : Dd + 1 < 2 ^ 30)
    (img : NotImg Mode.x64 m (B0 + x64_nzarg) (B0 + x64_shlarg4) (B0 + x64_shlres4) (B0 + x64_nzres)
      Dd k d0 w0 r0)
    (hEnt : ∀ j, j < 256 → Code m (B0 + x64_nzres_tab.getD j 0)
      (enc (.movB (fld Mode.x64 (B0 + x64_nzres_tab.getD j 0) 7 (B0 + x64_nzres + 6)) ((fun i => if i = 0 then 0 else 1) j)) ++
        (jmpTo (nrT j) (B0 + x64_nzres_tab.getD j 0 + 7) (B0 + x64_nzres) ++
          List.replicate (tO j) 0x90))) :
    ∃ mEnd, runN Mode.x64 ((if 248 ≤ k then 3 else 0) + 14) (B0 + x64_nzarg, m) = some (Dd - 1, mEnd) ∧
      mEnd Dd = (if k = 0 then 0 else 1) ∧
      ∀ x, ¬(x = B0 + x64_shlarg4 + 2 ∨ (B0 + x64_shlres4 + 3 ≤ x ∧ x < B0 + x64_shlres4 + 9) ∨
        (B0 + x64_shlres4 + 10 ≤ x ∧ x < B0 + x64_shlres4 + 14) ∨
        (B0 + x64_nzarg + 33 ≤ x ∧ x < B0 + x64_nzarg + 35) ∨ x = B0 + x64_nzres + 6 ∨ x = Dd) →
        mEnd x = m x := by
  obtain ⟨-, -, -, -, -, -, g1, g2, g3⟩ := x64_geometry
  have g4 : x64_shlres4 + 14 ≤ x64_nzarg := by decide
  obtain ⟨g5, -, -, -, -, -, -, -, -⟩ := x64_geometry
  have hE : ∀ j, j < 256 → B0 + x64_nzres_tab.getD j 0 = Eo (B0 + x64_nzarg + 37) j := by
    intro j hj
    rw [x64_nzres_offsets j hj]
    unfold Eo; omega
  exact fig5_original Mode.x64 m (B0 + x64_nzarg) (B0 + x64_shlarg4) (B0 + x64_shlres4)
    (B0 + x64_nzres) Dd k d0 w0 r0 (fun i => if i = 0 then 0 else 1) (fun i _ => by split <;> omega) hk (by omega) (by omega) (by omega) hDd hbig img
    (fun j hj => by
      have := hEnt j hj
      rw [hE j hj] at this
      exact this)

/-! The corrected source (L04): uniform 16-byte entries, 14 steps for every `k`. -/

/-- C16 (Fig. 5), x86 build of the corrected `writeexc.asm` (erratum L04): from `not` execution reaches the
return jump target `Dd - 1` after exactly `14` steps for every argument byte `k` (no NOP slide), having stored
`255 - k` at `Dd`; every write is to an instruction field. -/
theorem fig5c_x86 (B0 : Nat) (m : Mem) (Dd k d0 w0 r0 : Nat) (hk : k < 256)
    (hDd : B0 + x86c_notres + 12 ≤ Dd) (hbig : Dd + 1 < 2 ^ 30)
    (img : NotImg Mode.x86 m (B0 + x86c_notarg) (B0 + x86c_shlarg4) (B0 + x86c_shlres4)
      (B0 + x86c_notres) Dd k d0 w0 r0)
    (hEnt : ∀ j, j < 256 → Code m (B0 + x86c_notres_tab.getD j 0)
      (enc (.movB (fld Mode.x86 (B0 + x86c_notres_tab.getD j 0) 7 (B0 + x86c_notres + 6)) ((fun i => 255 - i) j)) ++
        (jmpTo (nrT j) (B0 + x86c_notres_tab.getD j 0 + 7) (B0 + x86c_notres) ++
          List.replicate (tC j) 0x90))) :
    ∃ mEnd, runN Mode.x86 14 (B0 + x86c_notarg, m) = some (Dd - 1, mEnd) ∧
      mEnd Dd = 255 - k ∧
      ∀ x, ¬(x = B0 + x86c_shlarg4 + 2 ∨ (B0 + x86c_shlres4 + 3 ≤ x ∧ x < B0 + x86c_shlres4 + 9) ∨
        (B0 + x86c_shlres4 + 10 ≤ x ∧ x < B0 + x86c_shlres4 + 14) ∨
        (B0 + x86c_notarg + 33 ≤ x ∧ x < B0 + x86c_notarg + 35) ∨ x = B0 + x86c_notres + 6 ∨ x = Dd) →
        mEnd x = m x := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := x86c_geometry
  have g10 : x86c_shlres4 + 14 ≤ x86c_notarg := by decide
  exact fig5_corrected Mode.x86 m (B0 + x86c_notarg) (B0 + x86c_shlarg4) (B0 + x86c_shlres4)
    (B0 + x86c_notres) Dd k d0 w0 r0 (fun i => 255 - i) (fun i _ => by omega) hk (by omega) (by omega) (by omega) hDd hbig img
    (fun j hj => by
      have := hEnt j hj
      rw [x86c_notres_offsets j hj] at this
      rw [show B0 + (x86c_notarg + 37 + 16 * j) = B0 + x86c_notarg + 37 + 16 * j by omega] at this
      exact this)

/-- C16 (NZ) (Fig. 5), x86 build of the corrected `writeexc.asm` (erratum L04): from `nz` execution reaches the
return jump target `Dd - 1` after exactly `14` steps for every argument byte `k` (no NOP slide), having stored
`(k ≠ 0)` at `Dd`; every write is to an instruction field. -/
theorem fig5c_nz_x86 (B0 : Nat) (m : Mem) (Dd k d0 w0 r0 : Nat) (hk : k < 256)
    (hDd : B0 + x86c_nzres + 12 ≤ Dd) (hbig : Dd + 1 < 2 ^ 30)
    (img : NotImg Mode.x86 m (B0 + x86c_nzarg) (B0 + x86c_shlarg4) (B0 + x86c_shlres4)
      (B0 + x86c_nzres) Dd k d0 w0 r0)
    (hEnt : ∀ j, j < 256 → Code m (B0 + x86c_nzres_tab.getD j 0)
      (enc (.movB (fld Mode.x86 (B0 + x86c_nzres_tab.getD j 0) 7 (B0 + x86c_nzres + 6)) ((fun i => if i = 0 then 0 else 1) j)) ++
        (jmpTo (nrT j) (B0 + x86c_nzres_tab.getD j 0 + 7) (B0 + x86c_nzres) ++
          List.replicate (tC j) 0x90))) :
    ∃ mEnd, runN Mode.x86 14 (B0 + x86c_nzarg, m) = some (Dd - 1, mEnd) ∧
      mEnd Dd = (if k = 0 then 0 else 1) ∧
      ∀ x, ¬(x = B0 + x86c_shlarg4 + 2 ∨ (B0 + x86c_shlres4 + 3 ≤ x ∧ x < B0 + x86c_shlres4 + 9) ∨
        (B0 + x86c_shlres4 + 10 ≤ x ∧ x < B0 + x86c_shlres4 + 14) ∨
        (B0 + x86c_nzarg + 33 ≤ x ∧ x < B0 + x86c_nzarg + 35) ∨ x = B0 + x86c_nzres + 6 ∨ x = Dd) →
        mEnd x = m x := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := x86c_geometry
  have g10 : x86c_shlres4 + 14 ≤ x86c_nzarg := by decide
  exact fig5_corrected Mode.x86 m (B0 + x86c_nzarg) (B0 + x86c_shlarg4) (B0 + x86c_shlres4)
    (B0 + x86c_nzres) Dd k d0 w0 r0 (fun i => if i = 0 then 0 else 1) (fun i _ => by split <;> omega) hk (by omega) (by omega) (by omega) hDd hbig img
    (fun j hj => by
      have := hEnt j hj
      rw [x86c_nzres_offsets j hj] at this
      rw [show B0 + (x86c_nzarg + 37 + 16 * j) = B0 + x86c_nzarg + 37 + 16 * j by omega] at this
      exact this)

/-- C16 (Fig. 5), x64 build of the corrected `writeexc.asm` (erratum L04): from `not` execution reaches the
return jump target `Dd - 1` after exactly `14` steps for every argument byte `k` (no NOP slide), having stored
`255 - k` at `Dd`; every write is to an instruction field. -/
theorem fig5c_x64 (B0 : Nat) (m : Mem) (Dd k d0 w0 r0 : Nat) (hk : k < 256)
    (hDd : B0 + x64c_notres + 12 ≤ Dd) (hbig : Dd + 1 < 2 ^ 30)
    (img : NotImg Mode.x64 m (B0 + x64c_notarg) (B0 + x64c_shlarg4) (B0 + x64c_shlres4)
      (B0 + x64c_notres) Dd k d0 w0 r0)
    (hEnt : ∀ j, j < 256 → Code m (B0 + x64c_notres_tab.getD j 0)
      (enc (.movB (fld Mode.x64 (B0 + x64c_notres_tab.getD j 0) 7 (B0 + x64c_notres + 6)) ((fun i => 255 - i) j)) ++
        (jmpTo (nrT j) (B0 + x64c_notres_tab.getD j 0 + 7) (B0 + x64c_notres) ++
          List.replicate (tC j) 0x90))) :
    ∃ mEnd, runN Mode.x64 14 (B0 + x64c_notarg, m) = some (Dd - 1, mEnd) ∧
      mEnd Dd = 255 - k ∧
      ∀ x, ¬(x = B0 + x64c_shlarg4 + 2 ∨ (B0 + x64c_shlres4 + 3 ≤ x ∧ x < B0 + x64c_shlres4 + 9) ∨
        (B0 + x64c_shlres4 + 10 ≤ x ∧ x < B0 + x64c_shlres4 + 14) ∨
        (B0 + x64c_notarg + 33 ≤ x ∧ x < B0 + x64c_notarg + 35) ∨ x = B0 + x64c_notres + 6 ∨ x = Dd) →
        mEnd x = m x := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := x64c_geometry
  have g10 : x64c_shlres4 + 14 ≤ x64c_notarg := by decide
  exact fig5_corrected Mode.x64 m (B0 + x64c_notarg) (B0 + x64c_shlarg4) (B0 + x64c_shlres4)
    (B0 + x64c_notres) Dd k d0 w0 r0 (fun i => 255 - i) (fun i _ => by omega) hk (by omega) (by omega) (by omega) hDd hbig img
    (fun j hj => by
      have := hEnt j hj
      rw [x64c_notres_offsets j hj] at this
      rw [show B0 + (x64c_notarg + 37 + 16 * j) = B0 + x64c_notarg + 37 + 16 * j by omega] at this
      exact this)

/-- C16 (NZ) (Fig. 5), x64 build of the corrected `writeexc.asm` (erratum L04): from `nz` execution reaches the
return jump target `Dd - 1` after exactly `14` steps for every argument byte `k` (no NOP slide), having stored
`(k ≠ 0)` at `Dd`; every write is to an instruction field. -/
theorem fig5c_nz_x64 (B0 : Nat) (m : Mem) (Dd k d0 w0 r0 : Nat) (hk : k < 256)
    (hDd : B0 + x64c_nzres + 12 ≤ Dd) (hbig : Dd + 1 < 2 ^ 30)
    (img : NotImg Mode.x64 m (B0 + x64c_nzarg) (B0 + x64c_shlarg4) (B0 + x64c_shlres4)
      (B0 + x64c_nzres) Dd k d0 w0 r0)
    (hEnt : ∀ j, j < 256 → Code m (B0 + x64c_nzres_tab.getD j 0)
      (enc (.movB (fld Mode.x64 (B0 + x64c_nzres_tab.getD j 0) 7 (B0 + x64c_nzres + 6)) ((fun i => if i = 0 then 0 else 1) j)) ++
        (jmpTo (nrT j) (B0 + x64c_nzres_tab.getD j 0 + 7) (B0 + x64c_nzres) ++
          List.replicate (tC j) 0x90))) :
    ∃ mEnd, runN Mode.x64 14 (B0 + x64c_nzarg, m) = some (Dd - 1, mEnd) ∧
      mEnd Dd = (if k = 0 then 0 else 1) ∧
      ∀ x, ¬(x = B0 + x64c_shlarg4 + 2 ∨ (B0 + x64c_shlres4 + 3 ≤ x ∧ x < B0 + x64c_shlres4 + 9) ∨
        (B0 + x64c_shlres4 + 10 ≤ x ∧ x < B0 + x64c_shlres4 + 14) ∨
        (B0 + x64c_nzarg + 33 ≤ x ∧ x < B0 + x64c_nzarg + 35) ∨ x = B0 + x64c_nzres + 6 ∨ x = Dd) →
        mEnd x = m x := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := x64c_geometry
  have g10 : x64c_shlres4 + 14 ≤ x64c_nzarg := by decide
  exact fig5_corrected Mode.x64 m (B0 + x64c_nzarg) (B0 + x64c_shlarg4) (B0 + x64c_shlres4)
    (B0 + x64c_nzres) Dd k d0 w0 r0 (fun i => if i = 0 then 0 else 1) (fun i _ => by split <;> omega) hk (by omega) (by omega) (by omega) hDd hbig img
    (fun j hj => by
      have := hEnt j hj
      rw [x64c_nzres_offsets j hj] at this
      rw [show B0 + (x64c_nzarg + 37 + 16 * j) = B0 + x64c_nzarg + 37 + 16 * j by omega] at this
      exact this)

end WriteExecute.X86
