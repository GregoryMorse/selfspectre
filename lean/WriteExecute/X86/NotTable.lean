module
public import WriteExecute.X86.Fig5

public section

namespace WriteExecute.X86

theorem Code_replicate_drop (m : Mem) (x : Nat) :
    ∀ (i t b : Nat), Code m b (List.replicate t x) → i ≤ t → Code m (b + i) (List.replicate (t - i) x)
  | 0, t, b, h, _ => by simpa using h
  | i + 1, 0, b, _, hi => by omega
  | i + 1, t + 1, b, h, hi => by
    have := Code_replicate_drop m x i t (b + 1) h.2 (by omega)
    rw [show b + (i + 1) = b + 1 + i by omega, show t + 1 - (i + 1) = t - i by omega]
    exact this

theorem jmpTo_length (near : Bool) (A N : Nat) : (jmpTo near A N).length = if near then 5 else 2 := by
  cases near <;> simp [jmpTo, enc_len, Ins.len]

/-- The last `s ≤ t0` NOPs of a table entry, in the memory bytes. -/
theorem entry_tail (m : Mem) (E0 N v t0 s : Nat) (near : Bool) (mode : Mode) (hs : s ≤ t0)
    (h : Code m E0 (enc (.movB (fld mode E0 7 (N + 6)) v) ++
      (jmpTo near (E0 + 7) N ++ List.replicate t0 0x90))) :
    Code m (E0 + 7 + (if near then 5 else 2) + (t0 - s)) (List.replicate s 0x90) := by
  obtain ⟨-, h2⟩ := (Code_append m _ _ _).1 h
  rw [enc_len] at h2
  simp only [Ins.len] at h2
  obtain ⟨-, h3⟩ := (Code_append m _ _ _).1 h2
  rw [jmpTo_length] at h3
  have := Code_replicate_drop m 0x90 (t0 - s) t0 _ h3 (by omega)
  rw [show t0 - (t0 - s) = s by omega] at this
  rw [show E0 + 7 + (if near then 5 else 2) + (t0 - s) = E0 + 7 + (if near then 5 else 2) + (t0 - s) from rfl]
  exact this

/-- The part of the image of `WriteExecNOT`/`WriteExecSHL4` and the wrapper patches that does not
depend on the NOT table layout (addresses are absolute: `x86` base added to section offsets, or
any base for `x64`). `a0 = notarg`, `X = shlarg4`, `R = shlres4`, `N = notres`, `Dd` = result byte. -/
structure NotImg (mode : Mode) (m : Mem) (a0 X R N Dd k d0 w0 r0 : Nat) : Prop where
  i0 : Code m a0 (enc (.movB (fld mode a0 7 (X + 2)) k))
  i1 : Code m (a0 + 7) (enc (.movD (fld mode (a0 + 7) 10 (R + 3)) (fld mode R 9 (a0 + 32 + 1))))
  i2 : Code m (a0 + 17) (enc (.movD (fld mode (a0 + 17) 10 (R + 9 + 1)) (jrel (R + 9) (a0 + 32))))
  i3 : Code m (a0 + 27) (enc (.jmp32 (jrel (a0 + 27) X)))
  iX : Code m X (enc (.jmp32 (256 * 128)))
  iT : ∀ j, j < 256 → Code m (X + 5 + 256 * j)
      (enc (.movW (fld mode (X + 5 + 256 * j) 9 (R + 7)) (j * 2 ^ 4)) ++
        enc (.jmp32 (jrel (X + 5 + 256 * j + 9) R)))
  iR : Code m R (enc (.movW d0 w0))
  iS : Code m (R + 9) (enc (.jmp32 r0))
  iG : Code m (a0 + 32) (enc (.jmp32 32768))
  iN : Code m N (enc (.movB (fld mode N 7 Dd) 0))
  iRet : Code m (N + 7) (enc (.jmp32 (jrel (N + 7) (Dd - 1))))

/-- Entry offsets of the NOT table as assembled with the published threshold `0f6h`: entry 247 has
seven NOPs but a near jump, so it is 19 bytes and later entries are shifted by 3. -/
@[expose] def Eo (B j : Nat) : Nat := B + 16 * j + (if 248 ≤ j then 3 else 0)
@[expose] def nrT (j : Nat) : Bool := decide (j < 248)
@[expose] def tO (j : Nat) : Nat := if 246 < j then 7 else 4
@[expose] def tC (j : Nat) : Nat := if 247 < j then 7 else 4

theorem fig5_original (mode : Mode) (m : Mem) (a0 X R N Dd k d0 w0 r0 : Nat)
    (F : Nat → Nat) (hF : ∀ j, j < 256 → F j < 256) (hk : k < 256) (hR : R = X + 5 + 65536) (hord : R + 14 ≤ a0) (hN : N = a0 + 37 + 4099)
    (hDd : N + 12 ≤ Dd) (hbig : Dd + 1 < 2 ^ 30)
    (img : NotImg mode m a0 X R N Dd k d0 w0 r0)
    (hEnt : ∀ j, j < 256 → Code m (Eo (a0 + 37) j)
      (enc (.movB (fld mode (Eo (a0 + 37) j) 7 (N + 6)) (F j)) ++
        (jmpTo (nrT j) (Eo (a0 + 37) j + 7) N ++ List.replicate (tO j) 0x90))) :
    ∃ mEnd, runN mode ((if 248 ≤ k then 3 else 0) + 14) (a0, m) = some (Dd - 1, mEnd) ∧
      mEnd Dd = F k ∧
      ∀ x, ¬(x = X + 2 ∨ (R + 3 ≤ x ∧ x < R + 9) ∨ (R + 10 ≤ x ∧ x < R + 14) ∨
        (a0 + 33 ≤ x ∧ x < a0 + 35) ∨ x = N + 6 ∨ x = Dd) → mEnd x = m x := by
  have hslack : ∀ j, j < 256 → Code m (a0 + 32 + 5 + j * 2 ^ 4)
      (List.replicate (Eo (a0 + 37) j - (a0 + 32 + 5 + j * 2 ^ 4)) 0x90) := by
    intro j hj
    by_cases h248 : 248 ≤ j
    · have e : Eo (a0 + 37) j - (a0 + 32 + 5 + j * 2 ^ 4) = 3 := by
        unfold Eo; simp only [h248, ite_true]; omega
      rw [e]
      have := entry_tail m (Eo (a0 + 37) (j - 1)) N (F (j - 1)) (tO (j - 1)) 3 (nrT (j - 1)) mode
        (by unfold tO; split <;> omega) (hEnt (j - 1) (by omega))
      have ep : Eo (a0 + 37) (j - 1) + 7 + (if nrT (j - 1) = true then 5 else 2) + (tO (j - 1) - 3) =
          a0 + 32 + 5 + j * 2 ^ 4 := by
        unfold Eo nrT tO
        by_cases h : j = 248
        · subst h; simp <;> omega
        · have h1 : ¬ (j - 1 < 248) := by omega
          have h2 : 248 ≤ j - 1 := by omega
          have h3 : 246 < j - 1 := by omega
          simp [h1, h2, h3] <;> omega
      rw [ep] at this
      exact this
    · have e : Eo (a0 + 37) j - (a0 + 32 + 5 + j * 2 ^ 4) = 0 := by
        unfold Eo; simp only [h248, ite_false]; omega
      rw [e]; trivial
  have := not_exec mode m a0 X R N Dd k d0 w0 r0 (Eo (a0 + 37)) nrT tO F hF hk hR hord
    (fun j hj => by unfold Eo; split <;> omega) hDd hbig (by omega)
    img.i0 img.i1 img.i2 img.i3 img.iX img.iT img.iR img.iS img.iG hslack hEnt
    (fun j hj hn => by
      have : ¬ j < 248 := by simpa [nrT] using hn
      unfold Eo; simp only [show 248 ≤ j by omega, ite_true]; omega)
    img.iN img.iRet
  have e : Eo (a0 + 37) k - (a0 + 32 + 5 + k * 2 ^ 4) = if 248 ≤ k then 3 else 0 := by
    unfold Eo; split <;> omega
  rw [e] at this
  exact this

theorem fig5_corrected (mode : Mode) (m : Mem) (a0 X R N Dd k d0 w0 r0 : Nat)
    (F : Nat → Nat) (hF : ∀ j, j < 256 → F j < 256) (hk : k < 256) (hR : R = X + 5 + 65536) (hord : R + 14 ≤ a0) (hN : N = a0 + 37 + 4096)
    (hDd : N + 12 ≤ Dd) (hbig : Dd + 1 < 2 ^ 30)
    (img : NotImg mode m a0 X R N Dd k d0 w0 r0)
    (hEnt : ∀ j, j < 256 → Code m (a0 + 37 + 16 * j)
      (enc (.movB (fld mode (a0 + 37 + 16 * j) 7 (N + 6)) (F j)) ++
        (jmpTo (nrT j) (a0 + 37 + 16 * j + 7) N ++ List.replicate (tC j) 0x90))) :
    ∃ mEnd, runN mode 14 (a0, m) = some (Dd - 1, mEnd) ∧ mEnd Dd = F k ∧
      ∀ x, ¬(x = X + 2 ∨ (R + 3 ≤ x ∧ x < R + 9) ∨ (R + 10 ≤ x ∧ x < R + 14) ∨
        (a0 + 33 ≤ x ∧ x < a0 + 35) ∨ x = N + 6 ∨ x = Dd) → mEnd x = m x := by
  have := not_exec mode m a0 X R N Dd k d0 w0 r0 (fun j => a0 + 37 + 16 * j) nrT tC F hF hk hR hord
    (fun j hj => by omega) hDd hbig (by omega)
    img.i0 img.i1 img.i2 img.i3 img.iX img.iT img.iR img.iS img.iG
    (fun j hj => by
      have e : a0 + 37 + 16 * j - (a0 + 32 + 5 + j * 2 ^ 4) = 0 := by omega
      rw [e]; trivial)
    hEnt
    (fun j hj hn => by
      have : ¬ j < 248 := by simpa [nrT] using hn
      omega)
    img.iN img.iRet
  have e : a0 + 37 + 16 * k - (a0 + 32 + 5 + k * 2 ^ 4) = 0 := by omega
  rw [e] at this
  exact this

/-! W10: entry sizes. `size thr N B j` is the assembled size of entry `j`: seven bytes of `mov`, a near
(5) or short (2) jump, and the NOP padding chosen by the macro threshold. -/

@[expose] def entrySize (nr : Nat → Bool) (t : Nat → Nat) (j : Nat) : Nat :=
  7 + (if nr j then 5 else 2) + t j

/-- Published threshold (`0f6h`): all entries take 16 bytes except entry 247, which takes 19. -/
theorem w10_original_sizes (j : Nat) (hj : j < 256) :
    entrySize nrT tO j = if j = 247 then 19 else 16 := by
  unfold entrySize nrT tO
  by_cases h1 : j < 248 <;> by_cases h2 : 246 < j <;> by_cases h3 : j = 247 <;>
    simp [h1, h2, h3] <;> omega

/-- Corrected threshold (`0f7h`): every entry takes exactly 16 bytes. -/
theorem w10_corrected_sizes (j : Nat) (hj : j < 256) : entrySize nrT tC j = 16 := by
  unfold entrySize nrT tC
  by_cases h1 : j < 248 <;> by_cases h2 : 247 < j <;> simp [h1, h2] <;> omega

/-- The jump forms are those the assembler chooses: short exactly when the table end is within reach. -/
theorem w10_original_forms (B j : Nat) (hj : j < 256) :
    (nrT j = false ↔ (B + 4099) - (Eo B j + 9) < 128) := by
  unfold nrT Eo
  by_cases h : j < 248 <;> by_cases h' : 248 ≤ j <;> simp [h, h'] <;> omega

theorem w10_corrected_forms (B j : Nat) (hj : j < 256) :
    (nrT j = false ↔ (B + 4096) - (B + 16 * j + 9) < 128) := by
  unfold nrT
  by_cases h : j < 248 <;> simp [h] <;> omega

/-- The original offsets are the running sums of the sizes, ending at `notres`. -/
theorem w10_original_offsets (B j : Nat) (hj : j < 256) :
    Eo B (j + 1) = Eo B j + entrySize nrT tO j := by
  unfold Eo entrySize nrT tO
  by_cases h1 : j < 248 <;> by_cases h2 : 246 < j <;> by_cases h3 : 248 ≤ j + 1 <;>
    by_cases h4 : 248 ≤ j <;> simp [h1, h2, h3, h4] <;> omega

theorem w10_original_end (B : Nat) : B + 4099 = Eo B 255 + entrySize nrT tO 255 := by
  simp [Eo, entrySize, nrT, tO]

theorem w10_corrected_offsets (B j : Nat) (hj : j < 256) :
    B + 16 * (j + 1) = B + 16 * j + entrySize nrT tC j := by
  have := w10_corrected_sizes j hj
  omega

end WriteExecute.X86
