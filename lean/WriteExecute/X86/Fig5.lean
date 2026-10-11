module
public import WriteExecute.X86.Lookup

public section

namespace WriteExecute.X86

theorem Code_frame' {m : Mem} {e n v a : Nat} {ins : Ins} (h : Code m a (enc ins))
    (hd : a + ins.len ≤ e ∨ e + n ≤ a) : Code (wr m e n v) a (enc ins) :=
  Code_frame m e n v _ a h (by rw [enc_len]; exact hd)

theorem Code_frame2 {m : Mem} {e n v a : Nat} {i1 i2 : Ins} (h : Code m a (enc i1 ++ enc i2))
    (hd : a + i1.len + i2.len ≤ e ∨ e + n ≤ a) : Code (wr m e n v) a (enc i1 ++ enc i2) :=
  Code_frame m e n v _ a h (by rw [List.length_append, enc_len, enc_len]; omega)

macro "fz" : tactic => `(tactic| (simp only [Ins.len]; omega))

theorem wr_apply_in (m : Mem) (e n v x : Nat) (h : e ≤ x ∧ x < e + n) :
    wr m e n v x = v / 256 ^ (x - e) % 256 := by simp [wr, h]

theorem wr_apply_out (m : Mem) (e n v x : Nat) (h : ¬(e ≤ x ∧ x < e + n)) :
    wr m e n v x = m x := by simp [wr, h]

/-- The `not` lookup of Fig. 5, from `notarg` to the return jump: the argument byte `k` is patched into
the SHL4 table jump, SHL4 stores `16 k` into the `notargshl` jump, which selects entry `k` of the NOT
table (reached through a NOP slide of `E k - P` bytes), which stores `255 - k` into the operand of
`notres`; `notres` writes it to `Dd`. -/
theorem not_exec (mode : Mode) (m : Mem) (a0 X R N Dd k d0 w0 r0 : Nat)
    (E : Nat → Nat) (nr : Nat → Bool) (t : Nat → Nat) (F : Nat → Nat) (hF : ∀ j, j < 256 → F j < 256)
    (hk : k < 256) (hR : R = X + 5 + 65536) (hord : R + 14 ≤ a0)
    (hEge : ∀ j, j < 256 → a0 + 32 + 5 + j * 2 ^ 4 ≤ E j ∧ E j + 14 ≤ N + 6)
    (hDd : N + 12 ≤ Dd) (hbig : Dd + 1 < 2 ^ 30) (hX : X + 2 ≤ R)
    (i0 : Code m a0 (enc (.movB (fld mode a0 7 (X + 2)) k)))
    (i1 : Code m (a0 + 7) (enc (.movD (fld mode (a0 + 7) 10 (R + 3)) (fld mode R 9 (a0 + 32 + 1)))))
    (i2 : Code m (a0 + 17) (enc (.movD (fld mode (a0 + 17) 10 (R + 9 + 1)) (jrel (R + 9) (a0 + 32)))))
    (i3 : Code m (a0 + 27) (enc (.jmp32 (jrel (a0 + 27) X))))
    (iX : Code m X (enc (.jmp32 (256 * 128))))
    (iT : ∀ j, j < 256 → Code m (X + 5 + 256 * j)
      (enc (.movW (fld mode (X + 5 + 256 * j) 9 (R + 7)) (j * 2 ^ 4)) ++
        enc (.jmp32 (jrel (X + 5 + 256 * j + 9) R))))
    (iR : Code m R (enc (.movW d0 w0)))
    (iS : Code m (R + 9) (enc (.jmp32 r0)))
    (iG : Code m (a0 + 32) (enc (.jmp32 32768)))
    (hslack : ∀ j, j < 256 →
      Code m (a0 + 32 + 5 + j * 2 ^ 4) (List.replicate (E j - (a0 + 32 + 5 + j * 2 ^ 4)) 0x90))
    (hEnt : ∀ j, j < 256 → Code m (E j)
      (enc (.movB (fld mode (E j) 7 (N + 6)) (F j)) ++
        (jmpTo (nr j) (E j + 7) N ++ List.replicate (t j) 0x90)))
    (hshort : ∀ j, j < 256 → nr j = false → E j + 9 ≤ N ∧ N - (E j + 9) < 128)
    (iN : Code m N (enc (.movB (fld mode N 7 Dd) 0)))
    (iRet : Code m (N + 7) (enc (.jmp32 (jrel (N + 7) (Dd - 1))))) :
    ∃ mEnd, runN mode (E k - (a0 + 32 + 5 + k * 2 ^ 4) + 14) (a0, m) = some (Dd - 1, mEnd) ∧
      mEnd Dd = F k ∧
      ∀ x, ¬(x = X + 2 ∨ (R + 3 ≤ x ∧ x < R + 9) ∨ (R + 10 ≤ x ∧ x < R + 14) ∨
        (a0 + 33 ≤ x ∧ x < a0 + 35) ∨ x = N + 6 ∨ x = Dd) → mEnd x = m x := by
  have Ek := hEge k hk
  have hFk := hF k hk
  have hv16 : k * 2 ^ 4 < 65536 := by omega
  let m1 := wr m (X + 2) 1 k
  have hm1 : m1 = wr m (X + 2) 1 k := rfl
  let m2 := wr m1 (R + 3) 4 (fld mode R 9 (a0 + 32 + 1))
  have hm2 : m2 = wr m1 (R + 3) 4 (fld mode R 9 (a0 + 32 + 1)) := rfl
  let m3 := wr m2 (R + 9 + 1) 4 (jrel (R + 9) (a0 + 32))
  have hm3 : m3 = wr m2 (R + 9 + 1) 4 (jrel (R + 9) (a0 + 32)) := rfl
  -- Stage A: the three patches and the jump into SHL4
  have a1 : step mode (a0, m) = some (a0 + 7, m1) :=
    step_movB mode m a0 (X + 2) k (by omega) (by omega) hk i0
  have c1 : Code m1 (a0 + 7) (enc (.movD (fld mode (a0 + 7) 10 (R + 3)) (fld mode R 9 (a0 + 32 + 1)))) :=
    Code_frame' i1 (by fz)
  have a2 : step mode (a0 + 7, m1) = some (a0 + 17, m2) :=
    step_movD mode m1 (a0 + 7) (R + 3) _ (by omega) (by omega)
      (fld_lt mode R 9 _ (by omega)) c1
  have c2 : Code m2 (a0 + 17) (enc (.movD (fld mode (a0 + 17) 10 (R + 9 + 1)) (jrel (R + 9) (a0 + 32)))) :=
    Code_frame' (Code_frame' i2 (by fz)) (by fz)
  have a3 : step mode (a0 + 17, m2) = some (a0 + 27, m3) :=
    step_movD mode m2 (a0 + 17) (R + 9 + 1) _ (by omega) (by omega) (jrel_lt _ _) c2
  have c3 : Code m3 (a0 + 27) (enc (.jmp32 (jrel (a0 + 27) X))) :=
    Code_frame' (Code_frame' (Code_frame' i3 (by fz)) (by fz)) (by fz)
  have a4 : step mode (a0 + 27, m3) = some (X, m3) :=
    step_jmp32_to mode m3 (a0 + 27) X (by omega) (by omega) c3
  have A4 : runN mode 4 (a0, m) = some (X, m3) := by
    simp only [runN, a1, a2, a3, a4, Option.bind_some]
  -- Stage B: SHL4 lookup
  have hA : Code m3 X (enc (.jmp32 (256 * k))) :=
    Code_frame' (Code_frame' (patch_jmp32_byte m X 128 k (by omega) hk iX) (by fz)) (by fz)
  have hT : ∀ j, j < 256 → Code m3 (X + 5 + 256 * j)
      (enc (.movW (fld mode (X + 5 + 256 * j) 9 (R + 7)) (j * 2 ^ 4)) ++
        enc (.jmp32 (jrel (X + 5 + 256 * j + 9) R))) := fun j hj =>
    Code_frame2 (Code_frame2 (Code_frame2 (iT j hj) (by fz)) (by fz)) (by fz)
  have hR' : Code m3 R (enc (.movW (fld mode R 9 (a0 + 32 + 1)) w0)) :=
    Code_frame' (patch_movW_disp m1 R d0 _ w0 (Code_frame' iR (by fz))) (by fz)
  have hS' : Code m3 (R + 9) (enc (.jmp32 (jrel (R + 9) (a0 + 32)))) :=
    patch_jmp32 m2 (R + 9) r0 _ (Code_frame' (Code_frame' iS (by fz)) (by fz))
  have B5 := shl_lookup mode m3 X R k 4 (a0 + 32 + 1) w0 (a0 + 32) hR hk (by omega) (by omega)
    (by omega) (by omega) (by omega) hA hT hR' hS'
  let m4 := wr m3 (R + 7) 2 (k * 2 ^ 4)
  have hm4 : m4 = wr m3 (R + 7) 2 (k * 2 ^ 4) := rfl
  let m5 := wr m4 (a0 + 32 + 1) 2 (k * 2 ^ 4)
  have hm5 : m5 = wr m4 (a0 + 32 + 1) 2 (k * 2 ^ 4) := rfl
  -- Stage C: the patched jump selects table entry k
  have cG : Code m5 (a0 + 32) (enc (.jmp32 (k * 2 ^ 4))) :=
    patch_jmp32_word m4 (a0 + 32) 32768 (k * 2 ^ 4) (by omega) hv16
      (Code_frame' (Code_frame' (Code_frame' (Code_frame' iG (by fz)) (by fz)) (by fz)) (by fz))
  have c5 : step mode (a0 + 32, m5) = some (a0 + 32 + 5 + k * 2 ^ 4, m5) := by
    have := step_jmp32 mode m5 (a0 + 32) (k * 2 ^ 4) (by omega) cG
    simpa using this
  -- Stage D: NOT table entry with slide
  have hsl : Code m5 (a0 + 32 + 5 + k * 2 ^ 4) (List.replicate (E k - (a0 + 32 + 5 + k * 2 ^ 4)) 0x90) := by
    have h0 := hslack k hk
    have f1 := Code_frame m1 (R + 3) 4 (fld mode R 9 (a0 + 32 + 1)) _ _
      (Code_frame m (X + 2) 1 k _ _ h0 (Or.inr (by omega))) (Or.inr (by omega))
    have f2 := Code_frame _ (R + 9 + 1) 4 (jrel (R + 9) (a0 + 32)) _ _ f1 (Or.inr (by omega))
    have f3 := Code_frame _ (R + 7) 2 (k * 2 ^ 4) _ _ f2 (Or.inr (by omega))
    exact Code_frame _ (a0 + 32 + 1) 2 (k * 2 ^ 4) _ _ f3 (Or.inr (by omega))
  have hen : Code m5 (E k) (enc (.movB (fld mode (E k) 7 (N + 6)) (F k)) ++
      (jmpTo (nr k) (E k + 7) N ++ List.replicate (t k) 0x90)) := by
    have h0 := hEnt k hk
    have f1 := Code_frame m1 (R + 3) 4 (fld mode R 9 (a0 + 32 + 1)) _ _
      (Code_frame m (X + 2) 1 k _ _ h0 (Or.inr (by omega))) (Or.inr (by omega))
    have f2 := Code_frame _ (R + 9 + 1) 4 (jrel (R + 9) (a0 + 32)) _ _ f1 (Or.inr (by omega))
    have f3 := Code_frame _ (R + 7) 2 (k * 2 ^ 4) _ _ f2 (Or.inr (by omega))
    exact Code_frame _ (a0 + 32 + 1) 2 (k * 2 ^ 4) _ _ f3 (Or.inr (by omega))
  have D := table16_lookup mode m5 (a0 + 32 + 5 + k * 2 ^ 4) (E k) N (F k) (t k) (nr k)
    Ek.1 (by omega) (by omega) (by omega) Ek.2 (hshort k hk) hsl hen
  let m6 := wr m5 (N + 6) 1 (F k)
  have hm6 : m6 = wr m5 (N + 6) 1 (F k) := rfl
  -- Stage E: notres stores the result, notret returns
  have cN : Code m6 N (enc (.movB (fld mode N 7 Dd) (F k))) :=
    patch_movB_imm m5 N _ 0 (F k) (by omega) (by omega)
      (Code_frame' (Code_frame' (Code_frame' (Code_frame' (Code_frame' iN (by fz)) (by fz)) (by fz))
        (by fz)) (by fz))
  let m7 := wr m6 Dd 1 (F k)
  have hm7 : m7 = wr m6 Dd 1 (F k) := rfl
  have e1 : step mode (N, m6) = some (N + 7, m7) :=
    step_movB mode m6 N Dd (F k) (by omega) (by omega) (by omega) cN
  have cRet : Code m7 (N + 7) (enc (.jmp32 (jrel (N + 7) (Dd - 1)))) :=
    Code_frame' (Code_frame' (Code_frame' (Code_frame' (Code_frame' (Code_frame' (Code_frame'
      iRet (by fz)) (by fz)) (by fz)) (by fz)) (by fz)) (by fz)) (by fz)
  have e2 : step mode (N + 7, m7) = some (Dd - 1, m7) :=
    step_jmp32_to mode m7 (N + 7) (Dd - 1) (by omega) (by omega) cRet
  have E2 : runN mode 2 (N, m6) = some (Dd - 1, m7) := by
    simp only [runN, e1, e2, Option.bind_some]
  refine ⟨m7, ?_, ?_, ?_⟩
  · have hs : E k - (a0 + 32 + 5 + k * 2 ^ 4) + 14 =
        4 + 5 + 1 + (E k - (a0 + 32 + 5 + k * 2 ^ 4) + 2) + 2 := by omega
    rw [hs]
    exact runN_trans mode (runN_trans mode (runN_trans mode (runN_trans mode A4 B5)
      (runN_one mode _ _ c5)) D) E2
  · rw [hm7, wr_apply_in _ _ _ _ _ (by omega)]
    simp only [Nat.sub_self, Nat.pow_zero, Nat.div_one]
    exact Nat.mod_eq_of_lt (by omega)
  · intro x hx
    rw [hm7, wr_apply_out _ _ _ _ _ (by omega), hm6, wr_apply_out _ _ _ _ _ (by omega),
      hm5, wr_apply_out _ _ _ _ _ (by omega), hm4, wr_apply_out _ _ _ _ _ (by omega),
      hm3, wr_apply_out _ _ _ _ _ (by omega), hm2, wr_apply_out _ _ _ _ _ (by omega),
      hm1, wr_apply_out _ _ _ _ _ (by omega)]

end WriteExecute.X86
