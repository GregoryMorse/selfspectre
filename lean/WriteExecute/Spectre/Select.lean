module
public import WriteExecute.Spec.Spectre

public section

namespace WriteExecute.Spectre

theorem selX1_32 : ∀ r, r < 6 → selX1 32 r = if r = 0 then BitVec.allOnes 32 else 0 := by
  intro r hr
  have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem selX1_64 : ∀ r, r < 6 → selX1 64 r = if r = 0 then BitVec.allOnes 64 else 0 := by
  intro r hr
  have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem sel_ones {w : Nat} (t m : BitVec w) : t ^^^ (BitVec.allOnes w &&& (m ^^^ t)) = m := by
  ext i
  simp
  cases t[i] <;> cases m[i] <;> rfl

theorem sel_zero {w : Nat} (t m : BitVec w) : t ^^^ ((0 : BitVec w) &&& (m ^^^ t)) = t := by
  simp

/-- C19 (32-bit `size_t`): Fig. 1 yields `m` iff `j % 6 = 0`, otherwise `t`. -/
theorem select_32 (j : Nat) (t m : BitVec 32) : selectIdx 32 j t m = if j % 6 = 0 then m else t := by
  unfold selectIdx
  rw [selX1_32 (j % 6) (Nat.mod_lt _ (by omega))]
  by_cases h : j % 6 = 0
  · simp only [h, ite_true]; exact sel_ones t m
  · simp only [h, ite_false]; exact sel_zero t m

/-- C19 (64-bit `size_t`). -/
theorem select_64 (j : Nat) (t m : BitVec 64) : selectIdx 64 j t m = if j % 6 = 0 then m else t := by
  unfold selectIdx
  rw [selX1_64 (j % 6) (Nat.mod_lt _ (by omega))]
  by_cases h : j % 6 = 0
  · simp only [h, ite_true]; exact sel_ones t m
  · simp only [h, ite_false]; exact sel_zero t m

end WriteExecute.Spectre
