module
public import WriteExecute.Spec.Spectre
public import WriteExecute.Arith.Tables

public section

namespace WriteExecute.Spectre

open WriteExecute.Arith

/-- Inverse of `mixIdx` on `0 .. 255` (167 * 23 = 15 * 256 + 1). -/
@[expose] def mixInv (j : Nat) : Nat := ((j + 256 - 13) * 23) % 256

/-- C20: `mixIdx` permutes `0 .. 255`. -/
theorem mix_perm : ∀ i, i < 256 → mixIdx i < 256 ∧ mixInv (mixIdx i) = i ∧ mixIdx (mixInv i) = i :=
  all1 (p := fun i => mixIdx i < 256 ∧ mixInv (mixIdx i) = i ∧ mixIdx (mixInv i) = i)
    (by decide +kernel)

theorem mix_injective (a b : Nat) (ha : a < 256) (hb : b < 256) (h : mixIdx a = mixIdx b) : a = b := by
  have h1 := (mix_perm a ha).2.1
  have h2 := (mix_perm b hb).2.1
  rw [← h1, ← h2, h]

theorem mix_surjective (j : Nat) (hj : j < 256) : ∃ i, i < 256 ∧ mixIdx i = j :=
  ⟨mixInv j, by unfold mixInv; omega, (mix_perm j hj).2.2⟩

end WriteExecute.Spectre
