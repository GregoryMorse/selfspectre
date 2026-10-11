module
public import WriteExecute.Spec.Universal

public section

namespace WriteExecute.Universal

open WriteExecute.TM

theorem handlerSize_pos (Q : Nat) : 0 < handlerSize Q := by unfold handlerSize; omega

theorem cellWord_entry_op {A Q : Nat} (M : Machine A Q) (sym q : Nat) (hq : q < Q) :
    cellWord M sym (2 * q) = 2 := by
  unfold cellWord
  have h1 : 2 * q < 2 * Q := by omega
  have h2 : 2 * q % 2 = 0 := by omega
  simp [h1, h2]

theorem cellWord_entry_disp {A Q : Nat} (M : Machine A Q) (sym q : Nat) (hq : q < Q) :
    cellWord M sym (2 * q + 1) = entryDisp A Q q sym := by
  unfold cellWord
  have h1 : 2 * q + 1 < 2 * Q := by omega
  have h2 : (2 * q + 1) % 2 = 1 := by omega
  have h3 : (2 * q + 1) / 2 = q := by omega
  simp [h1, h2, h3]

/-- Decoding the address of a handler word. -/
theorem decode_handler (A Q q sym off : Nat) (hq : q < Q) (hs : sym < A) (ho : off < handlerSize Q) :
    (q * A + sym) * handlerSize Q + off < Q * A * handlerSize Q ∧
    ((q * A + sym) * handlerSize Q + off) / handlerSize Q / A = q ∧
    ((q * A + sym) * handlerSize Q + off) / handlerSize Q % A = sym ∧
    ((q * A + sym) * handlerSize Q + off) % handlerSize Q = off := by
  have hK := handlerSize_pos Q
  have hidx : q * A + sym < Q * A := by
    have : (q + 1) * A ≤ Q * A := Nat.mul_le_mul_right A hq
    rw [Nat.add_mul] at this; omega
  have hdiv : ((q * A + sym) * handlerSize Q + off) / handlerSize Q = q * A + sym := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt ho]; omega
  have hmod : ((q * A + sym) * handlerSize Q + off) % handlerSize Q = off := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ho]
  have hA : 0 < A := by omega
  refine ⟨?_, ?_, ?_, hmod⟩
  · have : (q * A + sym + 1) * handlerSize Q ≤ Q * A * handlerSize Q :=
      Nat.mul_le_mul_right _ hidx
    rw [Nat.add_mul] at this; omega
  · rw [hdiv, Nat.add_comm, Nat.add_mul_div_right _ _ hA, Nat.div_eq_of_lt hs]; omega
  · rw [hdiv, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]

theorem cellWord_handler {A Q : Nat} (M : Machine A Q) (s q sym off : Nat)
    (hq : q < Q) (hs : sym < A) (ho : off < handlerSize Q) :
    cellWord M s (handlerAt A Q q sym + off) = handlerWord M q sym off := by
  obtain ⟨h1, h2, h3, h4⟩ := decode_handler A Q q sym off hq hs ho
  have e : handlerAt A Q q sym + off - 2 * Q = (q * A + sym) * handlerSize Q + off := by
    unfold handlerAt; omega
  have n : ¬ (handlerAt A Q q sym + off < 2 * Q) := by unfold handlerAt; omega
  unfold cellWord
  rw [if_neg n, e, if_pos h1, h2, h3, h4]

theorem handler_end_le {A Q : Nat} (q sym off : Nat) (hq : q < Q) (hs : sym < A)
    (ho : off < handlerSize Q) : handlerAt A Q q sym + off < cellSize A Q := by
  obtain ⟨h1, -, -, -⟩ := decode_handler A Q q sym off hq hs ho
  unfold handlerAt cellSize; omega

/-- Only the entry displacements depend on the cell's symbol. -/
theorem cellWord_indep {A Q : Nat} (M : Machine A Q) (s t j : Nat)
    (h : ¬ (j < 2 * Q ∧ j % 2 = 1)) : cellWord M s j = cellWord M t j := by
  unfold cellWord
  by_cases h1 : j < 2 * Q
  · have : j % 2 = 0 := by omega
    simp [h1, this]
  · simp [h1]

/-- A tape's layout at an address inside cell `c`. -/
theorem layout_at {A Q : Nat} (M : Machine A Q) (tape : Int → Fin A) (c : Int) (j : Nat)
    (hj : j < cellSize A Q) :
    layout M tape (c * (cellSize A Q : Int) + (j : Int)) = cellWord M (tape c).val j := by
  have hS : (0 : Int) < (cellSize A Q : Int) := by omega
  have hj' : (j : Int) < (cellSize A Q : Int) := by omega
  have hd : (c * (cellSize A Q : Int) + (j : Int)) / (cellSize A Q : Int) = c := by
    rw [Int.add_comm, Int.add_mul_ediv_right _ _ (Int.ne_of_gt hS), Int.ediv_eq_zero_of_lt (by omega) hj']
    omega
  have hm : (c * (cellSize A Q : Int) + (j : Int)) % (cellSize A Q : Int) = (j : Int) := by
    rw [Int.add_comm, Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by omega) hj']
  unfold layout
  rw [hd, hm]
  simp

end WriteExecute.Universal
