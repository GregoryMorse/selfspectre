module
public import WriteExecute.Spec.Arith

public section

namespace WriteExecute.Arith

/-- Every digit is a byte. -/
@[expose] def Bytes (l : List Nat) : Prop := ∀ d ∈ l, d < 256

theorem Bytes.nil : Bytes [] := by intro d hd; simp at hd

theorem Bytes.cons {a : Nat} {l : List Nat} (ha : a < 256) (hl : Bytes l) : Bytes (a :: l) := by
  intro d hd
  rcases List.mem_cons.mp hd with rfl | h
  · exact ha
  · exact hl d h

theorem Bytes.head {a : Nat} {l : List Nat} (h : Bytes (a :: l)) : a < 256 :=
  h a (List.mem_cons_self ..)

theorem Bytes.tail {a : Nat} {l : List Nat} (h : Bytes (a :: l)) : Bytes l :=
  fun d hd => h d (List.mem_cons_of_mem _ hd)

theorem ofBytes_lt : ∀ (l : List Nat), Bytes l → ofBytes l < 256 ^ l.length
  | [], _ => by simp [ofBytes]
  | a :: l, h => by
    have ih := ofBytes_lt l h.tail
    have ha := h.head
    have e : 256 ^ (l.length + 1) = 256 * 256 ^ l.length := by rw [Nat.pow_succ, Nat.mul_comm]
    simp only [ofBytes, List.length_cons, e]
    have : 256 * ofBytes l + 256 ≤ 256 * 256 ^ l.length := by omega
    omega

theorem toBytes_length (n x : Nat) : (toBytes n x).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [toBytes, ih]

theorem toBytes_bytes (n x : Nat) : Bytes (toBytes n x) := by
  induction n generalizing x with
  | zero => exact Bytes.nil
  | succ n ih => exact Bytes.cons (Nat.mod_lt _ (by omega)) (ih _)

theorem ofBytes_toBytes (n x : Nat) : ofBytes (toBytes n x) = x % 256 ^ n := by
  induction n generalizing x with
  | zero => simp [toBytes, ofBytes, Nat.mod_one]
  | succ n ih =>
    have e : 256 ^ (n + 1) = 256 * 256 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
    simp only [toBytes, ofBytes, ih, e]
    exact Nat.mod_mul.symm

/-- Digits of a number that fits determine it. -/
theorem ofBytes_of_mod {n x : Nat} (h : x < 256 ^ n) : ofBytes (toBytes n x) = x := by
  rw [ofBytes_toBytes, Nat.mod_eq_of_lt h]

end WriteExecute.Arith
