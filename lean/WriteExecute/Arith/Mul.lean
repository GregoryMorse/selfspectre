module
public import WriteExecute.Arith.Shift

public section

namespace WriteExecute.Arith

/-! C09: shift-and-add multiplication, built on the proved 64-bit ADD and SHL. -/

theorem cadd {P a a' b b' : Nat} (h1 : a % P = a' % P) (h2 : b % P = b' % P) :
    (a + b) % P = (a' + b') % P := by
  rw [Nat.add_mod, h1, h2, ← Nat.add_mod]

theorem cmul {P a a' b b' : Nat} (h1 : a % P = a' % P) (h2 : b % P = b' % P) :
    (a * b) % P = (a' * b') % P := by
  rw [Nat.mul_mod, h1, h2, ← Nat.mul_mod]

theorem mulLoop_spec : ∀ (k tx y acc : Nat), acc < 256 ^ 8 →
    mulLoop k tx y acc = (acc + tx * (y % 2 ^ k)) % 256 ^ 8
  | 0, tx, y, acc, h => by
    simp only [mulLoop, Nat.pow_zero, Nat.mod_one, Nat.mul_zero, Nat.add_zero]
    exact (Nat.mod_eq_of_lt h).symm
  | k + 1, tx, y, acc, h => by
    have P0 : 0 < 256 ^ 8 := pow256_pos 8
    have hy : y % 2 ^ (k + 1) = y % 2 + 2 * (y / 2 % 2 ^ k) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mod_mul]
    have hsh : (shlN 8 tx 1) % 256 ^ 8 = (tx * 2) % 256 ^ 8 := by
      rw [shlN_spec, Nat.mod_mod]
    have hsh2 : ∀ Y, (shlN 8 tx 1 * Y) % 256 ^ 8 = (tx * (2 * Y)) % 256 ^ 8 := by
      intro Y
      rw [← Nat.mul_assoc]
      exact cmul hsh rfl
    by_cases h1 : y % 2 = 1
    · have hacc : addN 8 acc tx = (acc + tx) % 256 ^ 8 := addN_spec 8 acc tx
      have hlt : (acc + tx) % 256 ^ 8 < 256 ^ 8 := Nat.mod_lt _ P0
      have ih := mulLoop_spec k (shlN 8 tx 1) (y / 2) (addN 8 acc tx) (by rw [hacc]; exact hlt)
      simp only [mulLoop, h1, ite_true]
      rw [ih, hy, h1]
      generalize y / 2 % 2 ^ k = Y
      have key : acc + tx * (1 + 2 * Y) = (acc + tx) + tx * (2 * Y) := by
        rw [Nat.mul_add, Nat.mul_one]; omega
      rw [key]
      exact cadd (by rw [hacc, Nat.mod_mod]) (hsh2 Y)
    · have h0 : y % 2 = 0 := by omega
      have ih := mulLoop_spec k (shlN 8 tx 1) (y / 2) acc h
      simp only [mulLoop, h1, ite_false]
      rw [ih, hy, h0]
      generalize y / 2 % 2 ^ k = Y
      rw [Nat.zero_add]
      exact cadd rfl (hsh2 Y)

/-- C09: 32 x 32 -> 64-bit product. -/
theorem mul32_spec (x y : Nat) (hy : y < 2 ^ 32) : mul32 x y = (x * y) % 2 ^ 64 := by
  unfold mul32
  rw [mulLoop_spec 32 x y 0 (pow256_pos 8), Nat.mod_eq_of_lt hy, Nat.zero_add]

theorem mul32_exact (x y : Nat) (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) : mul32 x y = x * y := by
  rw [mul32_spec x y hy]
  apply Nat.mod_eq_of_lt
  calc x * y < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' hx hy
    _ = 2 ^ 64 := by rw [← Nat.pow_add]

end WriteExecute.Arith
