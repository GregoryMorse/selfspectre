module
public import WriteExecute.Arith.Mul

public section

namespace WriteExecute.Arith

/-! C11: the division-overflow facts and the two-step reduction behind erratum W04 and fix L03. -/

theorem mod_lt_word (n d : Nat) (hd0 : 0 < d) (hd : d ≤ 2 ^ 32) : n % d < 2 ^ 32 :=
  Nat.lt_of_lt_of_le (Nat.mod_lt _ hd0) hd

/-- A 64-bit by 32-bit division has a 32-bit quotient exactly when the high word is below the divisor. -/
theorem div_lt_word_iff (n d : Nat) (hd0 : 0 < d) : n / d < 2 ^ 32 ↔ n / 2 ^ 32 < d := by
  rw [Nat.div_lt_iff_lt_mul hd0, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 32), Nat.mul_comm]

/-- The product of two residues divided by the modulus never overflows 32 bits. -/
theorem mulmod_div_lt (a b d : Nat) (ha : a < d) (hb : b < d) (hd : d ≤ 2 ^ 32) :
    a * b / d < 2 ^ 32 := by
  have hd0 : 0 < d := by omega
  have : a * b < d * d := Nat.mul_lt_mul'' ha hb
  have h2 : a * b / d < d := (Nat.div_lt_iff_lt_mul hd0).mpr this
  omega

/-- The high half may be reduced first without changing the value, and the reduced 64-bit value
divides without overflow. -/
theorem two_step (hi lo m : Nat) (hm : 0 < m) (hlo : lo < 2 ^ 32) :
    ((hi % m) * 2 ^ 32 + lo) % m = (hi * 2 ^ 32 + lo) % m ∧ (hi % m) * 2 ^ 32 + lo < m * 2 ^ 32 := by
  constructor
  · exact cadd (cmul (Nat.mod_mod hi m) rfl) rfl
  · have h1 : hi % m < m := Nat.mod_lt _ hm
    have h2 : (hi % m + 1) * 2 ^ 32 ≤ m * 2 ^ 32 := Nat.mul_le_mul_right _ h1
    rw [Nat.add_mul, Nat.one_mul] at h2
    omega

theorem mulmodFixed_spec (a b m : Nat) (hm : 0 < m) : mulmodFixed a b m = (a * b) % m := by
  unfold mulmodFixed
  have hlo : (a * b) % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (Nat.two_pow_pos 32)
  rw [(two_step ((a * b) / 2 ^ 32) ((a * b) % 2 ^ 32) m hm hlo).1, Nat.div_add_mod']

/-- Erratum L03: the published `mulmod` is wrong, e.g. `65536 * 65536 mod 3`. -/
theorem mulmodLegacy_wrong : mulmodLegacy 65536 65536 3 ≠ (65536 * 65536) % 3 := by decide +kernel

end WriteExecute.Arith
