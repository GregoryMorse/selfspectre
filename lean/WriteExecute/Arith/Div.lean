module
public import WriteExecute.Arith.Mul

public section

namespace WriteExecute.Arith

/-! C10: the 64-iteration restoring division of `doDivision` (writeexec.c, WriteExecDIV32). -/

/-- One iteration, abstractly: shift in the top bit of `quot` into the remainder, subtract the
divisor when it fits (counting the overflow bit of the 32-bit remainder), set the quotient's low bit. -/
theorem divStep_abs (y q r : Nat) (hy0 : 0 < y) (hy : y < 2 ^ 32) (hr : r < y) (hq : q < 2 ^ 64) :
    divStep y (q, r) =
      (q * 2 % 2 ^ 64 + (if y ≤ 2 * r + q / 2 ^ 63 then 1 else 0),
       2 * r + q / 2 ^ 63 - (if y ≤ 2 * r + q / 2 ^ 63 then y else 0)) := by
  unfold divStep
  by_cases c1 : q * 2 % 2 ^ 64 < q <;> simp only [c1, ↓reduceIte] <;> (repeat' split) <;>
    simp only [Prod.mk.injEq] <;> constructor <;> omega


/-- Appending one bit to the dividend prefix: remainder and quotient digit. -/
theorem div_rem_step (y A D r bit : Nat) (hy : 0 < y) (hA : A = y * D + r) (hr : r < y)
    (hb : bit ≤ 1) :
    (2 * A + bit) % y = 2 * r + bit - (if y ≤ 2 * r + bit then y else 0) ∧
      (2 * A + bit) / y = 2 * D + (if y ≤ 2 * r + bit then 1 else 0) := by
  have hl : y * (2 * D) = 2 * (y * D) := Nat.mul_left_comm _ _ _
  have e : 2 * A + bit = (2 * r + bit) + y * (2 * D) := by rw [hA]; omega
  rw [e, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hy]
  by_cases hc : y ≤ 2 * r + bit
  · have h1 : (2 * r + bit) % y = 2 * r + bit - y := by
      rw [Nat.mod_eq_sub_mod hc]; exact Nat.mod_eq_of_lt (by omega)
    have h2 : (2 * r + bit) / y = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    simp only [hc, ite_true]
    omega
  · have h1 : (2 * r + bit) % y = 2 * r + bit := Nat.mod_eq_of_lt (by omega)
    have h2 : (2 * r + bit) / y = 0 := Nat.div_eq_of_lt (by omega)
    simp only [hc, ite_false]
    omega

@[expose] def DivInv (x y k : Nat) (s : Nat × Nat) : Prop :=
  s.1 = (x % 2 ^ (64 - k)) * 2 ^ k + (x / 2 ^ (64 - k)) / y ∧ s.2 = (x / 2 ^ (64 - k)) % y

theorem divInv_step (x y k : Nat) (s : Nat × Nat) (hx : x < 2 ^ 64) (hy0 : 0 < y) (hy : y < 2 ^ 32)
    (hk : k < 64) (h : DivInv x y k s) : DivInv x y (k + 1) (divStep y s) := by
  obtain ⟨q, r⟩ := s
  obtain ⟨hq, hr⟩ := h
  simp only [] at hq hr
  generalize ht : 63 - k = t
  have e1 : 64 - k = t + 1 := by omega
  have e2 : 64 - (k + 1) = t := by omega
  have hPK : 2 ^ t * 2 ^ k = 2 ^ 63 := by rw [← Nat.pow_add]; congr 1; omega
  rw [e1] at hq hr
  unfold DivInv
  simp only [e2]
  -- decomposition of x
  have hdiv : x / 2 ^ (t + 1) = x / 2 ^ t / 2 := by
    rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  have hmod : x % 2 ^ (t + 1) = x % 2 ^ t + 2 ^ t * (x / 2 ^ t % 2) := by
    rw [Nat.pow_succ, Nat.mod_mul]
  have hx2 := Nat.div_add_mod (x / 2 ^ t) 2
  generalize hA : x / 2 ^ (t + 1) = A at hq hr
  generalize hbit : x / 2 ^ t % 2 = bit at hmod hx2
  generalize hxl : x % 2 ^ t = xl at hmod ⊢
  have hAK : A < 2 ^ k := by
    rw [← hA]
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add]
    calc x < 2 ^ 64 := hx
      _ = 2 ^ (t + 1 + k) := by congr 1; omega
  have hxlP : xl < 2 ^ t := by rw [← hxl]; exact Nat.mod_lt _ (Nat.two_pow_pos t)
  have hbit1 : bit ≤ 1 := by have := Nat.mod_lt (x / 2 ^ t) (show 0 < 2 by omega); omega
  have hr' : r < y := by rw [hr]; exact Nat.mod_lt _ hy0
  have hD : A / y ≤ A := Nat.div_le_self _ _
  have hxlK : (xl + 1) * 2 ^ k ≤ 2 ^ t * 2 ^ k := Nat.mul_le_mul_right _ hxlP
  rw [Nat.add_mul, Nat.one_mul] at hxlK
  rw [hmod] at hq
  have hxA : x / 2 ^ t = 2 * A + bit := by rw [hA] at hdiv; omega
  rw [hxA, Nat.pow_succ]
  have hA' : A = y * (A / y) + r := by rw [hr]; exact (Nat.div_add_mod A y).symm
  have hbc : bit = 0 ∨ bit = 1 := by omega
  have key : q * 2 % 2 ^ 64 = 2 * (xl * 2 ^ k + A / y) ∧ q / 2 ^ 63 = bit ∧ q < 2 ^ 64 := by
    rcases hbc with rfl | rfl
    · simp only [Nat.mul_zero, Nat.add_zero] at hq
      generalize 2 ^ t * 2 ^ k = PK at hxlK hPK
      generalize A / y = D at hq hD ⊢
      refine ⟨?_, ?_, ?_⟩ <;> omega
    · simp only [Nat.mul_one, Nat.add_mul] at hq
      generalize 2 ^ t * 2 ^ k = PK at hq hxlK hPK
      generalize A / y = D at hq hD ⊢
      refine ⟨?_, ?_, ?_⟩ <;> omega
  obtain ⟨k1, k2, k3⟩ := key
  rw [divStep_abs y q r hy0 hy hr' k3, k1, k2]
  obtain ⟨d1, d2⟩ := div_rem_step y A (A / y) r bit hy0 hA' hr' hbit1
  have hm : xl * (2 ^ k * 2) = 2 * (xl * 2 ^ k) := by
    rw [← Nat.mul_assoc, Nat.mul_comm]
  constructor
  · rw [d2, hm]; omega
  · rw [d1]


theorem divRun_inv (x y : Nat) (hx : x < 2 ^ 64) (hy0 : 0 < y) (hy : y < 2 ^ 32) :
    ∀ (n j : Nat) (s : Nat × Nat), j + n ≤ 64 → DivInv x y j s → DivInv x y (j + n) (divRun y n s)
  | 0, j, s, _, h => by simpa [divRun] using h
  | n + 1, j, s, hn, h => by
    have h1 := divInv_step x y j s hx hy0 hy (by omega) h
    have h2 := divRun_inv x y hx hy0 hy n (j + 1) (divStep y s) (by omega) h1
    have e : j + 1 + n = j + (n + 1) := by omega
    rw [e] at h2
    exact h2

/-- C10: 64/32-bit division and modulo (quotient reduced mod 2^32, remainder), for a nonzero divisor. -/
theorem doDivision_spec (x y : Nat) (hx : x < 2 ^ 64) (hy0 : 0 < y) (hy : y < 2 ^ 32) :
    doDivision x y = ((x / y) % 2 ^ 32, x % y) := by
  unfold doDivision
  have h0 : DivInv x y 0 (x, 0) := by
    unfold DivInv
    simp only [Nat.sub_zero, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hx,
      Nat.div_eq_of_lt hx, Nat.zero_div, Nat.add_zero, Nat.zero_mod]
    trivial
  have h := divRun_inv x y hx hy0 hy 64 0 (x, 0) (by omega) h0
  obtain ⟨h1, h2⟩ := h
  simp only [Nat.zero_add, Nat.sub_self, Nat.pow_zero, Nat.mod_one, Nat.zero_mul, Nat.zero_add,
    Nat.div_one] at h1 h2
  simp only [h1, h2]

end WriteExecute.Arith
