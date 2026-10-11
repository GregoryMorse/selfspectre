module
public import WriteExecute.Arith.Reduce

public section

namespace WriteExecute.Arith

/-! C12: right-to-left square and multiply, and the operation count (erratum W05). -/

theorem pow_split_two (b e : Nat) : b ^ e = (b * b) ^ (e / 2) * b ^ (e % 2) := by
  have h := Nat.div_add_mod e 2
  conv => lhs; rw [← h]
  rw [Nat.pow_add, Nat.pow_mul, Nat.pow_two]

theorem modexpLoop_spec (m : Nat) (hm : 0 < m) :
    ∀ (k r b e : Nat), r < m → e < 2 ^ k → modexpLoop m k r b e = (r * b ^ e) % m
  | 0, r, b, e, hr, he => by
    have : e = 0 := by simpa using he
    subst this
    simp [modexpLoop, Nat.mod_eq_of_lt hr]
  | k + 1, r, b, e, hr, he => by
    by_cases h0 : e = 0
    · subst h0
      simp [modexpLoop, Nat.mod_eq_of_lt hr]
    · have hr' : (if e % 2 = 1 then r * b % m else r) < m := by
        split
        · exact Nat.mod_lt _ hm
        · exact hr
      have he' : e / 2 < 2 ^ k := by
        have : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
        omega
      have ih := modexpLoop_spec m hm k _ (b * b % m) (e / 2) hr' he'
      simp only [modexpLoop, h0, ite_false]
      rw [ih, pow_split_two b e]
      have h1 : (if e % 2 = 1 then r * b % m else r) % m = (r * b ^ (e % 2)) % m := by
        have hlt : e % 2 < 2 := Nat.mod_lt _ (by omega)
        by_cases ho : e % 2 = 1
        · simp [ho, Nat.mod_mod]
        · have : e % 2 = 0 := by omega
          simp [ho, this]
      have h2 : (b * b % m) ^ (e / 2) % m = (b * b) ^ (e / 2) % m := (Nat.pow_mod _ _ _).symm
      have := cmul h1 h2
      rw [this, Nat.mul_assoc, Nat.mul_comm (b ^ (e % 2))]


/-- C12: the assembly version (initial result `1`) is correct for moduli `m ≥ 2`. -/
theorem modexpAsm_spec (b e m : Nat) (hm : 2 ≤ m) (he : e < 2 ^ 32) :
    modexpAsm b e m = b ^ e % m := by
  unfold modexpAsm
  rw [modexpLoop_spec m (by omega) 32 1 (b % m) e (by omega) he, Nat.one_mul, ← Nat.pow_mod]

/-- The corrected C reference (initial result `1 % m`, erratum L02) is correct for every `m ≥ 1`. -/
theorem modexpRef_spec (b e m : Nat) (hm : 1 ≤ m) (he : e < 2 ^ 32) :
    modexpRef b e m = b ^ e % m := by
  unfold modexpRef
  rw [modexpLoop_spec m (by omega) 32 (1 % m) (b % m) e (Nat.mod_lt _ (by omega)) he]
  have h1 : (1 % m * (b % m) ^ e) % m = (1 * b ^ e) % m :=
    cmul (Nat.mod_mod 1 m) (Nat.pow_mod b e m).symm
  rw [h1, Nat.one_mul]

/-- Documented precondition (L05): for `m = 1`, `e = 0` the assembly returns `1`, the reference `0`. -/
theorem modexp_m1_e0 (b : Nat) : modexpAsm b 0 1 = 1 ∧ modexpRef b 0 1 = 0 := by
  simp [modexpAsm, modexpRef, modexpLoop]

theorem naiveLoop_spec (m b : Nat) (hm : 0 < m) :
    ∀ (k c : Nat), c < m → naiveLoop m b k c = (c * b ^ k) % m
  | 0, c, hc => by simp [naiveLoop, Nat.mod_eq_of_lt hc]
  | k + 1, c, hc => by
    rw [naiveLoop, naiveLoop_spec m b hm k _ (Nat.mod_lt _ hm), mod_mul_right', Nat.pow_succ,
      Nat.mul_assoc, Nat.mul_comm b, ← Nat.mul_assoc]

theorem modexpNaive_spec (b e m : Nat) (hm : 1 ≤ m) : modexpNaive b e m = b ^ e % m := by
  unfold modexpNaive
  by_cases h1 : m = 1
  · subst h1; simp [Nat.mod_one]
  · simp only [h1, ite_false]
    rw [naiveLoop_spec m b (by omega) e 1 (by omega), Nat.one_mul]

/-- Number of bits of `e`. -/
@[expose] def bitlen (e : Nat) : Nat := if e = 0 then 0 else Nat.log2 e + 1

theorem bitlen_step (e : Nat) (he : 0 < e) : bitlen e = bitlen (e / 2) + 1 := by
  unfold bitlen
  by_cases h2 : 2 ≤ e
  · have : e / 2 ≠ 0 := by omega
    rw [Nat.log2_def e]
    simp [h2, this]
    omega
  · have : e = 1 := by omega
    subst this
    simp [Nat.log2_def]

theorem popcount_zero (k : Nat) : popcount k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [popcount, ih]

/-- C12 / W05: the number of modular multiplications is `bitlen e + popcount e`, i.e.
`⌊log₂ e⌋ + 1 + popcount e`, not `⌊log₂ e⌋ + popcount e`. -/
theorem mulCount_eq : ∀ (k e : Nat), e < 2 ^ k → mulCount k e = bitlen e + popcount k e
  | 0, e, he => by
    have : e = 0 := by simpa using he
    subst this
    simp [mulCount, bitlen, popcount]
  | k + 1, e, he => by
    by_cases h0 : e = 0
    · subst h0
      simp [mulCount, bitlen, popcount_zero]
    · have he' : e / 2 < 2 ^ k := by
        have : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
        omega
      have ih := mulCount_eq k (e / 2) he'
      have hb := bitlen_step e (by omega)
      simp only [mulCount, popcount, h0, ite_false]
      omega

theorem mulCount_log2 (e : Nat) (h1 : 1 ≤ e) (h2 : e < 2 ^ 32) :
    mulCount 32 e = Nat.log2 e + 1 + popcount 32 e := by
  rw [mulCount_eq 32 e h2]
  unfold bitlen
  simp [show e ≠ 0 by omega]

end WriteExecute.Arith
