module
public import WriteExecute.Arith.Tables
public import WriteExecute.Arith.Bytes

public section

namespace WriteExecute.Arith

theorem incIf_spec (cin a : Nat) (hc : cin ≤ 1) (ha : a < 256) :
    (incIf cin a).1 < 256 ∧ (incIf cin a).1 + 256 * (incIf cin a).2 = a + cin ∧
      (incIf cin a).2 ≤ 1 ∧ ((incIf cin a).2 = 1 → (incIf cin a).1 = 0) := by
  obtain ⟨h1, h2, h3⟩ := inc_spec a ha
  by_cases h : cin = 1
  · subst h
    simp only [incIf, ite_true]
    omega
  · have : cin = 0 := by omega
    subst this
    simp [incIf]
    omega

theorem pow_succ_mul (n c : Nat) : 256 ^ (n + 1) * c = 256 * (256 ^ n * c) := by
  rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm]

/-- C07: the digit-wise addition with the INC carry scheme adds, and its carry out is a bit. -/
theorem addDigits_spec : ∀ (as bs : List Nat) (cin : Nat), as.length = bs.length → Bytes as →
    Bytes bs → cin ≤ 1 →
    ofBytes (addDigits as bs cin).1 + 256 ^ as.length * (addDigits as bs cin).2
        = ofBytes as + ofBytes bs + cin ∧
      (addDigits as bs cin).2 ≤ 1 ∧ Bytes (addDigits as bs cin).1 ∧
      (addDigits as bs cin).1.length = as.length
  | [], bs, cin, hl, _, _, hc => by
    cases bs with
    | nil => simp [addDigits, ofBytes, Bytes.nil, hc]
    | cons b bs => simp at hl
  | a :: as, bs, cin, hl, ha, hb, hc => by
    cases bs with
    | nil => simp at hl
    | cons b bs =>
      have hl' : as.length = bs.length := by simpa using hl
      have hb0 := hb.head
      have ha0 := ha.head
      obtain ⟨p1, p2, p3, p4⟩ := incIf_spec cin a hc ha.head
      simp only [addDigits]
      generalize incIf cin a = p at p1 p2 p3 p4 ⊢
      obtain ⟨q1, q2⟩ := p
      simp only at p1 p2 p3 p4 ⊢
      have hlo := addLo_spec q1 b
      have hcy := addCry_spec q1 b p1 hb.head
      have hc' : tAddCry q1 b + q2 ≤ 1 := by
        rw [hcy]
        by_cases h : q2 = 1
        · have := p4 h; omega
        · omega
      obtain ⟨i1, i2, i3, i4⟩ := addDigits_spec as bs (tAddCry q1 b + q2) hl' ha.tail hb.tail hc'
      refine ⟨?_, i2, Bytes.cons (by rw [hlo]; exact Nat.mod_lt _ (by omega)) i3, by simp [i4]⟩
      simp only [ofBytes, List.length_cons]
      rw [pow_succ_mul]
      generalize 256 ^ as.length * (addDigits as bs (tAddCry q1 b + q2)).2 = Z at i1 ⊢
      rw [hlo]
      omega

theorem addN_spec (n x y : Nat) : addN n x y = (x + y) % 256 ^ n := by
  unfold addN
  have hx := toBytes_length n x
  have hy := toBytes_length n y
  obtain ⟨i1, i2, i3, i4⟩ := addDigits_spec (toBytes n x) (toBytes n y) 0
    (by rw [hx, hy]) (toBytes_bytes n x) (toBytes_bytes n y) (by omega)
  rw [ofBytes_toBytes, ofBytes_toBytes, hx] at i1
  have hlt := ofBytes_lt _ i3
  rw [i4, hx] at hlt
  generalize ofBytes (addDigits (toBytes n x) (toBytes n y) 0).1 = o at *
  generalize (addDigits (toBytes n x) (toBytes n y) 0).2 = c at *
  have e : x % 256 ^ n + y % 256 ^ n = o + 256 ^ n * c := by omega
  rw [Nat.add_mod, e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

end WriteExecute.Arith
