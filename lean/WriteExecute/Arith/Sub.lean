module
public import WriteExecute.Arith.Add

public section

namespace WriteExecute.Arith

theorem decIf_spec (bin a : Nat) (hc : bin ≤ 1) (ha : a < 256) :
    (decIf bin a).1 < 256 ∧ (decIf bin a).1 + bin = a + 256 * (decIf bin a).2 ∧
      (decIf bin a).2 ≤ 1 ∧ ((decIf bin a).2 = 1 → (decIf bin a).1 = 255) := by
  obtain ⟨h1, h2, h3, h4⟩ := dec_spec a ha
  by_cases h : bin = 1
  · subst h
    simp only [decIf, ite_true]
    omega
  · have : bin = 0 := by omega
    subst this
    simp [decIf]
    omega

/-- C07: digit-wise subtraction with the DEC borrow scheme. -/
theorem subDigits_spec : ∀ (as bs : List Nat) (bin : Nat), as.length = bs.length → Bytes as →
    Bytes bs → bin ≤ 1 →
    ofBytes (subDigits as bs bin).1 + ofBytes bs + bin
        = ofBytes as + 256 ^ as.length * (subDigits as bs bin).2 ∧
      (subDigits as bs bin).2 ≤ 1 ∧ Bytes (subDigits as bs bin).1 ∧
      (subDigits as bs bin).1.length = as.length
  | [], bs, bin, hl, _, _, hc => by
    cases bs with
    | nil => simp [subDigits, ofBytes, Bytes.nil, hc]
    | cons b bs => simp at hl
  | a :: as, bs, bin, hl, ha, hb, hc => by
    cases bs with
    | nil => simp at hl
    | cons b bs =>
      have hl' : as.length = bs.length := by simpa using hl
      have hb0 := hb.head
      have ha0 := ha.head
      obtain ⟨p1, p2, p3, p4⟩ := decIf_spec bin a hc ha.head
      simp only [subDigits]
      generalize decIf bin a = p at p1 p2 p3 p4 ⊢
      obtain ⟨q1, q2⟩ := p
      simp only at p1 p2 p3 p4 ⊢
      obtain ⟨s1, s2, s3⟩ := sub_spec q1 b p1 hb0
      have hc' : tSubBor q1 b + q2 ≤ 1 := by
        by_cases h : q2 = 1
        · have := p4 h; omega
        · omega
      obtain ⟨i1, i2, i3, i4⟩ := subDigits_spec as bs (tSubBor q1 b + q2) hl' ha.tail hb.tail hc'
      refine ⟨?_, i2, Bytes.cons (by omega) i3, by simp [i4]⟩
      simp only [ofBytes, List.length_cons]
      rw [pow_succ_mul]
      generalize 256 ^ as.length * (subDigits as bs (tSubBor q1 b + q2)).2 = Z at i1 ⊢
      omega

theorem subN_spec (n x y : Nat) : subN n x y = (x % 256 ^ n + 256 ^ n - y % 256 ^ n) % 256 ^ n := by
  unfold subN
  have hx := toBytes_length n x
  have hy := toBytes_length n y
  obtain ⟨i1, i2, i3, i4⟩ := subDigits_spec (toBytes n x) (toBytes n y) 0
    (by rw [hx, hy]) (toBytes_bytes n x) (toBytes_bytes n y) (by omega)
  rw [ofBytes_toBytes, ofBytes_toBytes, hx] at i1
  have hlt := ofBytes_lt _ i3
  rw [i4, hx] at hlt
  have hP : 0 < 256 ^ n := by apply Nat.pos_of_ne_zero; simp
  have hxl : x % 256 ^ n < 256 ^ n := Nat.mod_lt _ hP
  have hyl : y % 256 ^ n < 256 ^ n := Nat.mod_lt _ hP
  generalize ofBytes (subDigits (toBytes n x) (toBytes n y) 0).1 = o at *
  generalize (subDigits (toBytes n x) (toBytes n y) 0).2 = c at *
  rcases Nat.lt_or_ge c 1 with h | h
  · have c0 : c = 0 := by omega
    subst c0
    have e : x % 256 ^ n + 256 ^ n - y % 256 ^ n = o + 256 ^ n * 1 := by omega
    rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · have c1 : c = 1 := by omega
    subst c1
    have e : x % 256 ^ n + 256 ^ n - y % 256 ^ n = o + 256 ^ n * 0 := by omega
    rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

end WriteExecute.Arith
