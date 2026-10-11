module
public import WriteExecute.Arith.Add

public section

namespace WriteExecute.Arith

/-! C08: shifts and XOR. -/

theorem pow256_pos (n : Nat) : 0 < 256 ^ n := by apply Nat.pos_of_ne_zero; simp

theorem bytes_append {l₁ l₂ : List Nat} (h₁ : Bytes l₁) (h₂ : Bytes l₂) : Bytes (l₁ ++ l₂) := by
  intro d hd
  rcases List.mem_append.mp hd with h | h
  · exact h₁ d h
  · exact h₂ d h

theorem bytes_replicate0 (k : Nat) : Bytes (List.replicate k 0) := by
  intro d hd
  rcases (List.mem_replicate.mp hd) with ⟨_, rfl⟩
  omega

theorem bytes_take {l : List Nat} (m : Nat) (h : Bytes l) : Bytes (l.take m) :=
  fun d hd => h d (List.mem_of_mem_take hd)

theorem bytes_drop {l : List Nat} (m : Nat) (h : Bytes l) : Bytes (l.drop m) :=
  fun d hd => h d (List.mem_of_mem_drop hd)

theorem ofBytes_take : ∀ (m : Nat) (l : List Nat), Bytes l → ofBytes (l.take m) = ofBytes l % 256 ^ m
  | 0, l, _ => by simp [ofBytes, Nat.mod_one]
  | m + 1, [], _ => by simp [ofBytes]
  | m + 1, a :: l, h => by
    have ha := h.head
    have ih := ofBytes_take m l h.tail
    have e : 256 ^ (m + 1) = 256 * 256 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
    have h1 : (a + 256 * ofBytes l) % 256 = a := by omega
    have h2 : (a + 256 * ofBytes l) / 256 = ofBytes l := by omega
    simp only [List.take_succ_cons, ofBytes, ih]
    rw [e, Nat.mod_mul, h1, h2]

theorem ofBytes_replicate_append (k : Nat) (l : List Nat) :
    ofBytes (List.replicate k 0 ++ l) = 256 ^ k * ofBytes l := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, ofBytes, ih, Nat.pow_succ]
    rw [Nat.mul_comm (256 ^ k) 256, Nat.mul_assoc]
    omega

theorem ofBytes_replicate_zero (k : Nat) : ofBytes (List.replicate k 0) = 0 := by
  induction k with
  | zero => simp [ofBytes]
  | succ k ih => simp [List.replicate_succ, ofBytes, ih]

theorem ofBytes_append_zeros (k : Nat) : ∀ l : List Nat, ofBytes (l ++ List.replicate k 0) = ofBytes l
  | [] => by simp only [List.nil_append, ofBytes]; exact ofBytes_replicate_zero k
  | a :: l => by simp [ofBytes, ofBytes_append_zeros k l]

theorem ofBytes_drop : ∀ (k : Nat) (l : List Nat), Bytes l → ofBytes (l.drop k) = ofBytes l / 256 ^ k
  | 0, l, _ => by simp
  | k + 1, [], _ => by simp [ofBytes]
  | k + 1, a :: l, h => by
    have ha := h.head
    have ih := ofBytes_drop k l h.tail
    have h2 : (a + 256 * ofBytes l) / 256 = ofBytes l := by omega
    simp only [List.drop_succ_cons, ofBytes, ih]
    rw [Nat.pow_succ, Nat.mul_comm (256 ^ k) 256, ← Nat.div_div_eq_div_mul, h2]

theorem mod_mul_left' (a b P : Nat) : (a * (b % P)) % P = (a * b) % P := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

theorem mod_mul_right' (a b P : Nat) : ((a % P) * b) % P = (a * b) % P := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

/-! Left shift. -/

theorem shlPass_spec (o : Nat) (ho : o < 8) : ∀ (bs : List Nat) (h : Nat), Bytes bs → h < 2 ^ o →
    Bytes (shlPass o h bs) ∧ (shlPass o h bs).length = bs.length ∧
      ∃ c, ofBytes (shlPass o h bs) + 256 ^ bs.length * c = h + ofBytes bs * 2 ^ o
  | [], h, _, _ => by
    refine ⟨Bytes.nil, rfl, h, ?_⟩
    simp [shlPass, ofBytes]
  | b :: bs, h, hb, hh => by
    have hb0 := hb.head
    obtain ⟨s1, s2, s3, s4⟩ := shl_split o (by omega) b hb0
    have hx := shl_xor o b h (by omega) hb0 hh
    have h8 : 2 ^ o ≤ 2 ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
    have hlt : (tShlLo o b ^^^ h) < 256 := by
      have := Nat.xor_lt_two_pow (n := 8) (x := tShlLo o b) (y := h) (by simpa using s1)
        (by omega)
      simpa using this
    obtain ⟨r1, r2, c, r3⟩ := shlPass_spec o ho bs (tShlHi o b) hb.tail s3
    refine ⟨Bytes.cons hlt r1, by simp only [shlPass, List.length_cons, r2], c, ?_⟩
    simp only [shlPass, ofBytes, List.length_cons]
    rw [pow_succ_mul, hx, Nat.add_mul, Nat.mul_assoc]
    generalize 256 ^ bs.length * c = Z at r3 ⊢
    omega

theorem shlPass_val (o : Nat) (ho : o < 8) (bs : List Nat) (hb : Bytes bs) :
    ofBytes (shlPass o 0 bs) = (ofBytes bs * 2 ^ o) % 256 ^ bs.length := by
  obtain ⟨r1, r2, c, r3⟩ := shlPass_spec o ho bs 0 hb (Nat.two_pow_pos o)
  have hlt := ofBytes_lt _ r1
  rw [r2] at hlt
  have r3' : ofBytes (shlPass o 0 bs) + 256 ^ bs.length * c = ofBytes bs * 2 ^ o := by
    simpa using r3
  rw [← r3', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

theorem shlN_spec (n x c : Nat) : shlN n x c = (x * 2 ^ c) % 256 ^ n := by
  unfold shlN
  have hL : Bytes ((List.replicate (c / 8) 0 ++ toBytes n x).take n) :=
    bytes_take n (bytes_append (bytes_replicate0 _) (toBytes_bytes n x))
  have hlen : ((List.replicate (c / 8) 0 ++ toBytes n x).take n).length = n := by
    simp [toBytes_length]
  rw [shlPass_val (c % 8) (by omega) _ hL, hlen, ofBytes_take, ofBytes_replicate_append,
    ofBytes_toBytes]
  · generalize hk : c / 8 = k
    generalize ho : c % 8 = o
    have hc : c = 8 * k + o := by omega
    subst hc
    have e : 2 ^ (8 * k + o) = 256 ^ k * 2 ^ o := by
      rw [Nat.pow_add, Nat.pow_mul]
    rw [e, mod_mul_left', mod_mul_right', Nat.mul_comm (256 ^ k) x, Nat.mul_assoc]
  · exact bytes_append (bytes_replicate0 _) (toBytes_bytes n x)

/-! Right shift. -/

theorem shr_step (m w b c R : Nat) (hm : 0 < m) (hmw : m * w = 256) :
    b / m + (c % m) * w + 256 * ((c + 256 * R) / m) = (b + 256 * (c + 256 * R)) / m := by
  have e1 : 256 * (c + 256 * R) = m * (w * (c + 256 * R)) := by
    rw [← Nat.mul_assoc, hmw]
  have e2 : 256 * R = m * (w * R) := by rw [← Nat.mul_assoc, hmw]
  have d1 : (b + 256 * (c + 256 * R)) / m = b / m + w * (c + 256 * R) := by
    rw [e1, Nat.add_mul_div_left _ _ hm]
  have d2 : (c + 256 * R) / m = c / m + w * R := by
    rw [e2, Nat.add_mul_div_left _ _ hm]
  have hc : w * c = 256 * (c / m) + (c % m) * w := by
    have := Nat.div_add_mod c m
    calc w * c = w * (m * (c / m) + c % m) := by rw [this]
      _ = (m * w) * (c / m) + (c % m) * w := by
        rw [Nat.mul_add, Nat.mul_comm m w, Nat.mul_assoc, Nat.mul_comm w (c % m)]
      _ = 256 * (c / m) + (c % m) * w := by rw [hmw]
  have hR : w * (256 * R) = 256 * (w * R) := Nat.mul_left_comm _ _ _
  rw [d1, d2, Nat.mul_add w c (256 * R), hR]
  omega

theorem shrPass_spec (o : Nat) (ho : o < 8) : ∀ (bs : List Nat), Bytes bs →
    Bytes (shrPass o bs) ∧ (shrPass o bs).length = bs.length ∧
      ofBytes (shrPass o bs) = ofBytes bs / 2 ^ o
  | [], _ => by simp [shrPass, ofBytes, Bytes.nil]
  | [b], hb => by
    obtain ⟨s1, -, -, s3⟩ := shr_split o (by omega) b hb.head
    refine ⟨Bytes.cons (by
      have : 2 ^ (8 - o) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
      omega) Bytes.nil, rfl, ?_⟩
    simp [shrPass, ofBytes, s3]
  | b :: c :: rest, hb => by
    have hb0 := hb.head
    have hc0 := hb.tail.head
    obtain ⟨s1, -, -, s3⟩ := shr_split o (by omega) b hb0
    obtain ⟨t1, t0, t2, t3⟩ := shr_split o (by omega) c hc0
    have hx := shr_xor o b c (by omega) hb0 hc0
    have h8 : 2 ^ (8 - o) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
    have hlt : (tShrHi o b ^^^ tShrLo o c) < 256 := by
      have := Nat.xor_lt_two_pow (n := 8) (x := tShrHi o b) (y := tShrLo o c) (by omega)
        (by simpa using t0)
      simpa using this
    obtain ⟨r1, r2, r3⟩ := shrPass_spec o ho (c :: rest) hb.tail
    refine ⟨Bytes.cons hlt r1, by simp only [shrPass, List.length_cons] at r2 ⊢; omega, ?_⟩
    have hm : 0 < 2 ^ o := Nat.two_pow_pos o
    have hmw : 2 ^ o * 2 ^ (8 - o) = 256 := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
    have key := shr_step (2 ^ o) (2 ^ (8 - o)) b c (ofBytes rest) hm hmw
    simp only [shrPass, ofBytes] at r3 ⊢
    rw [hx, r3, s3, t2, ← key]

theorem shrN_spec (n x c : Nat) : shrN n x c = (x % 256 ^ n) / 2 ^ c := by
  unfold shrN
  have hb : Bytes ((toBytes n x).drop (c / 8) ++ List.replicate (c / 8) 0) :=
    bytes_append (bytes_drop _ (toBytes_bytes n x)) (bytes_replicate0 _)
  obtain ⟨-, -, h3⟩ := shrPass_spec (c % 8) (by omega) _ hb
  rw [h3, ofBytes_append_zeros, ofBytes_drop _ _ (toBytes_bytes n x), ofBytes_toBytes,
    Nat.div_div_eq_div_mul]
  generalize hk : c / 8 = k
  generalize ho : c % 8 = o
  have hc : c = 8 * k + o := by omega
  subst hc
  have e : 2 ^ (8 * k + o) = 256 ^ k * 2 ^ o := by
    rw [Nat.pow_add, Nat.pow_mul]
  rw [e]

/-! XOR. -/

theorem xorDigits_spec : ∀ (as bs : List Nat), as.length = bs.length → Bytes as → Bytes bs →
    Bytes (xorDigits as bs) ∧ (xorDigits as bs).length = as.length ∧
      ofBytes (xorDigits as bs) = ofBytes as ^^^ ofBytes bs
  | [], bs, hl, _, _ => by
    cases bs with
    | nil => simp [xorDigits, ofBytes, Bytes.nil]
    | cons b bs => simp at hl
  | a :: as, bs, hl, ha, hb => by
    cases bs with
    | nil => simp at hl
    | cons b bs =>
      have hl' : as.length = bs.length := by simpa using hl
      obtain ⟨i1, i2, i3⟩ := xorDigits_spec as bs hl' ha.tail hb.tail
      have hlt : (a ^^^ b) < 256 := by
        have := Nat.xor_lt_two_pow (n := 8) (x := a) (y := b) (by simpa using ha.head)
          (by simpa using hb.head)
        simpa using this
      refine ⟨Bytes.cons hlt i1, by simp only [xorDigits, List.length_cons, i2], ?_⟩
      simp only [xorDigits, ofBytes, i3]
      have m1 := @Nat.xor_mod_two_pow (a + 256 * ofBytes as) (b + 256 * ofBytes bs) 8
      have d1 := @Nat.xor_div_two_pow (a + 256 * ofBytes as) (b + 256 * ofBytes bs) 8
      have ha0 := ha.head
      have hb0 := hb.head
      have e1 : (a + 256 * ofBytes as) % 2 ^ 8 = a := by simp; omega
      have e2 : (b + 256 * ofBytes bs) % 2 ^ 8 = b := by simp; omega
      have e3 : (a + 256 * ofBytes as) / 2 ^ 8 = ofBytes as := by simp; omega
      have e4 : (b + 256 * ofBytes bs) / 2 ^ 8 = ofBytes bs := by simp; omega
      rw [e1, e2] at m1
      rw [e3, e4] at d1
      have := Nat.div_add_mod ((a + 256 * ofBytes as) ^^^ (b + 256 * ofBytes bs)) (2 ^ 8)
      rw [m1, d1] at this
      simp at this
      omega

theorem xorN_spec (n x y : Nat) : xorN n x y = (x ^^^ y) % 256 ^ n := by
  unfold xorN
  obtain ⟨-, -, h3⟩ := xorDigits_spec (toBytes n x) (toBytes n y)
    (by rw [toBytes_length, toBytes_length]) (toBytes_bytes n x) (toBytes_bytes n y)
  rw [h3, ofBytes_toBytes, ofBytes_toBytes]
  have e : 256 ^ n = 2 ^ (8 * n) := by rw [Nat.pow_mul]
  rw [e, Nat.xor_mod_two_pow]

end WriteExecute.Arith
