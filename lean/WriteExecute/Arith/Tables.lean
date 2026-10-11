module
public import WriteExecute.Spec.Arith

public section

namespace WriteExecute.Arith

/-! C06: every 8-bit table is its specification. Finite checks are discharged by kernel evaluation
(`decide +kernel`; no native code), in pieces of at most a few thousand cases. -/

theorem all1 {n : Nat} {p : Nat → Prop} [DecidablePred p]
    (h : (List.range n).all (fun a => decide (p a)) = true) : ∀ a, a < n → p a := by
  intro a ha
  exact of_decide_eq_true (List.all_eq_true.mp h a (List.mem_range.mpr ha))

theorem all2 {n m : Nat} {p : Nat → Nat → Prop} [∀ a b, Decidable (p a b)]
    (h : (List.range n).all (fun a => (List.range m).all (fun b => decide (p a b))) = true) :
    ∀ a, a < n → ∀ b, b < m → p a b := by
  intro a ha b hb
  have h1 := List.all_eq_true.mp h a (List.mem_range.mpr ha)
  exact of_decide_eq_true (List.all_eq_true.mp h1 b (List.mem_range.mpr hb))

theorem all3d {n : Nat} {m : Nat → Nat} {k : Nat → Nat → Nat} {p : Nat → Nat → Nat → Prop}
    [∀ a b c, Decidable (p a b c)]
    (h : (List.range n).all (fun a => (List.range (m a)).all (fun b =>
      (List.range (k a b)).all (fun c => decide (p a b c)))) = true) :
    ∀ a, a < n → ∀ b, b < m a → ∀ c, c < k a b → p a b c := by
  intro a ha b hb c hc
  have h1 := List.all_eq_true.mp h a (List.mem_range.mpr ha)
  have h2 := List.all_eq_true.mp h1 b (List.mem_range.mpr hb)
  exact of_decide_eq_true (List.all_eq_true.mp h2 c (List.mem_range.mpr hc))

theorem and255 (x : Nat) : x &&& 255 = x % 256 := by
  have := Nat.and_two_pow_sub_one_eq_mod x 8
  simpa using this

theorem shr256 (x : Nat) : x >>> 8 = x / 256 := by
  have := Nat.shiftRight_eq_div_pow x 8
  simpa using this

theorem tNot_spec : ∀ i, i < 256 → tNot i = 255 - i :=
  all1 (p := fun i => tNot i = 255 - i) (by decide +kernel)

theorem tNZ_spec (i : Nat) : tNZ i = if i = 0 then 0 else 1 := by
  unfold tNZ; by_cases h : i = 0 <;> simp [h]

/-- SHLGEN: the two tables split `i * 2^o` into the byte kept and the byte carried. -/
theorem shl_split : ∀ o, o < 9 → ∀ i, i < 256 →
    tShlLo o i < 256 ∧ tShlLo o i % 2 ^ o = 0 ∧ tShlHi o i < 2 ^ o ∧
      tShlHi o i * 256 + tShlLo o i = i * 2 ^ o :=
  all2 (p := fun o i => tShlLo o i < 256 ∧ tShlLo o i % 2 ^ o = 0 ∧ tShlHi o i < 2 ^ o ∧
    tShlHi o i * 256 + tShlLo o i = i * 2 ^ o) (by decide +kernel)

theorem xor_shl_core : ∀ o, o < 9 → ∀ u, u < 2 ^ (8 - o) → ∀ h, h < 2 ^ o →
    ((u * 2 ^ o) ^^^ h) = u * 2 ^ o + h :=
  all3d (m := fun o => 2 ^ (8 - o)) (k := fun o _ => 2 ^ o)
    (p := fun o u h => ((u * 2 ^ o) ^^^ h) = u * 2 ^ o + h) (by decide +kernel)

theorem xor_shr_core : ∀ o, o < 9 → ∀ x, x < 2 ^ (8 - o) → ∀ v, v < 2 ^ o →
    (x ^^^ (v * 2 ^ (8 - o))) = x + v * 2 ^ (8 - o) :=
  all3d (m := fun o => 2 ^ (8 - o)) (k := fun o _ => 2 ^ o)
    (p := fun o x v => (x ^^^ (v * 2 ^ (8 - o))) = x + v * 2 ^ (8 - o)) (by decide +kernel)

theorem pow_split (o : Nat) (ho : o < 9) : 2 ^ (8 - o) * 2 ^ o = 256 := by
  rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]

/-- The carried byte has only the low `o` bits, the kept byte none of them, so XOR is `+`. -/
theorem shl_xor (o i h : Nat) (ho : o < 9) (hi : i < 256) (hh : h < 2 ^ o) :
    (tShlLo o i ^^^ h) = tShlLo o i + h := by
  obtain ⟨h1, h2, -, -⟩ := shl_split o ho i hi
  have hpos : 0 < 2 ^ o := Nat.two_pow_pos _
  have hx : tShlLo o i / 2 ^ o * 2 ^ o = tShlLo o i := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h2)
  have hu : tShlLo o i / 2 ^ o < 2 ^ (8 - o) := by
    have : tShlLo o i / 2 ^ o * 2 ^ o < 2 ^ (8 - o) * 2 ^ o := by
      rw [hx, pow_split o ho]; exact h1
    exact Nat.lt_of_mul_lt_mul_right this
  have := xor_shl_core o ho _ hu h hh
  rwa [hx] at this

/-- SHRGEN. -/
theorem shr_split : ∀ o, o < 9 → ∀ i, i < 256 →
    tShrHi o i < 2 ^ (8 - o) ∧ tShrLo o i < 256 ∧ tShrLo o i = (i % 2 ^ o) * 2 ^ (8 - o) ∧
      tShrHi o i = i / 2 ^ o :=
  all2 (p := fun o i => tShrHi o i < 2 ^ (8 - o) ∧ tShrLo o i < 256 ∧
    tShrLo o i = (i % 2 ^ o) * 2 ^ (8 - o) ∧ tShrHi o i = i / 2 ^ o) (by decide +kernel)

theorem shr_xor (o a j : Nat) (ho : o < 9) (ha : a < 256) (hj : j < 256) :
    (tShrHi o a ^^^ tShrLo o j) = tShrHi o a + tShrLo o j := by
  obtain ⟨h1, -, -, -⟩ := shr_split o ho a ha
  obtain ⟨-, -, h2, -⟩ := shr_split o ho j hj
  have hv : j % 2 ^ o < 2 ^ o := Nat.mod_lt _ (Nat.two_pow_pos _)
  rw [h2]
  exact xor_shr_core o ho _ h1 _ hv

/-- INC / DEC / SUB / ADD low byte follow from `x &&& 255 = x % 256`. -/
theorem inc_spec (i : Nat) (hi : i < 256) :
    tIncLo i + 256 * tIncHi i = i + 1 ∧ tIncLo i < 256 ∧ tIncHi i < 2 := by
  unfold tIncLo tIncHi; rw [and255, shr256]; omega

theorem dec_spec (i : Nat) (hi : i < 256) :
    tDecLo i + 1 = i + 256 * tDecBor i ∧ tDecLo i < 256 ∧ tDecBor i < 2 ∧ (tDecBor i = 1 → i = 0) := by
  unfold tDecLo tDecBor; rw [and255]; by_cases h : i = 0 <;> simp [h] <;> omega

theorem sub_spec (a b : Nat) (ha : a < 256) (hb : b < 256) :
    tSubLo a b + b = a + 256 * tSubBor a b ∧ tSubLo a b < 256 ∧ tSubBor a b < 2 := by
  unfold tSubLo tSubBor; rw [and255]; by_cases h : a < b <;> simp [h] <;> omega

theorem addLo_spec (a b : Nat) : tAddLo a b = (a + b) % 256 := by
  unfold tAddLo; exact and255 _

theorem addCry_chunk0 : ∀ a, a < 16 → ∀ b, b < 256 →
    tAddCry (0 + a) b = (0 + a + b) / 256 :=
  all2 (p := fun a b => tAddCry (0 + a) b = (0 + a + b) / 256) (by decide +kernel)

theorem addCry_chunk1 : ∀ a, a < 16 → ∀ b, b < 256 →
    tAddCry (16 + a) b = (16 + a + b) / 256 :=
  all2 (p := fun a b => tAddCry (16 + a) b = (16 + a + b) / 256) (by decide +kernel)

theorem addCry_chunk2 : ∀ a, a < 16 → ∀ b, b < 256 →
    tAddCry (32 + a) b = (32 + a + b) / 256 :=
  all2 (p := fun a b => tAddCry (32 + a) b = (32 + a + b) / 256) (by decide +kernel)

theorem addCry_chunk3 : ∀ a, a < 16 → ∀ b, b < 256 →
    tAddCry (48 + a) b = (48 + a + b) / 256 :=
  all2 (p := fun a b => tAddCry (48 + a) b = (48 + a + b) / 256) (by decide +kernel)

theorem addCry_chunk4 : ∀ a, a < 16 → ∀ b, b < 256 →
    tAddCry (64 + a) b = (64 + a + b) / 256 :=
  all2 (p := fun a b => tAddCry (64 + a) b = (64 + a + b) / 256) (by decide +kernel)

theorem addCry_chunk5 : ∀ a, a < 16 → ∀ b, b < 256 →
    tAddCry (80 + a) b = (80 + a + b) / 256 :=
  all2 (p := fun a b => tAddCry (80 + a) b = (80 + a + b) / 256) (by decide +kernel)

theorem addCry_chunk6 : ∀ a, a < 16 → ∀ b, b < 256 →
    tAddCry (96 + a) b = (96 + a + b) / 256 :=
  all2 (p := fun a b => tAddCry (96 + a) b = (96 + a + b) / 256) (by decide +kernel)

theorem addCry_chunk7 : ∀ a, a < 16 → ∀ b, b < 256 →
    tAddCry (112 + a) b = (112 + a + b) / 256 :=
  all2 (p := fun a b => tAddCry (112 + a) b = (112 + a + b) / 256) (by decide +kernel)

theorem addCry_chunk8 : ∀ a, a < 16 → ∀ b, b < 256 →
    tAddCry (128 + a) b = (128 + a + b) / 256 :=
  all2 (p := fun a b => tAddCry (128 + a) b = (128 + a + b) / 256) (by decide +kernel)

theorem addCry_chunk9 : ∀ a, a < 16 → ∀ b, b < 256 →
    tAddCry (144 + a) b = (144 + a + b) / 256 :=
  all2 (p := fun a b => tAddCry (144 + a) b = (144 + a + b) / 256) (by decide +kernel)

theorem addCry_chunk10 : ∀ a, a < 16 → ∀ b, b < 256 →
    tAddCry (160 + a) b = (160 + a + b) / 256 :=
  all2 (p := fun a b => tAddCry (160 + a) b = (160 + a + b) / 256) (by decide +kernel)

theorem addCry_chunk11 : ∀ a, a < 16 → ∀ b, b < 256 →
    tAddCry (176 + a) b = (176 + a + b) / 256 :=
  all2 (p := fun a b => tAddCry (176 + a) b = (176 + a + b) / 256) (by decide +kernel)

theorem addCry_chunk12 : ∀ a, a < 16 → ∀ b, b < 256 →
    tAddCry (192 + a) b = (192 + a + b) / 256 :=
  all2 (p := fun a b => tAddCry (192 + a) b = (192 + a + b) / 256) (by decide +kernel)

theorem addCry_chunk13 : ∀ a, a < 16 → ∀ b, b < 256 →
    tAddCry (208 + a) b = (208 + a + b) / 256 :=
  all2 (p := fun a b => tAddCry (208 + a) b = (208 + a + b) / 256) (by decide +kernel)

theorem addCry_chunk14 : ∀ a, a < 16 → ∀ b, b < 256 →
    tAddCry (224 + a) b = (224 + a + b) / 256 :=
  all2 (p := fun a b => tAddCry (224 + a) b = (224 + a + b) / 256) (by decide +kernel)

theorem addCry_chunk15 : ∀ a, a < 16 → ∀ b, b < 256 →
    tAddCry (240 + a) b = (240 + a + b) / 256 :=
  all2 (p := fun a b => tAddCry (240 + a) b = (240 + a + b) / 256) (by decide +kernel)

/-- ADD carry: the expression of DEFINEADD is the carry out of the byte addition. -/
theorem addCry_spec (a b : Nat) (ha : a < 256) (hb : b < 256) : tAddCry a b = (a + b) / 256 := by
  by_cases h0 : a < 16
  · have := addCry_chunk0 (a - 0) (by omega) b hb
    rwa [show 0 + (a - 0) = a by omega] at this
  by_cases h1 : a < 32
  · have := addCry_chunk1 (a - 16) (by omega) b hb
    rwa [show 16 + (a - 16) = a by omega] at this
  by_cases h2 : a < 48
  · have := addCry_chunk2 (a - 32) (by omega) b hb
    rwa [show 32 + (a - 32) = a by omega] at this
  by_cases h3 : a < 64
  · have := addCry_chunk3 (a - 48) (by omega) b hb
    rwa [show 48 + (a - 48) = a by omega] at this
  by_cases h4 : a < 80
  · have := addCry_chunk4 (a - 64) (by omega) b hb
    rwa [show 64 + (a - 64) = a by omega] at this
  by_cases h5 : a < 96
  · have := addCry_chunk5 (a - 80) (by omega) b hb
    rwa [show 80 + (a - 80) = a by omega] at this
  by_cases h6 : a < 112
  · have := addCry_chunk6 (a - 96) (by omega) b hb
    rwa [show 96 + (a - 96) = a by omega] at this
  by_cases h7 : a < 128
  · have := addCry_chunk7 (a - 112) (by omega) b hb
    rwa [show 112 + (a - 112) = a by omega] at this
  by_cases h8 : a < 144
  · have := addCry_chunk8 (a - 128) (by omega) b hb
    rwa [show 128 + (a - 128) = a by omega] at this
  by_cases h9 : a < 160
  · have := addCry_chunk9 (a - 144) (by omega) b hb
    rwa [show 144 + (a - 144) = a by omega] at this
  by_cases h10 : a < 176
  · have := addCry_chunk10 (a - 160) (by omega) b hb
    rwa [show 160 + (a - 160) = a by omega] at this
  by_cases h11 : a < 192
  · have := addCry_chunk11 (a - 176) (by omega) b hb
    rwa [show 176 + (a - 176) = a by omega] at this
  by_cases h12 : a < 208
  · have := addCry_chunk12 (a - 192) (by omega) b hb
    rwa [show 192 + (a - 192) = a by omega] at this
  by_cases h13 : a < 224
  · have := addCry_chunk13 (a - 208) (by omega) b hb
    rwa [show 208 + (a - 208) = a by omega] at this
  by_cases h14 : a < 240
  · have := addCry_chunk14 (a - 224) (by omega) b hb
    rwa [show 224 + (a - 224) = a by omega] at this
  by_cases h15 : a < 256
  · have := addCry_chunk15 (a - 240) (by omega) b hb
    rwa [show 240 + (a - 240) = a by omega] at this
  omega

end WriteExecute.Arith
