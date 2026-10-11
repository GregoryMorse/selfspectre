module
public import WriteExecute.Spec.X86

public section

namespace WriteExecute.X86

theorem Code_append (m : Mem) : ∀ (xs ys : List Nat) (a : Nat),
    Code m a (xs ++ ys) ↔ Code m a xs ∧ Code m (a + xs.length) ys
  | [], ys, a => by simp [Code]
  | x :: xs, ys, a => by
    simp only [List.cons_append, Code, Code_append m xs ys (a + 1), List.length_cons, and_assoc]
    rw [show a + 1 + xs.length = a + (xs.length + 1) by omega]

theorem Code_frame (m : Mem) (e n v : Nat) :
    ∀ (bs : List Nat) (a : Nat), Code m a bs → (a + bs.length ≤ e ∨ e + n ≤ a) →
      Code (wr m e n v) a bs
  | [], _, _, _ => trivial
  | b :: bs, a, h, hd => by
    refine ⟨?_, Code_frame m e n v bs (a + 1) h.2 (by simp at hd; omega)⟩
    have : ¬(e ≤ a ∧ a < e + n) := by simp at hd; omega
    simp only [wr, this, if_false]
    exact h.1

theorem rd_le (m : Mem) : ∀ (n v a : Nat), Code m a (le n v) → v < 256 ^ n → rd m a n = v
  | 0, v, a, _, hv => by
    have : v = 0 := by simpa using hv
    subst this; rfl
  | n + 1, v, a, h, hv => by
    have ih := rd_le m n (v / 256) (a + 1) h.2 (by
      rw [Nat.pow_succ, Nat.mul_comm] at hv; exact Nat.div_lt_of_lt_mul hv)
    simp only [rd, ih, h.1]
    omega

theorem le_bound (n v : Nat) : (le n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [le, ih]

/-- Well-formed instructions: operands fit their fields. -/
@[expose] def Wf : Ins → Prop
  | .nop => True
  | .jmp8 r => r < 256
  | .jmp32 r => r < 2 ^ 32
  | .movB d i => d < 2 ^ 32 ∧ i < 256
  | .movW d i => d < 2 ^ 32 ∧ i < 2 ^ 16
  | .movD d i => d < 2 ^ 32 ∧ i < 2 ^ 32

theorem decode_enc (m : Mem) (pc : Nat) (ins : Ins) (hw : Wf ins) (h : Code m pc (enc ins)) :
    decode m pc = some ins := by
  cases ins with
  | nop => simp [enc, Code] at h; simp [decode, h]
  | jmp8 r => simp [enc, Code] at h; simp [decode, h]
  | jmp32 r =>
    simp only [enc, Code] at h
    have := rd_le m 4 r (pc + 1) h.2 (by simp only [Wf] at hw; omega)
    simp [decode, h.1, this]
  | movB d i =>
    simp only [enc, List.cons_append, Code_append, Code, le_bound] at h
    have := rd_le m 4 d (pc + 2) h.2.2.1 (by simpa using hw.1)
    simp [decode, h.1, h.2.1, this, h.2.2.2.1]
  | movW d i =>
    simp only [enc, List.cons_append, Code_append, Code, le_bound] at h
    have h1 := rd_le m 4 d (pc + 3) h.2.2.2.1 (by simpa using hw.1)
    have h2 := rd_le m 2 i (pc + 7) h.2.2.2.2 (by simpa using hw.2)
    simp [decode, h.1, h.2.1, h.2.2.1, h1, h2]
  | movD d i =>
    simp only [enc, List.cons_append, Code_append, Code, le_bound] at h
    have h1 := rd_le m 4 d (pc + 2) h.2.2.1 (by simpa using hw.1)
    have h2 := rd_le m 4 i (pc + 6) h.2.2.2 (by simpa using hw.2)
    simp [decode, h.1, h.2.1, h1, h2]

theorem sext32_small (r : Nat) (h : r < 2 ^ 31) : sext 32 r = (r : Int) := by
  simp only [sext]; rw [if_pos (by simpa using h)]

theorem sext8_small (r : Nat) (h : r < 128) : sext 8 r = (r : Int) := by
  simp only [sext]; rw [if_pos (by simpa using h)]

theorem step_nop (mode : Mode) (m : Mem) (pc : Nat) (h : Code m pc (enc .nop)) :
    step mode (pc, m) = some (pc + 1, m) := by
  simp [step, decode_enc m pc .nop trivial h]

theorem step_jmp8 (mode : Mode) (m : Mem) (pc r : Nat) (hr : r < 128)
    (h : Code m pc (enc (.jmp8 r))) : step mode (pc, m) = some (pc + 2 + r, m) := by
  have hd := decode_enc m pc (.jmp8 r) (by simp [Wf]; omega) h
  simp [step, hd, sext8_small r hr, tgt]
  omega

theorem step_jmp32 (mode : Mode) (m : Mem) (pc r : Nat) (hr : r < 2 ^ 31)
    (h : Code m pc (enc (.jmp32 r))) : step mode (pc, m) = some (pc + 5 + r, m) := by
  have hd := decode_enc m pc (.jmp32 r) (by simp [Wf]; omega) h
  simp [step, hd, sext32_small r hr, tgt]
  omega

theorem sext_back (P T : Nat) (hP : P ≤ 2 ^ 30 + 16) (hT : T < 2 ^ 30) :
    (P : Int) + sext 32 ((T + 2 ^ 32 - P) % 2 ^ 32) = T := by
  generalize hv : (T + 2 ^ 32 - P) % 2 ^ 32 = v
  have hv1 : v < 2 ^ 32 := by rw [← hv]; exact Nat.mod_lt _ (by omega)
  have hv2 : (P ≤ T ∧ v = T - P) ∨ (T < P ∧ v = T + 2 ^ 32 - P) := by
    by_cases hc : P ≤ T
    · left; refine ⟨hc, ?_⟩
      rw [← hv, show T + 2 ^ 32 - P = (T - P) + 2 ^ 32 by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    · right; refine ⟨by omega, ?_⟩
      rw [← hv]; exact Nat.mod_eq_of_lt (by omega)
  simp only [sext]
  by_cases hc : v < 2 ^ (32 - 1)
  · simp only [hc, ite_true]; omega
  · simp only [hc, ite_false]; omega

theorem sext32_jrel (A T : Nat) (hA : A < 2 ^ 30) (hT : T < 2 ^ 30) :
    (A + 5 : Int) + sext 32 (jrel A T) = T := by
  have := sext_back (A + 5) T (by omega) hT
  simpa [jrel] using this

theorem jrel_lt (A T : Nat) : jrel A T < 2 ^ 32 := Nat.mod_lt _ (by omega)

theorem step_jmp32_to (mode : Mode) (m : Mem) (pc T : Nat) (hA : pc < 2 ^ 30) (hT : T < 2 ^ 30)
    (h : Code m pc (enc (.jmp32 (jrel pc T)))) : step mode (pc, m) = some (T, m) := by
  have hd := decode_enc m pc (.jmp32 (jrel pc T)) (jrel_lt pc T) h
  have := sext32_jrel pc T hA hT
  simp only [step, hd, tgt]
  split
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
    omega
  · exfalso; omega

theorem tgt_ok (pc len : Nat) (d : Int) (T : Nat) (h : (pc + len : Int) + d = T) :
    tgt pc len d = some T := by
  unfold tgt
  have : (0 : Int) ≤ (pc + len : Int) + d := by omega
  have h0 : (0 : Int) ≤ T := by omega
  simp only [this, ite_true, h, Int.toNat_natCast, h0]

theorem ea_fld (mode : Mode) (A len T : Nat) (hA : A < 2 ^ 30) (hlen : len ≤ 10) (hT : T < 2 ^ 30) :
    ea mode A len (fld mode A len T) = some T := by
  cases mode with
  | x86 => rfl
  | x64 =>
    have := sext_back (A + len) T (by omega) hT
    simp only [ea, fld]
    exact tgt_ok _ _ _ _ (by simpa using this)

theorem fld_lt (mode : Mode) (A len T : Nat) (hT : T < 2 ^ 32) : fld mode A len T < 2 ^ 32 := by
  cases mode with
  | x86 => exact hT
  | x64 => exact Nat.mod_lt _ (by omega)

theorem step_movB (mode : Mode) (m : Mem) (pc T i : Nat) (hA : pc < 2 ^ 30) (hT : T < 2 ^ 30)
    (hi : i < 256) (h : Code m pc (enc (.movB (fld mode pc 7 T) i))) :
    step mode (pc, m) = some (pc + 7, wr m T 1 i) := by
  have hd := decode_enc m pc _ (by simp only [Wf]; exact ⟨fld_lt mode pc 7 T (by omega), hi⟩) h
  simp [step, hd, ea_fld mode pc 7 T hA (by omega) hT]

theorem step_movW (mode : Mode) (m : Mem) (pc T i : Nat) (hA : pc < 2 ^ 30) (hT : T < 2 ^ 30)
    (hi : i < 2 ^ 16) (h : Code m pc (enc (.movW (fld mode pc 9 T) i))) :
    step mode (pc, m) = some (pc + 9, wr m T 2 i) := by
  have hd := decode_enc m pc _ (by simp only [Wf]; exact ⟨fld_lt mode pc 9 T (by omega), hi⟩) h
  simp [step, hd, ea_fld mode pc 9 T hA (by omega) hT]

theorem step_movD (mode : Mode) (m : Mem) (pc T i : Nat) (hA : pc < 2 ^ 30) (hT : T < 2 ^ 30)
    (hi : i < 2 ^ 32) (h : Code m pc (enc (.movD (fld mode pc 10 T) i))) :
    step mode (pc, m) = some (pc + 10, wr m T 4 i) := by
  have hd := decode_enc m pc _ (by simp only [Wf]; exact ⟨fld_lt mode pc 10 T (by omega), hi⟩) h
  simp [step, hd, ea_fld mode pc 10 T hA (by omega) hT]

theorem runN_add (mode : Mode) (a b : Nat) (s : Nat × Mem) :
    runN mode (a + b) s = (runN mode a s).bind (runN mode b) := by
  induction a generalizing s with
  | zero => simp [runN]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [runN]
    cases step mode s <;> simp [ih]

theorem runN_one (mode : Mode) (s s' : Nat × Mem) (h : step mode s = some s') :
    runN mode 1 s = some s' := by simp [runN, h]

theorem runN_trans (mode : Mode) {a b : Nat} {s s1 s2 : Nat × Mem}
    (h1 : runN mode a s = some s1) (h2 : runN mode b s1 = some s2) :
    runN mode (a + b) s = some s2 := by
  rw [runN_add, h1]; exact h2

end WriteExecute.X86
