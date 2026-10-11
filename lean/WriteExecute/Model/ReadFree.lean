module
public import WriteExecute.Spec.Machine

public section

namespace WriteExecute.WE

/-- The only memory the machine consults: the three words at the program counter. -/
@[expose] def window (s : State) : Int × Int × Int × Int :=
  (s.pc, s.mem s.pc, s.mem (s.pc + 1), s.mem (s.pc + 2))

/-- Apply a one-store effect to a state. -/
@[expose] def apply (s : State) (e : Status × Int × Option (Int × Int)) : Status × State :=
  (e.1, ⟨e.2.1, match e.2.2 with
    | none => s.mem
    | some (a, v) => write s.mem a v⟩)

/-- The effect determined by a state's fetch window. -/
@[expose] def effectOf (s : State) : Status × Int × Option (Int × Int) :=
  effect s.pc (s.mem s.pc) (s.mem (s.pc + 1)) (s.mem (s.pc + 2))

/-- C01 (read-freedom): one step is a function of the fetch window alone, and its memory effect is
at most one store (a jump stores nothing and moves the program counter). There is no data read,
register or stack. -/
theorem step_eq_effect (s : State) : step s = apply s (effectOf s) := by
  unfold step decode effectOf effect apply
  by_cases h1 : s.mem s.pc = 1
  · simp [h1]
  · by_cases h2 : s.mem s.pc = 2
    · simp [h2]
    · by_cases h3 : s.mem s.pc = 3 <;> simp [h1, h2, h3]

/-- Two states with the same fetch window take the same status, next program counter and store. -/
theorem effect_congr (s t : State) (h : window s = window t) : effectOf s = effectOf t := by
  simp only [window, Prod.mk.injEq] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  unfold effectOf
  rw [← h1, ← h2, ← h3, ← h0]

/-- A mov-store effect writes a value taken from the window to an address computed from it. -/
theorem store_from_window (pc a b c : Int) (x v : Int)
    (h : (effect pc a b c).2.2 = some (x, v)) : a = 1 ∧ x = pc + 3 + b ∧ v = c := by
  unfold effect at h
  by_cases h1 : a = 1
  · simp [h1] at h; exact ⟨h1, h.1.symm, h.2.symm⟩
  · by_cases h2 : a = 2
    · simp [h2] at h
    · by_cases h3 : a = 3 <;> simp [h1, h2, h3] at h

end WriteExecute.WE
