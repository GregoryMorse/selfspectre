module
public import WriteExecute.Spec.Machine

public section

namespace WriteExecute.WE

theorem run_one (t : State) : run 1 t = step t := by
  unfold run
  cases h : step t with
  | mk st u => cases st <;> simp [run]

/-- A stopped run stays stopped. -/
theorem run_stop (a b : Nat) (s : State) (h : (run a s).1 ≠ .running) : run (a + b) s = run a s := by
  induction a generalizing s with
  | zero => simp [run] at h
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [run]
    cases hs : step s with
    | mk st t =>
      cases st
      · simp only [hs, run] at h ⊢; exact ih t h
      · rfl
      · rfl

theorem run_add (a b : Nat) (s : State) :
    run (a + b) s = match run a s with
      | (.running, t) => run b t
      | r => r := by
  induction a generalizing s with
  | zero => simp [run]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [run]
    cases hs : step s with
    | mk st t =>
      cases st
      · simp [ih]
      · rfl
      · rfl

theorem run_succ_right (n : Nat) (s : State) :
    run (n + 1) s = match run n s with
      | (.running, t) => step t
      | r => r := by
  rw [run_add]
  cases h : run n s with
  | mk st t => cases st <;> simp [run_one]

theorem halts_not_faults (s : State) : Halts s → ¬ Faults s := by
  rintro ⟨n, t, hn⟩ ⟨m, u, hm⟩
  by_cases le : n ≤ m
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le le
    have := run_stop n k s (by simp [hn])
    rw [this, hn] at hm
    simp at hm
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_le le)
    have := run_stop m k s (by simp [hm])
    rw [← hk, hn, hm] at this
    simp at this

theorem halts_not_diverges (s : State) : Halts s → ¬ Diverges s := by
  rintro ⟨n, t, hn⟩ hd
  have := hd n
  simp [hn] at this

theorem faults_not_diverges (s : State) : Faults s → ¬ Diverges s := by
  rintro ⟨n, t, hn⟩ hd
  have := hd n
  simp [hn] at this

/-- Every run halts, faults or diverges. -/
theorem trichotomy (s : State) : Halts s ∨ Faults s ∨ Diverges s := by
  by_cases hd : Diverges s
  · exact Or.inr (Or.inr hd)
  · obtain ⟨n, hn⟩ := Classical.not_forall.mp hd
    cases h : run n s with
    | mk st t =>
      cases st
      · simp [h] at hn
      · exact Or.inl ⟨n, t, h⟩
      · exact Or.inr (Or.inl ⟨n, t, h⟩)

end WriteExecute.WE
