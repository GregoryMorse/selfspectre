module
public import WriteExecute.Universal.Step

public section

namespace WriteExecute.Universal

open WriteExecute.TM

/-- One Turing step is `Q + 2` Write-Execute steps. -/
theorem encode_step_some {A Q : Nat} (M : Machine A Q) (cfg cfg' : Configuration A Q)
    (h : TM.step M cfg = some cfg') : WE.run (Q + 2) (encode M cfg) = (.running, encode M cfg') := by
  unfold TM.step at h
  cases hT : M.transition cfg.state (cfg.tape cfg.head) with
  | none => simp [hT] at h
  | some r =>
    obtain ⟨nx, right, q'⟩ := r
    simp [hT] at h
    subst h
    exact cell_step_some M cfg.tape cfg.head cfg.state nx right q' hT

theorem encode_step_none {A Q : Nat} (M : Machine A Q) (cfg : Configuration A Q)
    (h : TM.step M cfg = none) : ∃ t, WE.run 2 (encode M cfg) = (.halted, t) := by
  have hT : M.transition cfg.state (cfg.tape cfg.head) = none := by
    unfold TM.step at h
    cases hT : M.transition cfg.state (cfg.tape cfg.head) with
    | none => rfl
    | some r => simp [hT] at h
  exact ⟨_, cell_step_none M cfg.tape cfg.head cfg.state hT⟩

/-- Simulation of `n` Turing steps by `n (Q + 2)` Write-Execute steps. -/
theorem simulate {A Q : Nat} (M : Machine A Q) :
    ∀ (n : Nat) (cfg cfg' : Configuration A Q), TM.run M n cfg = some cfg' →
      WE.run (n * (Q + 2)) (encode M cfg) = (.running, encode M cfg') := by
  intro n
  induction n with
  | zero =>
    intro cfg cfg' h
    simp [TM.run] at h
    subst h
    simp [WE.run]
  | succ n ih =>
    intro cfg cfg' h
    simp only [TM.run] at h
    cases hs : TM.step M cfg with
    | none => simp [hs] at h
    | some c1 =>
      simp [hs] at h
      have e : (n + 1) * (Q + 2) = (Q + 2) + n * (Q + 2) := by
        rw [Nat.succ_mul, Nat.add_comm]
      rw [e, WE.run_add, encode_step_some M cfg c1 hs]
      exact ih c1 cfg' h

theorem halts_to_halts {A Q : Nat} (M : Machine A Q) (cfg : Configuration A Q)
    (h : TM.Halts M cfg) : WE.Halts (encode M cfg) := by
  obtain ⟨n, fin, hn, hs⟩ := h
  obtain ⟨t, ht⟩ := encode_step_none M fin hs
  refine ⟨n * (Q + 2) + 2, t, ?_⟩
  rw [WE.run_add, simulate M n cfg fin hn]
  exact ht

theorem diverges_to_diverges {A Q : Nat} (M : Machine A Q) (cfg : Configuration A Q)
    (h : TM.Diverges M cfg) : WE.Diverges (encode M cfg) := by
  intro n
  obtain ⟨fin, hf⟩ := h n
  have hr := simulate M n cfg fin hf
  refine Classical.byContradiction fun hne => ?_
  have hle : n ≤ n * (Q + 2) := Nat.le_mul_of_pos_right n (by omega)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  have := WE.run_stop n k (encode M cfg) hne
  rw [← hk, hr] at this
  exact hne (by rw [← this])

/-- C02: the encoded machine halts exactly when the Turing machine does. -/
theorem halts_iff {A Q : Nat} (M : Machine A Q) (cfg : Configuration A Q) :
    WE.Halts (encode M cfg) ↔ TM.Halts M cfg := by
  constructor
  · intro h
    refine Classical.byContradiction fun hn => ?_
    exact WE.halts_not_diverges _ h (diverges_to_diverges M cfg
      ((TM.diverges_iff_not_halts M cfg).mpr hn))
  · exact halts_to_halts M cfg

theorem diverges_iff {A Q : Nat} (M : Machine A Q) (cfg : Configuration A Q) :
    WE.Diverges (encode M cfg) ↔ TM.Diverges M cfg := by
  constructor
  · intro h
    rw [TM.diverges_iff_not_halts]
    intro hh
    exact WE.halts_not_diverges _ (halts_to_halts M cfg hh) h
  · exact diverges_to_diverges M cfg

/-- The encoding never reaches an undecodable opcode. -/
theorem never_faults {A Q : Nat} (M : Machine A Q) (cfg : Configuration A Q) :
    ¬ WE.Faults (encode M cfg) := by
  by_cases h : TM.Halts M cfg
  · exact WE.halts_not_faults _ (halts_to_halts M cfg h)
  · intro hf
    exact WE.faults_not_diverges _ hf (diverges_to_diverges M cfg
      ((TM.diverges_iff_not_halts M cfg).mpr h))

/-- C02 for a finite input: the unbounded blank-cell template run on `input`. -/
theorem universal_halts_iff {A Q : Nat} (M : Machine A Q) (input : List (Fin A)) :
    WE.Halts (initial M input) ↔ TM.Halts M (initialConfiguration M input) :=
  halts_iff M _

theorem universal_diverges_iff {A Q : Nat} (M : Machine A Q) (input : List (Fin A)) :
    WE.Diverges (initial M input) ↔ TM.Diverges M (initialConfiguration M input) :=
  diverges_iff M _

end WriteExecute.Universal
