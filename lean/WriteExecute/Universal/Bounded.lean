module
public import WriteExecute.Universal.Step

public section

namespace WriteExecute.Universal

open WriteExecute.TM

theorem div_cell {A Q : Nat} (c : Int) (j : Nat) (hj : j < cellSize A Q) :
    (c * (cellSize A Q : Int) + (j : Int)) / (cellSize A Q : Int) = c := by
  have hS : (0 : Int) < (cellSize A Q : Int) := by omega
  have hj' : (j : Int) < (cellSize A Q : Int) := by omega
  rw [Int.add_comm, Int.add_mul_ediv_right _ _ (Int.ne_of_gt hS),
    Int.ediv_eq_zero_of_lt (by omega) hj']
  omega

theorem patch_mask (A Q : Nat) (b : Int) (sym : Nat) (m1 : Int → Int) (N : Nat)
    (hP : ∀ j : Nat, j < Q → 0 ≤ (b + 2 * (j : Int) + 1) / (cellSize A Q : Int) ∧
      (b + 2 * (j : Int) + 1) / (cellSize A Q : Int) < (N : Int)) :
    ∀ i, i ≤ Q → ∀ x : Int,
      patch A Q b sym i (fun a => if 0 ≤ a / (cellSize A Q : Int) ∧ a / (cellSize A Q : Int) < (N : Int)
          then m1 a else 0) x =
        if 0 ≤ x / (cellSize A Q : Int) ∧ x / (cellSize A Q : Int) < (N : Int)
          then patch A Q b sym i m1 x else 0 := by
  intro i
  induction i with
  | zero => intro _ x; rfl
  | succ i ih =>
    intro hi x
    by_cases h : x = b + 2 * (i : Int) + 1
    · subst h
      have := hP i (by omega)
      simp [patch, write, this]
    · have := ih (by omega) x
      simp [patch, write, h, this]

theorem bounded_hL {A Q : Nat} (M : Machine A Q) (N : Nat) (tape : Int → Fin A) (c : Int)
    (hc : 0 ≤ c ∧ c < (N : Int)) :
    ∀ j : Nat, j < cellSize A Q →
      bounded M N tape (c * (cellSize A Q : Int) + (j : Int)) = cellWord M (tape c).val j := by
  intro j hj
  unfold bounded
  rw [div_cell c j hj, if_pos hc]
  exact layout_at M tape c j hj

theorem bounded_step_some {A Q : Nat} (M : Machine A Q) (N : Nat) (tape : Int → Fin A) (c : Int)
    (hc : 0 ≤ c ∧ c < (N : Int)) (q : Fin Q) (nx : Fin A) (right : Bool) (q' : Fin Q)
    (ht : M.transition q (tape c) = some (nx, right, q')) :
    WE.run (Q + 2) ⟨c * (cellSize A Q : Int) + 2 * (q.val : Int), bounded M N tape⟩ =
      (.running, ⟨(if right then c + 1 else c - 1) * (cellSize A Q : Int) + 2 * (q'.val : Int),
        bounded M N (write tape c nx)⟩) := by
  rw [cell_step_some_gen M tape c (bounded M N tape) (bounded_hL M N tape c hc) q nx right q' ht]
  have hP : ∀ j : Nat, j < Q →
      0 ≤ (c * (cellSize A Q : Int) + 2 * (j : Int) + 1) / (cellSize A Q : Int) ∧
      (c * (cellSize A Q : Int) + 2 * (j : Int) + 1) / (cellSize A Q : Int) < (N : Int) := by
    intro j hj
    have hS : 2 * j + 1 < cellSize A Q := by unfold cellSize; omega
    have e := div_cell (A := A) (Q := Q) c (2 * j + 1) hS
    push_cast at e
    rw [show c * (cellSize A Q : Int) + 2 * (j : Int) + 1 = c * (cellSize A Q : Int) + (2 * (j : Int) + 1) from by omega, e]
    exact hc
  have hm : patch A Q (c * (cellSize A Q : Int)) nx.val Q (bounded M N tape)
      = bounded M N (write tape c nx) := by
    funext x
    unfold bounded
    rw [patch_mask A Q _ nx.val (layout M tape) N hP Q (Nat.le_refl _) x,
      patch_eq_layout_write]
  rw [hm]

theorem bounded_step_none {A Q : Nat} (M : Machine A Q) (N : Nat) (tape : Int → Fin A) (c : Int)
    (hc : 0 ≤ c ∧ c < (N : Int)) (q : Fin Q) (ht : M.transition q (tape c) = none) :
    ∃ t, WE.run 2 ⟨c * (cellSize A Q : Int) + 2 * (q.val : Int), bounded M N tape⟩ =
      (.halted, t) :=
  ⟨_, cell_step_none_gen M tape c (bounded M N tape) (bounded_hL M N tape c hc) q ht⟩

/-- The guard: outside the image the fetched opcode is `0`, so the run faults. -/
theorem bounded_guard {A Q : Nat} (M : Machine A Q) (N : Nat) (tape : Int → Fin A) (c' : Int)
    (q' : Fin Q) (hout : ¬ (0 ≤ c' ∧ c' < (N : Int))) :
    ∃ t, WE.run 1 ⟨c' * (cellSize A Q : Int) + 2 * (q'.val : Int), bounded M N tape⟩ =
      (.faulted, t) := by
  have hS : 2 * q'.val < cellSize A Q := by
    have := q'.2; unfold cellSize; omega
  have e := div_cell (A := A) (Q := Q) c' (2 * q'.val) hS
  push_cast at e
  have h0 : bounded M N tape (c' * (cellSize A Q : Int) + 2 * (q'.val : Int)) = 0 := by
    unfold bounded
    rw [e, if_neg hout]
  rw [WE.run_one]
  exact ⟨⟨c' * (cellSize A Q : Int) + 2 * (q'.val : Int), bounded M N tape⟩, by simp [WE.step, WE.decode, h0]⟩

theorem bounded_encode_step {A Q : Nat} (M : Machine A Q) (N : Nat) (cfg cfg' : Configuration A Q)
    (hc : 0 ≤ cfg.head ∧ cfg.head < (N : Int)) (h : TM.step M cfg = some cfg') :
    WE.run (Q + 2) (encodeB M N cfg) = (.running, encodeB M N cfg') := by
  unfold TM.step at h
  cases hT : M.transition cfg.state (cfg.tape cfg.head) with
  | none => simp [hT] at h
  | some r =>
    obtain ⟨nx, right, q'⟩ := r
    simp [hT] at h
    subst h
    exact bounded_step_some M N cfg.tape cfg.head hc cfg.state nx right q' hT

/-- C03, exactness: while every configuration visited lies inside the image, `n` Turing steps are
simulated exactly by `n (Q + 2)` Write-Execute steps. -/
theorem bounded_simulate {A Q : Nat} (M : Machine A Q) (N : Nat) :
    ∀ (n : Nat) (cfg cfg' : Configuration A Q), TM.run M n cfg = some cfg' →
      (∀ k, k < n → ∀ c1, TM.run M k cfg = some c1 → 0 ≤ c1.head ∧ c1.head < (N : Int)) →
      WE.run (n * (Q + 2)) (encodeB M N cfg) = (.running, encodeB M N cfg') := by
  intro n
  induction n with
  | zero =>
    intro cfg cfg' h _
    simp [TM.run] at h
    subst h
    simp [WE.run]
  | succ n ih =>
    intro cfg cfg' h hin
    simp only [TM.run] at h
    cases hs : TM.step M cfg with
    | none => simp [hs] at h
    | some c1 =>
      simp [hs] at h
      have h0 := hin 0 (by omega) cfg (by simp [TM.run])
      have e : (n + 1) * (Q + 2) = (Q + 2) + n * (Q + 2) := by
        rw [Nat.succ_mul, Nat.add_comm]
      rw [e, WE.run_add, bounded_encode_step M N cfg c1 h0 hs]
      exact ih c1 cfg' h (fun k hk c2 hc2 => hin (k + 1) (by omega) c2 (by simp [TM.run, hs, hc2]))

/-- C03, halting inside the image is faithful. -/
theorem bounded_halts {A Q : Nat} (M : Machine A Q) (N : Nat) (cfg fin : Configuration A Q) (n : Nat)
    (hn : TM.run M n cfg = some fin) (hs : TM.step M fin = none)
    (hin : ∀ k, k < n → ∀ c1, TM.run M k cfg = some c1 → 0 ≤ c1.head ∧ c1.head < (N : Int))
    (hfin : 0 ≤ fin.head ∧ fin.head < (N : Int)) : WE.Halts (encodeB M N cfg) := by
  have hT : M.transition fin.state (fin.tape fin.head) = none := by
    unfold TM.step at hs
    cases hT : M.transition fin.state (fin.tape fin.head) with
    | none => rfl
    | some r => simp [hT] at hs
  obtain ⟨t, ht⟩ := bounded_step_none M N fin.tape fin.head hfin fin.state hT
  refine ⟨n * (Q + 2) + 2, t, ?_⟩
  rw [WE.run_add, bounded_simulate M N n cfg fin hn hin]
  exact ht

/-- C03, the guard: the first step that leaves the image faults. -/
theorem bounded_faults {A Q : Nat} (M : Machine A Q) (N : Nat) (cfg fin fin' : Configuration A Q)
    (n : Nat) (hn : TM.run M n cfg = some fin) (hs : TM.step M fin = some fin')
    (hin : ∀ k, k < n → ∀ c1, TM.run M k cfg = some c1 → 0 ≤ c1.head ∧ c1.head < (N : Int))
    (hfin : 0 ≤ fin.head ∧ fin.head < (N : Int)) (hout : ¬ (0 ≤ fin'.head ∧ fin'.head < (N : Int))) :
    WE.Faults (encodeB M N cfg) := by
  obtain ⟨t, ht⟩ := bounded_guard M N fin'.tape fin'.head fin'.state hout
  refine ⟨n * (Q + 2) + (Q + 2) + 1, t, ?_⟩
  have r1 : WE.run (n * (Q + 2) + (Q + 2)) (encodeB M N cfg) = (.running, encodeB M N fin') := by
    rw [WE.run_add, bounded_simulate M N n cfg fin hn hin]
    exact bounded_encode_step M N fin fin' hfin hs
  rw [WE.run_add, r1]
  exact ht

end WriteExecute.Universal
