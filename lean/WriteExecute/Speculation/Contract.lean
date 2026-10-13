module
public import WriteExecute.Spec.Paper
public import WriteExecute.Model.Run
public import WriteExecute.Universal.Unbounded
public import WriteExecute.Spectre.Select
public import WriteExecute.Spectre.Mix
public import WriteExecute.Arith.Tables

public section

namespace WriteExecute.Speculation

open WriteExecute

theorem tstep_np (t : TState) (h : t.s.mem t.s.pc ≠ 4) :
    tstep t = ((WE.step t.s).1, ⟨(WE.step t.s).2, t.touched⟩) := by
  simp [tstep, h]

theorem tstep_probe (t : TState) (h : t.s.mem t.s.pc = 4) :
    tstep t = (.running, ⟨⟨t.s.pc + 2, t.s.mem⟩, (t.s.mem (t.s.pc + 2 + t.s.mem (t.s.pc + 1)) % 256) :: t.touched⟩) := by
  simp [tstep, h]

/-- A running Write-Execute step fetches opcode 1 or 2, never the probe opcode. -/
theorem step_running_ne4 (s u : WE.State) (h : WE.step s = (.running, u)) : s.mem s.pc ≠ 4 := by
  intro h4
  simp [WE.step, WE.decode, h4] at h

/-- A transient run that stays running without a probe is the ideal Write-Execute run. -/
theorem trun_run : ∀ (n : Nat) (s u : WE.State) (l : List Int),
    WE.run n s = (.running, u) → trun n ⟨s, l⟩ = (.running, ⟨u, l⟩)
  | 0, s, u, l, h => by
    simp [WE.run] at h
    subst h
    simp [trun]
  | n + 1, s, u, l, h => by
    cases hs : WE.step s with
    | mk st v =>
      cases st
      · have h4 := step_running_ne4 s v hs
        have e : tstep ⟨s, l⟩ = (.running, ⟨v, l⟩) := by
          rw [tstep_np _ h4]; simp [hs]
        have hr : WE.run (n + 1) s = WE.run n v := by simp [WE.run, hs]
        rw [hr] at h
        simp only [trun, e]
        exact trun_run n v u l h
      · simp [WE.run, hs] at h
      · simp [WE.run, hs] at h

theorem run_prefix (k W : Nat) (s u : WE.State) (h : WE.run k s = (.running, u)) (hW : W ≤ k) :
    ∃ v, WE.run W s = (.running, v) := by
  have e := WE.run_add W (k - W) s
  rw [Nat.add_sub_cancel' hW, h] at e
  cases hr : WE.run W s with
  | mk st v =>
    cases st
    · exact ⟨v, rfl⟩
    · rw [hr] at e; simp at e
    · rw [hr] at e; simp at e

theorem trun_add (a b : Nat) (t : TState) :
    trun (a + b) t = match trun a t with
      | (.running, u) => trun b u
      | r => r := by
  induction a generalizing t with
  | zero => simp [trun]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [trun]
    cases hs : tstep t with
    | mk st u =>
      cases st
      · simp [ih]
      · rfl
      · rfl

theorem tstep_touched (t : TState) : ∃ l, (tstep t).2.touched = l ++ t.touched := by
  unfold tstep
  split
  · exact ⟨[_], rfl⟩
  · exact ⟨[], rfl⟩

theorem trun_touched : ∀ (n : Nat) (t : TState), ∃ l, (trun n t).2.touched = l ++ t.touched
  | 0, t => ⟨[], by simp [trun]⟩
  | n + 1, t => by
    obtain ⟨l1, h1⟩ := tstep_touched t
    simp only [trun]
    cases hs : tstep t with
    | mk st u =>
      rw [hs] at h1
      cases st
      · obtain ⟨l2, h2⟩ := trun_touched n u
        exact ⟨l2 ++ l1, by simp only [] at h1 ⊢; rw [h2, h1, List.append_assoc]⟩
      · exact ⟨l1, h1⟩
      · exact ⟨l1, h1⟩

theorem branch_mono (W d n : Nat) (t : TState) :
    ∃ l, (branch (W + d) true false n t).touched = l ++ (branch W true false n t).touched := by
  simp only [branch]
  simp only [Bool.false_eq_true, ite_false, ite_true]
  have hle : min W n ≤ min (W + d) n := by omega
  have e : min (W + d) n = min W n + (min (W + d) n - min W n) := by omega
  rw [e, trun_add]
  cases hr : trun (min W n) t with
  | mk st u =>
    cases st
    · obtain ⟨l, h⟩ := trun_touched (min (W + d) n - min W n) u
      exact ⟨l, by simpa using h⟩
    · exact ⟨[], by simp⟩
    · exact ⟨[], by simp⟩

theorem branch_one (W : Nat) (hW : 1 ≤ W) (t : TState) (a : Int)
    (h4 : t.s.mem t.s.pc = 4) (hr : t.s.mem (t.s.pc + 1) = a - (t.s.pc + 2)) :
    branch W true false 1 t = ⟨t.s, (t.s.mem a % 256) :: t.touched⟩ := by
  have hm : min W 1 = 1 := by omega
  have ha : t.s.pc + 2 + t.s.mem (t.s.pc + 1) = a := by rw [hr]; omega
  simp [branch, hm, trun, tstep_probe t h4, ha]

theorem hits_c0 : ∀ q : Nat, q < 32 → probeHits [((32 * 0 + q : Nat) : Int)] = [32 * 0 + q] :=
  Arith.all1 (n := 32) (p := fun q => probeHits [((32 * 0 + q : Nat) : Int)] = [32 * 0 + q]) (by decide +kernel)

theorem hits_c1 : ∀ q : Nat, q < 32 → probeHits [((32 * 1 + q : Nat) : Int)] = [32 * 1 + q] :=
  Arith.all1 (n := 32) (p := fun q => probeHits [((32 * 1 + q : Nat) : Int)] = [32 * 1 + q]) (by decide +kernel)

theorem hits_c2 : ∀ q : Nat, q < 32 → probeHits [((32 * 2 + q : Nat) : Int)] = [32 * 2 + q] :=
  Arith.all1 (n := 32) (p := fun q => probeHits [((32 * 2 + q : Nat) : Int)] = [32 * 2 + q]) (by decide +kernel)

theorem hits_c3 : ∀ q : Nat, q < 32 → probeHits [((32 * 3 + q : Nat) : Int)] = [32 * 3 + q] :=
  Arith.all1 (n := 32) (p := fun q => probeHits [((32 * 3 + q : Nat) : Int)] = [32 * 3 + q]) (by decide +kernel)

theorem hits_c4 : ∀ q : Nat, q < 32 → probeHits [((32 * 4 + q : Nat) : Int)] = [32 * 4 + q] :=
  Arith.all1 (n := 32) (p := fun q => probeHits [((32 * 4 + q : Nat) : Int)] = [32 * 4 + q]) (by decide +kernel)

theorem hits_c5 : ∀ q : Nat, q < 32 → probeHits [((32 * 5 + q : Nat) : Int)] = [32 * 5 + q] :=
  Arith.all1 (n := 32) (p := fun q => probeHits [((32 * 5 + q : Nat) : Int)] = [32 * 5 + q]) (by decide +kernel)

theorem hits_c6 : ∀ q : Nat, q < 32 → probeHits [((32 * 6 + q : Nat) : Int)] = [32 * 6 + q] :=
  Arith.all1 (n := 32) (p := fun q => probeHits [((32 * 6 + q : Nat) : Int)] = [32 * 6 + q]) (by decide +kernel)

theorem hits_c7 : ∀ q : Nat, q < 32 → probeHits [((32 * 7 + q : Nat) : Int)] = [32 * 7 + q] :=
  Arith.all1 (n := 32) (p := fun q => probeHits [((32 * 7 + q : Nat) : Int)] = [32 * 7 + q]) (by decide +kernel)

theorem probe_hits : ∀ p : Nat, p < 256 → probeHits [(p : Int)] = [p] := by
  intro p hp
  obtain ⟨c, q, hq, rfl⟩ : ∃ c q, q < 32 ∧ p = 32 * c + q := ⟨p / 32, p % 32, by omega, by omega⟩
  have hc : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hits_c0 q hq
  · exact hits_c1 q hq
  · exact hits_c2 q hq
  · exact hits_c3 q hq
  · exact hits_c4 q hq
  · exact hits_c5 q hq
  · exact hits_c6 q hq
  · exact hits_c7 q hq

theorem hits_nil : probeHits [] = [] := by decide +kernel

/-- From a cleared cache one probed page is exactly the reload hit. -/
theorem hits_single (x : Int) : probeHits ([x % 256]) = [(x % 256).toNat] := by
  have h0 : 0 ≤ x % 256 := by omega
  have h1 : x % 256 < 256 := by omega
  have e : x % 256 = ((x % 256).toNat : Int) := by omega
  have := probe_hits (x % 256).toNat (by omega)
  rw [← e] at this
  exact this

theorem leak_after (k : Nat) (s u : WE.State) (l : List Int) (h : WE.run k s = (.running, u))
    (h4 : u.mem u.pc = 4) :
    (∀ W, W ≤ k → (branch W true false (k + 1) ⟨s, l⟩).touched = l) ∧
    (∀ W, k + 1 ≤ W → (branch W true false (k + 1) ⟨s, l⟩).touched =
      (u.mem (u.pc + 2 + u.mem (u.pc + 1)) % 256) :: l) := by
  constructor
  · intro W hW
    have hm : min W (k + 1) = W := by omega
    obtain ⟨v, hv⟩ := run_prefix k W s u h hW
    simp [branch, hm, trun_run W s v l hv]
  · intro W hW
    have hm : min W (k + 1) = k + 1 := by omega
    have e := trun_add k 1 ⟨s, l⟩
    rw [trun_run k s u l h] at e
    simp [branch, hm, e, trun, tstep_probe ⟨u, l⟩ h4]

theorem leak_after_cleared (k : Nat) (s u : WE.State) (h : WE.run k s = (.running, u))
    (h4 : u.mem u.pc = 4) :
    (∀ W, W ≤ k → probeHits (branch W true false (k + 1) ⟨s, []⟩).touched = []) ∧
    (∀ W, k + 1 ≤ W → probeHits (branch W true false (k + 1) ⟨s, []⟩).touched =
      [(u.mem (u.pc + 2 + u.mem (u.pc + 1)) % 256).toNat]) := by
  have L := leak_after k s u [] h h4
  exact ⟨fun W hW => by rw [L.1 W hW]; exact hits_nil,
    fun W hW => by rw [L.2 W hW]; exact hits_single _⟩

theorem hidden (n : Nat) (s u : WE.State) (l : List Int) (h : WE.run n s = (.running, u)) :
    trun n ⟨s, l⟩ = (.running, ⟨u, l⟩) ∧
    ∀ W, n ≤ W → branch W true false n ⟨s, l⟩ = ⟨s, l⟩ := by
  refine ⟨trun_run n s u l h, fun W hW => ?_⟩
  have hm : min W n = n := by omega
  simp [branch, hm, trun_run n s u l h]

theorem ctr_foldl (m s : Nat) :
    (List.replicate (m + 1) true).foldl ctrUpdate s = min 3 (s + m + 1) := by
  induction m generalizing s with
  | zero => simp [ctrUpdate]
  | succ m ih =>
    rw [List.replicate_succ, List.foldl_cons, ih]
    simp [ctrUpdate]
    omega

theorem counter2_trains : counter2.Trains 3 := by
  change ∀ (s : Nat) (m : Nat), 3 ≤ m → decide (2 ≤ List.foldl ctrUpdate s (List.replicate m true)) = true
  intro s m hm
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have h : (List.replicate (m' + 1) true).foldl ctrUpdate s = min 3 (s + m' + 1) := ctr_foldl m' s
  show decide (2 ≤ (List.replicate (m' + 1) true).foldl ctrUpdate s) = true
  rw [h]
  simp
  omega

theorem mistrain (P : Predictor) (k : Nat) (hP : P.Trains k) (hk : k ≤ 5) (s0 : P.S) (j : Nat)
    (h29 : j ≤ 29) (hj : j % 6 = 0) :
    P.predict (P.after s0 (historyBefore j)) = true ∧ guardAt j = false := by
  have hl : historyBefore j =
      (List.range (24 - j)).map (fun i => guardAt (29 - i)) ++ List.replicate 5 true := by
    unfold historyBefore
    have e : 29 - j = (24 - j) + 5 := by omega
    rw [e, List.range_add, List.map_append]
    congr 1
    apply List.eq_replicate_iff.2
    refine ⟨by simp, ?_⟩
    intro b hb
    simp only [List.mem_map, List.mem_range] at hb
    obtain ⟨x, ⟨m, hm, rfl⟩, rfl⟩ := hb
    simp [guardAt]
    omega
  refine ⟨?_, by simp [guardAt, hj]⟩
  rw [hl]
  have := hP (P.after s0 ((List.range (24 - j)).map (fun i => guardAt (29 - i)))) 5 hk
  simpa [Predictor.after, List.foldl_append] using this

theorem select_guard_32 (j : Nat) (t m : BitVec 32) (size : Nat) (ht : t.toNat < size)
    (hm : size ≤ m.toNat) :
    (Spectre.selectIdx 32 j t m).toNat < size ↔ guardAt j = true := by
  rw [Spectre.select_32]
  by_cases h : j % 6 = 0 <;> simp [guardAt, h] <;> omega

theorem select_guard_64 (j : Nat) (t m : BitVec 64) (size : Nat) (ht : t.toNat < size)
    (hm : size ≤ m.toNat) :
    (Spectre.selectIdx 64 j t m).toNat < size ↔ guardAt j = true := by
  rw [Spectre.select_64]
  by_cases h : j % 6 = 0 <;> simp [guardAt, h] <;> omega

end WriteExecute.Speculation
