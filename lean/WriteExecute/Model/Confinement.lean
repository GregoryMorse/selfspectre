module
public import WriteExecute.Model.Run

public section

namespace WriteExecute.WE

/-! C04. A run that only ever fetches inside a finite address list `A` can only read words in
`W = A ∪ (A+1) ∪ (A+2)`, so all written values come from the finite list `V = s₀(W)` and all written
addresses from the finite list `T = {a + 3 + r | a ∈ A, r ∈ V}`. Hence the reachable states are a
program counter in `A` plus memory on `T` with values in `U`; memory off `T` never changes. -/

@[expose] def fetchWords (A : List Int) : List Int := A ++ A.map (· + 1) ++ A.map (· + 2)
@[expose] def valueList (A : List Int) (s0 : State) : List Int := (fetchWords A).map s0.mem
@[expose] def targetList (A : List Int) (s0 : State) : List Int :=
  A.flatMap fun a => (valueList A s0).map fun r => a + 3 + r
@[expose] def allValues (A : List Int) (s0 : State) : List Int :=
  valueList A s0 ++ (targetList A s0).map s0.mem

/-- Every state reached by a still-running prefix has its program counter in `A`. -/
@[expose] def Confined (A : List Int) (s0 : State) : Prop :=
  ∀ n s, run n s0 = (.running, s) → s.pc ∈ A

structure Inv (A : List Int) (s0 s : State) : Prop where
  pc : s.pc ∈ A
  fetch : ∀ x ∈ fetchWords A, s.mem x ∈ valueList A s0
  off : ∀ x, x ∉ targetList A s0 → s.mem x = s0.mem x
  tgt : ∀ x ∈ targetList A s0, s.mem x ∈ allValues A s0

theorem mem_fetch0 {A : List Int} {a : Int} (h : a ∈ A) : a ∈ fetchWords A := by
  simp [fetchWords, h]
theorem mem_fetch1 {A : List Int} {a : Int} (h : a ∈ A) : a + 1 ∈ fetchWords A := by
  simp only [fetchWords, List.mem_append, List.mem_map]
  exact Or.inl (Or.inr ⟨a, h, rfl⟩)
theorem mem_fetch2 {A : List Int} {a : Int} (h : a ∈ A) : a + 2 ∈ fetchWords A := by
  simp only [fetchWords, List.mem_append, List.mem_map]
  exact Or.inr ⟨a, h, rfl⟩

theorem inv_init (A : List Int) (s0 : State) (h : s0.pc ∈ A) : Inv A s0 s0 where
  pc := h
  fetch x hx := by simp [valueList]; exact ⟨x, hx, rfl⟩
  off _ _ := rfl
  tgt x hx := by simp [allValues]; exact Or.inr ⟨x, hx, rfl⟩

theorem inv_step {A : List Int} {s0 t s : State} (hinv : Inv A s0 t)
    (hstep : step t = (.running, s)) (hpc : s.pc ∈ A) : Inv A s0 s := by
  by_cases h1 : t.mem t.pc = 1
  · simp [step, decode, h1] at hstep
    subst hstep
    have hr := hinv.fetch _ (mem_fetch1 hinv.pc)
    have hv := hinv.fetch _ (mem_fetch2 hinv.pc)
    have hx : t.pc + 3 + t.mem (t.pc + 1) ∈ targetList A s0 := by
      simp only [targetList, List.mem_flatMap, List.mem_map]
      exact ⟨t.pc, hinv.pc, _, hr, rfl⟩
    have hvU : t.mem (t.pc + 2) ∈ allValues A s0 := by simp [allValues]; exact Or.inl hv
    refine ⟨hpc, ?_, ?_, ?_⟩
    · intro x hx'
      by_cases e : x = t.pc + 3 + t.mem (t.pc + 1)
      · simp [write, e, hv]
      · simp [write, e]; exact hinv.fetch x hx'
    · intro x hx'
      have e : x ≠ t.pc + 3 + t.mem (t.pc + 1) := fun e => hx' (e ▸ hx)
      simp [write, e]; exact hinv.off x hx'
    · intro x hx'
      by_cases e : x = t.pc + 3 + t.mem (t.pc + 1)
      · simp [write, e, hvU]
      · simp [write, e]; exact hinv.tgt x hx'
  · by_cases h2 : t.mem t.pc = 2
    · simp [step, decode, h2] at hstep
      subst hstep
      exact ⟨hpc, hinv.fetch, hinv.off, hinv.tgt⟩
    · by_cases h3 : t.mem t.pc = 3 <;> simp [step, decode, h1, h2, h3] at hstep

/-- C04: a confined run keeps the invariant, so its memory off the finite target list never changes
and its fetched/stored values stay in finite lists. -/
theorem confinement {A : List Int} {s0 : State} (hc : Confined A s0) :
    ∀ n s, run n s0 = (.running, s) → Inv A s0 s := by
  intro n
  induction n with
  | zero =>
    intro s h
    simp [run] at h
    subst h
    exact inv_init A _ (hc 0 _ rfl)
  | succ n ih =>
    intro s h
    rw [run_succ_right] at h
    cases hr : run n s0 with
    | mk st t =>
      cases st <;> simp [hr] at h
      exact inv_step (ih t hr) h (hc _ _ (by rw [run_succ_right, hr]; simpa using h))

end WriteExecute.WE
