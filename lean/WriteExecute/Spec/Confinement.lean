module
public import WriteExecute.Spec.Machine

public section

namespace WriteExecute.WE

/-! C04 vocabulary. A run that only ever fetches inside a finite address list `A` can only read words
in `W = A ∪ (A+1) ∪ (A+2)`, so all written values come from the finite list `V = s₀(W)` and all written
addresses from the finite list `T = {a + 3 + r | a ∈ A, r ∈ V}`. -/

@[expose] def fetchWords (A : List Int) : List Int := A ++ A.map (· + 1) ++ A.map (· + 2)
@[expose] def valueList (A : List Int) (s0 : State) : List Int := (fetchWords A).map s0.mem
@[expose] def targetList (A : List Int) (s0 : State) : List Int :=
  A.flatMap fun a => (valueList A s0).map fun r => a + 3 + r
@[expose] def allValues (A : List Int) (s0 : State) : List Int :=
  valueList A s0 ++ (targetList A s0).map s0.mem

/-- Every state reached by a still-running prefix has its program counter in `A`. -/
@[expose] def Confined (A : List Int) (s0 : State) : Prop :=
  ∀ n s, run n s0 = (.running, s) → s.pc ∈ A

end WriteExecute.WE
