module
public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import WriteExecute.Base.Turing

public section

namespace WriteExecute.MathlibTM0

variable {alphabet states : Nat} [Inhabited (Fin alphabet)] [Inhabited (Fin states)]

@[expose] def original (state : Fin states) : Fin (2 * states) := ⟨state.val, by have := state.isLt; omega⟩
@[expose] def restoring (state : Fin states) : Fin (2 * states) := ⟨states + state.val, by have := state.isLt; omega⟩

@[expose] def direction : Turing.Dir → Bool
  | .left => false
  | .right => true

@[expose] def entry (symbol : Fin alphabet) (next : Fin states) : Turing.TM0.Stmt (Fin alphabet) →
    Fin alphabet × Bool × Fin (2 * states)
  | .move dir => (symbol, direction dir, original next)
  | .write value => (value, true, restoring next)

/-- Compile the actual Mathlib TM0 machine to the finite write/move model.
A write moves right temporarily; the restoring phase rewrites the neighbor
with its current value and moves left. There are exactly twice as many labels. -/
@[expose] def compile (machine : Turing.TM0.Machine (Fin alphabet) (Fin states)) : TM.Machine alphabet (2 * states) :=
  { blank := default
    start := original default
    transition := fun state symbol =>
      if h : state.val < states then
        (machine ⟨state.val, h⟩ symbol).map fun result => entry symbol result.1 result.2
      else some (symbol, false, original ⟨state.val - states, by have := state.isLt; omega⟩) }

theorem original_transition (machine : Turing.TM0.Machine (Fin alphabet) (Fin states)) (state : Fin states)
    (symbol : Fin alphabet) : (compile machine).transition (original state) symbol =
      (machine state symbol).map (fun result => entry symbol result.1 result.2) := by
  simp [compile, original, state.isLt]

theorem restoring_transition (machine : Turing.TM0.Machine (Fin alphabet) (Fin states)) (state : Fin states)
    (symbol : Fin alphabet) : (compile machine).transition (restoring state) symbol = some (symbol, false, original state) := by
  have high : ¬ states + state.val < states := by omega
  simp [compile, restoring, high, original]

/-- Mathlib's tape is head-relative. The source's absolute coordinate is carried
by this relation, and every relative position is observed, on both sides. -/
@[expose] def Rep (library : Turing.TM0.Cfg (Fin alphabet) (Fin states))
    (source : TM.Configuration alphabet (2 * states)) : Prop :=
  source.state = original library.q ∧ ∀ position : Int, source.tape (source.head + position) = library.Tape.nth position

omit [Inhabited (Fin states)] in
theorem represented_head (library : Turing.TM0.Cfg (Fin alphabet) (Fin states))
    (source : TM.Configuration alphabet (2 * states)) (rep : Rep library source) :
    source.tape source.head = library.Tape.head := by simpa using rep.2 0

theorem initialized_tape_nth (input : List (Fin alphabet)) (position : Int) :
    (Turing.Tape.mk₁ input).nth position =
      if position < 0 then default else (input[position.toNat]?).getD default := by
  cases position with
  | ofNat index =>
    have nonnegative : ¬ (index : Int) < 0 := by omega
    simp [Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.ListBlank.nth_mk, List.getI, nonnegative]
  | negSucc index =>
    simp [Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk', Turing.Tape.nth, Turing.ListBlank.nth_mk]

theorem initial_rep (machine : Turing.TM0.Machine (Fin alphabet) (Fin states)) (input : List (Fin alphabet)) :
    Rep (Turing.TM0.init input) (TM.initialConfiguration (compile machine) input) := by
  refine ⟨rfl, ?_⟩
  intro position
  simpa [TM.initialConfiguration, compile, Turing.TM0.init] using (initialized_tape_nth input position).symm

@[expose] def moveResult (source : TM.Configuration alphabet (2 * states)) (next : Fin states) (dir : Turing.Dir) :
    TM.Configuration alphabet (2 * states) :=
  { state := original next, head := if direction dir then source.head + 1 else source.head - 1, tape := source.tape }

@[expose] def writeMiddle (source : TM.Configuration alphabet (2 * states)) (next : Fin states) (symbol : Fin alphabet) :
    TM.Configuration alphabet (2 * states) :=
  { state := restoring next, head := source.head + 1, tape := write source.tape source.head symbol }

@[expose] def writeResult (source : TM.Configuration alphabet (2 * states)) (next : Fin states) (symbol : Fin alphabet) :
    TM.Configuration alphabet (2 * states) :=
  { source with state := original next, tape := write source.tape source.head symbol }

theorem move_step (machine : Turing.TM0.Machine (Fin alphabet) (Fin states))
    (library : Turing.TM0.Cfg (Fin alphabet) (Fin states)) (source : TM.Configuration alphabet (2 * states))
    (next : Fin states) (dir : Turing.Dir) (rep : Rep library source)
    (chosen : machine library.q library.Tape.head = some (next, .move dir)) :
    TM.step (compile machine) source = some (moveResult source next dir) := by
  have transition : (compile machine).transition source.state (source.tape source.head) =
      some (source.tape source.head, direction dir, original next) := by
    rw [rep.1, represented_head library source rep, original_transition, chosen]
    rfl
  simpa [moveResult] using TM.transition_correct (compile machine) source (source.tape source.head) (direction dir) (original next) transition

theorem write_first_step (machine : Turing.TM0.Machine (Fin alphabet) (Fin states))
    (library : Turing.TM0.Cfg (Fin alphabet) (Fin states)) (source : TM.Configuration alphabet (2 * states))
    (next : Fin states) (symbol : Fin alphabet) (rep : Rep library source)
    (chosen : machine library.q library.Tape.head = some (next, .write symbol)) :
    TM.step (compile machine) source = some (writeMiddle source next symbol) := by
  have transition : (compile machine).transition source.state (source.tape source.head) = some (symbol, true, restoring next) := by
    rw [rep.1, represented_head library source rep, original_transition, chosen]
    rfl
  simpa [writeMiddle] using TM.transition_correct (compile machine) source symbol true (restoring next) transition

theorem write_second_step (machine : Turing.TM0.Machine (Fin alphabet) (Fin states))
    (source : TM.Configuration alphabet (2 * states)) (next : Fin states) (symbol : Fin alphabet) :
    TM.step (compile machine) (writeMiddle source next symbol) = some (writeResult source next symbol) := by
  have transition := restoring_transition machine next ((writeMiddle source next symbol).tape (writeMiddle source next symbol).head)
  have effect := TM.transition_correct (compile machine) (writeMiddle source next symbol)
    ((writeMiddle source next symbol).tape (writeMiddle source next symbol).head) false (original next) transition
  simp only [Bool.false_eq_true, ite_false, write_back] at effect
  simpa [writeMiddle, writeResult] using effect

theorem write_two_steps (machine : Turing.TM0.Machine (Fin alphabet) (Fin states))
    (library : Turing.TM0.Cfg (Fin alphabet) (Fin states)) (source : TM.Configuration alphabet (2 * states))
    (next : Fin states) (symbol : Fin alphabet) (rep : Rep library source)
    (chosen : machine library.q library.Tape.head = some (next, .write symbol)) :
    TM.run (compile machine) 2 source = some (writeResult source next symbol) := by
  simp [TM.run, write_first_step machine library source next symbol rep chosen, write_second_step]

omit [Inhabited (Fin states)] in
theorem move_rep (library : Turing.TM0.Cfg (Fin alphabet) (Fin states))
    (source : TM.Configuration alphabet (2 * states)) (next : Fin states) (dir : Turing.Dir) (rep : Rep library source) :
    Rep ⟨next, library.Tape.move dir⟩ (moveResult source next dir) := by
  refine ⟨rfl, ?_⟩
  intro position
  cases dir with
  | left =>
    change source.tape (source.head - 1 + position) = (library.Tape.move .left).nth position
    rw [Turing.Tape.move_left_nth, show source.head - 1 + position = source.head + (position - 1) by omega]
    exact rep.2 (position - 1)
  | right =>
    change source.tape (source.head + 1 + position) = (library.Tape.move .right).nth position
    rw [Turing.Tape.move_right_nth, show source.head + 1 + position = source.head + (position + 1) by omega]
    exact rep.2 (position + 1)

omit [Inhabited (Fin states)] in
theorem write_rep (library : Turing.TM0.Cfg (Fin alphabet) (Fin states))
    (source : TM.Configuration alphabet (2 * states)) (next : Fin states) (symbol : Fin alphabet) (rep : Rep library source) :
    Rep ⟨next, library.Tape.write symbol⟩ (writeResult source next symbol) := by
  refine ⟨rfl, ?_⟩
  intro position
  change write source.tape source.head symbol (source.head + position) = (library.Tape.write symbol).nth position
  rw [Turing.Tape.write_nth]
  by_cases zero : position = 0
  · subst position
    simp
  · have separate : source.head + position ≠ source.head := by omega
    simp only [write, separate, ite_false, zero]
    exact rep.2 position

theorem missing_step_iff (machine : Turing.TM0.Machine (Fin alphabet) (Fin states))
    (library : Turing.TM0.Cfg (Fin alphabet) (Fin states)) (source : TM.Configuration alphabet (2 * states))
    (rep : Rep library source) :
    TM.step (compile machine) source = none ↔ Turing.TM0.step machine library = none := by
  have head := represented_head library source rep
  simp only [TM.step, rep.1, head, original_transition, Turing.TM0.step]
  cases selected : machine library.q library.Tape.head with
  | none => simp
  | some command => rcases command with ⟨next, statement⟩; cases statement <;> simp [entry]

/-- One actual Mathlib step takes one or two actual source steps, with the
entire relative tape preserved and no unconstrained intermediate phase. -/
theorem simulate_step (machine : Turing.TM0.Machine (Fin alphabet) (Fin states))
    (library nextLibrary : Turing.TM0.Cfg (Fin alphabet) (Fin states))
    (source : TM.Configuration alphabet (2 * states)) (rep : Rep library source)
    (completed : Turing.TM0.step machine library = some nextLibrary) :
    ∃ count finish, 0 < count ∧ count ≤ 2 ∧ TM.run (compile machine) count source = some finish ∧ Rep nextLibrary finish := by
  cases chosen : machine library.q library.Tape.head with
  | none => simp [Turing.TM0.step, chosen] at completed
  | some command =>
    rcases command with ⟨next, statement⟩
    cases statement with
    | move dir =>
      have same : (⟨next, library.Tape.move dir⟩ : Turing.TM0.Cfg (Fin alphabet) (Fin states)) = nextLibrary :=
        Option.some.inj (by simpa [Turing.TM0.step, chosen] using completed)
      subst nextLibrary
      refine ⟨1, moveResult source next dir, by decide, by decide, ?_, move_rep library source next dir rep⟩
      simp [TM.run, move_step machine library source next dir rep chosen]
    | write symbol =>
      have same : (⟨next, library.Tape.write symbol⟩ : Turing.TM0.Cfg (Fin alphabet) (Fin states)) = nextLibrary :=
        Option.some.inj (by simpa [Turing.TM0.step, chosen] using completed)
      subst nextLibrary
      exact ⟨2, writeResult source next symbol, by decide, by decide,
        write_two_steps machine library source next symbol rep chosen, write_rep library source next symbol rep⟩


theorem source_run_reaches {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (count : Nat) (start finish : TM.Configuration alphabet states)
    (completed : TM.run machine count start = some finish) :
    StateTransition.Reaches (TM.step machine) start finish := by
  induction count generalizing start with
  | zero =>
    have same : start = finish := Option.some.inj completed
    subst finish
    exact Relation.ReflTransGen.refl
  | succ count ih =>
    cases first : TM.step machine start with
    | none => simp [TM.run, first] at completed
    | some next =>
      have rest : TM.run machine count next = some finish := by simpa [TM.run, first] using completed
      exact Relation.ReflTransGen.head first (ih next rest)

theorem source_reaches_run {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (start finish : TM.Configuration alphabet states)
    (reached : StateTransition.Reaches (TM.step machine) start finish) :
    ∃ count, TM.run machine count start = some finish := by
  induction reached with
  | refl => exact ⟨0, rfl⟩
  | @tail middle finish history last ih =>
    rcases ih with ⟨count, completed⟩
    refine ⟨count + 1, ?_⟩
    rw [TM.run_add, completed]
    simpa [TM.run] using last

theorem source_halts_eval {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (start : TM.Configuration alphabet states) :
    TM.Halts machine start ↔ (StateTransition.eval (TM.step machine) start).Dom := by
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨count, finish, completed, halted⟩
    exact ⟨finish, StateTransition.mem_eval.mpr ⟨source_run_reaches machine count start finish completed, halted⟩⟩
  · rintro ⟨finish, result⟩
    rcases StateTransition.mem_eval.mp result with ⟨reached, halted⟩
    rcases source_reaches_run machine start finish reached with ⟨count, completed⟩
    exact ⟨count, finish, completed, halted⟩

variable {alphabet states : Nat} [Inhabited (Fin alphabet)] [Inhabited (Fin states)]

/-- Refinement for the actual imported Mathlib transition functions. Each
library transition takes a positive number of source transitions. -/
theorem compiler_respects (machine : Turing.TM0.Machine (Fin alphabet) (Fin states)) :
    StateTransition.Respects (Turing.TM0.step machine) (TM.step (compile machine)) Rep := by
  intro library source rep
  cases chosen : machine library.q library.Tape.head with
  | none =>
    have halted : Turing.TM0.step machine library = none := by simp [Turing.TM0.step, chosen]
    rw [halted]
    exact (missing_step_iff machine library source rep).mpr halted
  | some command =>
    rcases command with ⟨next, statement⟩
    cases statement with
    | move dir =>
      simp only [Turing.TM0.step, chosen, Option.map_some]
      exact ⟨moveResult source next dir, move_rep library source next dir rep,
        Relation.TransGen.single (move_step machine library source next dir rep chosen)⟩
    | write symbol =>
      simp only [Turing.TM0.step, chosen, Option.map_some]
      have before : StateTransition.Reaches₁ (TM.step (compile machine)) source (writeMiddle source next symbol) :=
        Relation.TransGen.single (write_first_step machine library source next symbol rep chosen)
      exact ⟨writeResult source next symbol, write_rep library source next symbol rep,
        before.trans
          (Relation.TransGen.single (write_second_step machine source next symbol))⟩

theorem standard_halts_iff (machine : Turing.TM0.Machine (Fin alphabet) (Fin states)) (input : List (Fin alphabet)) :
    TM.Halts (compile machine) (TM.initialConfiguration (compile machine) input) ↔
      (Turing.TM0.eval machine input).Dom := by
  rw [source_halts_eval]
  exact StateTransition.tr_eval_dom (compiler_respects machine) (initial_rep machine input)


end WriteExecute.MathlibTM0
