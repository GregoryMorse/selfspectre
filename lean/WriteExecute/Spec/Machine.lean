module
public import WriteExecute.Base.Memory

public section

namespace WriteExecute.WE

/-- Ideal word-level Write-Execute machine: unbounded integer addresses and values, no registers,
no stack, no data reads. The only state is the program counter and the memory. -/
structure State where
  pc : Int
  mem : Int → Int

/-- Instruction encodings: `[1, rel, val]` stores `val` at `pc + 3 + rel` (displacement from the next
instruction, as with x86-64 RIP-relative addressing); `[2, rel]` jumps to `pc + 2 + rel`; `[3]` halts. -/
inductive Instr where
  | mov (rel val : Int)
  | jmp (rel : Int)
  | hlt

inductive Status where
  | running
  | halted
  | faulted
  deriving DecidableEq

/-- Instruction fetch reads only the three words at `pc`. Any other opcode word is a fault. -/
@[expose] def decode (m : Int → Int) (pc : Int) : Option Instr :=
  if m pc = 1 then some (.mov (m (pc + 1)) (m (pc + 2)))
  else if m pc = 2 then some (.jmp (m (pc + 1)))
  else if m pc = 3 then some .hlt
  else none

@[expose] def step (s : State) : Status × State :=
  match decode s.mem s.pc with
  | some (.mov r v) => (.running, ⟨s.pc + 3, write s.mem (s.pc + 3 + r) v⟩)
  | some (.jmp r) => (.running, ⟨s.pc + 2 + r, s.mem⟩)
  | some .hlt => (.halted, s)
  | none => (.faulted, s)

/-- Run at most `n` steps, stopping at the first non-running status. -/
@[expose] def run : Nat → State → Status × State
  | 0, s => (.running, s)
  | n + 1, s =>
    match step s with
    | (.running, t) => run n t
    | r => r

@[expose] def Halts (s : State) : Prop := ∃ n t, run n s = (.halted, t)
@[expose] def Faults (s : State) : Prop := ∃ n t, run n s = (.faulted, t)
@[expose] def Diverges (s : State) : Prop := ∀ n, (run n s).1 = .running

/-- The complete effect of one step as a function of the fetch window `(pc, m pc, m (pc+1), m (pc+2))`:
status, next program counter, and at most one store. -/
@[expose] def effect (pc a b c : Int) : Status × Int × Option (Int × Int) :=
  if a = 1 then (.running, pc + 3, some (pc + 3 + b, c))
  else if a = 2 then (.running, pc + 2 + b, none)
  else if a = 3 then (.halted, pc, none)
  else (.faulted, pc, none)

end WriteExecute.WE
