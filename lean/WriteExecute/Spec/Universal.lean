module
public import WriteExecute.Spec.Machine
public import WriteExecute.Base.Turing

public section

namespace WriteExecute.Universal

open WriteExecute.TM

/-! The construction. One tape cell is a block of `cellSize` words. Its first `2Q` words are one jump
per state `q` (`[2, d]` at offset `2q`); the displacement `d` of that jump records the cell's symbol
by pointing at the handler for `(q, symbol)`. A handler for a transition `(q,a) -> (a',right,q')` is
`Q` stores that rewrite every entry displacement of the current cell to symbol `a'`, followed by a
jump to the entry of state `q'` in the neighbouring cell. A missing transition is a halt. Handlers are
never written; only the entry displacements are. -/

@[expose] def handlerSize (Q : Nat) : Nat := 3 * Q + 2
@[expose] def cellSize (A Q : Nat) : Nat := 2 * Q + Q * A * handlerSize Q
/-- Offset of the handler for state `q` and symbol `sym` inside a cell. -/
@[expose] def handlerAt (A Q q sym : Nat) : Nat := 2 * Q + (q * A + sym) * handlerSize Q
/-- Displacement of state `q`'s entry jump (at offset `2q`) when the cell holds `sym`. -/
@[expose] def entryDisp (A Q q sym : Nat) : Int := (handlerAt A Q q sym : Int) - 2 * (q : Int) - 2

@[expose] def trans {A Q : Nat} (M : Machine A Q) (q sym : Nat) : Option (Fin A × Bool × Fin Q) :=
  if h : q < Q ∧ sym < A then M.transition ⟨q, h.1⟩ ⟨sym, h.2⟩ else none

/-- Word `off` of the handler for `(q, sym)`. -/
@[expose] def handlerWord {A Q : Nat} (M : Machine A Q) (q sym off : Nat) : Int :=
  match trans M q sym with
  | none => if off = 0 then 3 else 0
  | some (next, right, q') =>
    if off < 3 * Q then
      (if off % 3 = 0 then 1
       else if off % 3 = 1 then
         (2 * ((off / 3 : Nat) : Int) + 1) - ((handlerAt A Q q sym : Int) + 3 * ((off / 3 : Nat) : Int) + 3)
       else entryDisp A Q (off / 3) next.val)
    else if off = 3 * Q then 2
    else
      (if right then (cellSize A Q : Int) else -(cellSize A Q : Int)) + 2 * (q'.val : Int)
        - ((handlerAt A Q q sym : Int) + 3 * (Q : Int) + 2)

/-- Word `j` of a cell holding symbol `sym`. -/
@[expose] def cellWord {A Q : Nat} (M : Machine A Q) (sym j : Nat) : Int :=
  if j < 2 * Q then (if j % 2 = 0 then 2 else entryDisp A Q (j / 2) sym)
  else if j - 2 * Q < Q * A * handlerSize Q then
    handlerWord M ((j - 2 * Q) / handlerSize Q / A) ((j - 2 * Q) / handlerSize Q % A) ((j - 2 * Q) % handlerSize Q)
  else 0

/-- The memory image of a tape: cell `c` occupies addresses `c * cellSize .. c * cellSize + cellSize - 1`. -/
@[expose] def layout {A Q : Nat} (M : Machine A Q) (tape : Int → Fin A) : Int → Int :=
  fun a => cellWord M (tape (a / (cellSize A Q : Int))).val (a % (cellSize A Q : Int)).toNat

/-- A configuration's machine state: the program counter is at the entry of the current state in the
current cell. -/
@[expose] def encode {A Q : Nat} (M : Machine A Q) (cfg : Configuration A Q) : WE.State :=
  ⟨cfg.head * (cellSize A Q : Int) + 2 * (cfg.state.val : Int), layout M cfg.tape⟩

/-- The initial image for a finite input: the template everywhere, the input in cells `0 ..`. -/
@[expose] def initial {A Q : Nat} (M : Machine A Q) (input : List (Fin A)) : WE.State :=
  encode M (initialConfiguration M input)

end WriteExecute.Universal
