module

public section

/-! Byte-level model of the instruction subset used by the Write-Execute core of `writeexc.asm`:
`mov byte/word/dword ptr [disp32], imm` (`C6 05`, `66 C7 05`, `C7 05`), `jmp rel8/rel32` (`EB`, `E9`)
and `nop` (`90`). No register, no stack, no data read. Memory is a function from addresses to bytes
(values below 256); instruction fetch reads the *current* bytes, so patched operands take effect.
Addresses are naturals; the proofs assume they stay below `2^31`. -/

namespace WriteExecute.X86

abbrev Mem := Nat → Nat

/-- x86 uses the absolute `disp32` as the effective address; x64 uses RIP-relative `disp32`. -/
inductive Mode where
  | x86
  | x64

inductive Ins where
  | nop
  | jmp8 (rel : Nat)
  | jmp32 (rel : Nat)
  | movB (disp imm : Nat)
  | movW (disp imm : Nat)
  | movD (disp imm : Nat)

/-- Little-endian bytes of the low `n` bytes of `v`. -/
@[expose] def le : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, v => v % 256 :: le n (v / 256)

@[expose] def enc : Ins → List Nat
  | .nop => [0x90]
  | .jmp8 r => [0xEB, r]
  | .jmp32 r => 0xE9 :: le 4 r
  | .movB d i => 0xC6 :: 0x05 :: le 4 d ++ [i]
  | .movW d i => 0x66 :: 0xC7 :: 0x05 :: le 4 d ++ le 2 i
  | .movD d i => 0xC7 :: 0x05 :: le 4 d ++ le 4 i

@[expose] def Ins.len : Ins → Nat
  | .nop => 1
  | .jmp8 _ => 2
  | .jmp32 _ => 5
  | .movB _ _ => 7
  | .movW _ _ => 9
  | .movD _ _ => 10

/-- Little-endian value of `n` bytes at `a`. -/
@[expose] def rd (m : Mem) (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => m a + 256 * rd m (a + 1) n

/-- Store the low `n` bytes of `v` at `a`. -/
@[expose] def wr (m : Mem) (a n v : Nat) : Mem :=
  fun x => if a ≤ x ∧ x < a + n then v / 256 ^ (x - a) % 256 else m x

/-- Memory holds exactly these bytes from `a`. -/
@[expose] def Code (m : Mem) : Nat → List Nat → Prop
  | _, [] => True
  | a, b :: bs => m a = b ∧ Code m (a + 1) bs

@[expose] def decode (m : Mem) (pc : Nat) : Option Ins :=
  if m pc = 0x90 then some .nop
  else if m pc = 0xEB then some (.jmp8 (m (pc + 1)))
  else if m pc = 0xE9 then some (.jmp32 (rd m (pc + 1) 4))
  else if m pc = 0xC6 ∧ m (pc + 1) = 5 then some (.movB (rd m (pc + 2) 4) (m (pc + 6)))
  else if m pc = 0x66 ∧ m (pc + 1) = 0xC7 ∧ m (pc + 2) = 5 then
    some (.movW (rd m (pc + 3) 4) (rd m (pc + 7) 2))
  else if m pc = 0xC7 ∧ m (pc + 1) = 5 then some (.movD (rd m (pc + 2) 4) (rd m (pc + 6) 4))
  else none

/-- Two's complement reading of an `n`-bit field. -/
@[expose] def sext (n w : Nat) : Int := if w < 2 ^ (n - 1) then (w : Int) else (w : Int) - 2 ^ n

/-- `pc + len + d`, if non-negative. -/
@[expose] def tgt (pc len : Nat) (d : Int) : Option Nat :=
  if 0 ≤ (pc + len : Int) + d then some ((pc + len : Int) + d).toNat else none

/-- Effective address of a store with displacement field `d` in an instruction of length `len`. -/
@[expose] def ea : Mode → Nat → Nat → Nat → Option Nat
  | .x86, _, _, d => some d
  | .x64, pc, len, d => tgt pc len (sext 32 d)

/-- The `disp32` field that makes an instruction at `A` of length `len` address `T`. -/
@[expose] def fld : Mode → Nat → Nat → Nat → Nat
  | .x86, _, _, T => T
  | .x64, A, len, T => (T + 2 ^ 32 - (A + len)) % 2 ^ 32

/-- The `rel32` field of a `jmp rel32` at `A` that goes to `T`. -/
@[expose] def jrel (A T : Nat) : Nat := (T + 2 ^ 32 - (A + 5)) % 2 ^ 32

@[expose] def step (mode : Mode) (s : Nat × Mem) : Option (Nat × Mem) :=
  match decode s.2 s.1 with
  | some .nop => some (s.1 + 1, s.2)
  | some (.jmp8 r) => (tgt s.1 2 (sext 8 r)).map fun t => (t, s.2)
  | some (.jmp32 r) => (tgt s.1 5 (sext 32 r)).map fun t => (t, s.2)
  | some (.movB d i) => (ea mode s.1 7 d).map fun a => (s.1 + 7, wr s.2 a 1 i)
  | some (.movW d i) => (ea mode s.1 9 d).map fun a => (s.1 + 9, wr s.2 a 2 i)
  | some (.movD d i) => (ea mode s.1 10 d).map fun a => (s.1 + 10, wr s.2 a 4 i)
  | none => none

@[expose] def runN (mode : Mode) : Nat → Nat × Mem → Option (Nat × Mem)
  | 0, s => some s
  | n + 1, s => (step mode s).bind (runN mode n)

end WriteExecute.X86
