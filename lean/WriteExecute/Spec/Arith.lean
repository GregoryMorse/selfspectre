module

public section

/-! Algorithm-level specifications of the Write-Execute arithmetic (writeexc.asm), over little-endian
base-256 digit lists. The asm itself is evidence-tied (native vectors), not proved: see D1 in the plan.
Table functions transcribe the MASM macro expressions literally. -/

namespace WriteExecute.Arith

@[expose] def ofBytes : List Nat → Nat
  | [] => 0
  | b :: bs => b + 256 * ofBytes bs

@[expose] def toBytes : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, x => x % 256 :: toBytes k (x / 256)

/-! 8-bit tables (writeexc.asm: DEFINENOT, DEFINENZ, DEFINESHLGEN, DEFINESHRGEN, DEFINEINC, DEFINEDEC,
DEFINEADD, DEFINESUB; XOR/OR/AND are the bitwise operators). -/

@[expose] def tNot (i : Nat) : Nat := i ^^^ 255
@[expose] def tNZ (i : Nat) : Nat := if i ≠ 0 then 1 else 0
@[expose] def tShlLo (o i : Nat) : Nat := (i <<< o) &&& 255
@[expose] def tShlHi (o i : Nat) : Nat := i >>> (8 - o)
@[expose] def tShrLo (o i : Nat) : Nat := (i <<< (8 - o)) &&& 255
@[expose] def tShrHi (o i : Nat) : Nat := i >>> o
@[expose] def tIncLo (i : Nat) : Nat := (i + 1) &&& 255
@[expose] def tIncHi (i : Nat) : Nat := (i + 1) >>> 8
@[expose] def tDecLo (i : Nat) : Nat := (i + 255) &&& 255
@[expose] def tDecBor (i : Nat) : Nat := if i = 0 then 1 else 0
@[expose] def tAddLo (a b : Nat) : Nat := (a + b) &&& 255
/-- The carry expression of DEFINEADD: `(Orig and 80h and Index and 80h or (not (Orig+Index)) and 80h
and ((Index and 80h) xor (Orig and 80h))) shr 7`. -/
@[expose] def tAddCry (a b : Nat) : Nat :=
  (((a &&& 0x80) &&& (b &&& 0x80)) |||
    ((((a + b) &&& 0x80) ^^^ 0x80) &&& ((b &&& 0x80) ^^^ (a &&& 0x80)))) >>> 7
@[expose] def tSubLo (a b : Nat) : Nat := (a + 256 - b) &&& 255
@[expose] def tSubBor (a b : Nat) : Nat := if a < b then 1 else 0

/-! Wide addition/subtraction (ADDBYTE/SUBBYTE): byte `i` first receives the carry of byte `i-1` by
`INC` (resp. `DEC`) on its first operand, then the byte table. The two carries are exclusive. -/

@[expose] def incIf (cin a : Nat) : Nat × Nat :=
  if cin = 1 then (tIncLo a, tIncHi a) else (a, 0)

@[expose] def decIf (bin a : Nat) : Nat × Nat :=
  if bin = 1 then (tDecLo a, tDecBor a) else (a, 0)

@[expose] def addDigits : List Nat → List Nat → Nat → List Nat × Nat
  | a :: as, b :: bs, cin =>
    let p := incIf cin a
    let r := addDigits as bs (tAddCry p.1 b + p.2)
    (tAddLo p.1 b :: r.1, r.2)
  | _, _, cin => ([], cin)

@[expose] def subDigits : List Nat → List Nat → Nat → List Nat × Nat
  | a :: as, b :: bs, bin =>
    let p := decIf bin a
    let r := subDigits as bs (tSubBor p.1 b + p.2)
    (tSubLo p.1 b :: r.1, r.2)
  | _, _, bin => ([], bin)

/-- `n`-byte wrapping addition / subtraction. -/
@[expose] def addN (n x y : Nat) : Nat := ofBytes (addDigits (toBytes n x) (toBytes n y) 0).1
@[expose] def subN (n x y : Nat) : Nat := ofBytes (subDigits (toBytes n x) (toBytes n y) 0).1

/-! Shifts (SHLBYTE/SHLCARRY, SHRBYTE/SHRCARRY): a whole-byte move by `c / 8` and a bit shift by
`c % 8` through the SHLGEN/SHRGEN tables, the carry between bytes combined with XOR. -/

@[expose] def shlPass (o : Nat) : Nat → List Nat → List Nat
  | _, [] => []
  | h, b :: bs => (tShlLo o b ^^^ h) :: shlPass o (tShlHi o b) bs

@[expose] def shrPass (o : Nat) : List Nat → List Nat
  | [] => []
  | [b] => [tShrHi o b]
  | b :: c :: bs => (tShrHi o b ^^^ tShrLo o c) :: shrPass o (c :: bs)

@[expose] def shlN (n x c : Nat) : Nat :=
  ofBytes (shlPass (c % 8) 0 ((List.replicate (c / 8) 0 ++ toBytes n x).take n))

@[expose] def shrN (n x c : Nat) : Nat :=
  ofBytes (shrPass (c % 8) ((toBytes n x).drop (c / 8) ++ List.replicate (c / 8) 0))

/-- XOR of `n`-byte words, byte by byte through the XOR table. -/
@[expose] def xorDigits : List Nat → List Nat → List Nat
  | a :: as, b :: bs => (a ^^^ b) :: xorDigits as bs
  | _, _ => []

@[expose] def xorN (n x y : Nat) : Nat := ofBytes (xorDigits (toBytes n x) (toBytes n y))

/-- 32 x 32 -> 64 shift-and-add multiplication (WriteExecMUL32; `doMul` in writeexec.c). -/
@[expose] def mulLoop : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | k + 1, tx, y, acc =>
    mulLoop k (shlN 8 tx 1) (y / 2) (if y % 2 = 1 then addN 8 acc tx else acc)

@[expose] def mul32 (x y : Nat) : Nat := mulLoop 32 x y 0

/-- One iteration of `doDivision` (writeexec.c): 64-bit `quot`, 32-bit `rem`, with the remainder
overflow bit. -/
@[expose] def divStep (y : Nat) (s : Nat × Nat) : Nat × Nat :=
  let quot' := (s.1 * 2) % 2 ^ 64
  let carry := if quot' < s.1 then 1 else 0
  let remof := s.2 / 2 ^ 31 % 2 = 1
  let rem1 := (s.2 * 2 + carry) % 2 ^ 32
  if remof ∨ y ≤ rem1 then ((quot' + 1) % 2 ^ 64, (rem1 + 2 ^ 32 - y) % 2 ^ 32)
  else (quot', rem1)

@[expose] def divRun (y : Nat) : Nat → Nat × Nat → Nat × Nat
  | 0, s => s
  | k + 1, s => divRun y k (divStep y s)

/-- `(quotient mod 2^32, remainder)` of a 64-bit dividend by a 32-bit divisor. -/
@[expose] def doDivision (x y : Nat) : Nat × Nat :=
  let r := divRun y 64 (x, 0)
  (r.1 % 2 ^ 32, r.2)

/-- Right-to-left square and multiply (WriteExecMODEXP32). `init` is `1` in the asm (precondition
`m ≥ 2`) and `1 % m` in the corrected C reference (L02). -/
@[expose] def modexpLoop (m : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, r, _, _ => r
  | k + 1, r, b, e =>
    if e = 0 then r else modexpLoop m k (if e % 2 = 1 then r * b % m else r) (b * b % m) (e / 2)

@[expose] def modexpAsm (b e m : Nat) : Nat := modexpLoop m 32 1 (b % m) e
@[expose] def modexpRef (b e m : Nat) : Nat := modexpLoop m 32 (1 % m) (b % m) e

/-- Modular multiplications performed: one square per exponent bit and one multiply per set bit. -/
@[expose] def mulCount : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, e => if e = 0 then 0 else e % 2 + 1 + mulCount k (e / 2)

@[expose] def popcount : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, e => e % 2 + popcount k (e / 2)


/-- `mulmod` of spectreopt.c as published (the high half is divided, not reduced; see erratum L03). -/
@[expose] def mulmodLegacy (a b m : Nat) : Nat :=
  ((((a * b) / 2 ^ 32) / m) * 2 ^ 32 + (a * b) % 2 ^ 32) % m

/-- The corrected two-step reduction: reduce the high half, then the 64-bit value `hi * 2^32 + lo`. -/
@[expose] def mulmodFixed (a b m : Nat) : Nat :=
  ((((a * b) / 2 ^ 32) % m) * 2 ^ 32 + (a * b) % 2 ^ 32) % m


/-- The naive reference of the paper (`modexp` in spectreopt.c): one modular multiplication per unit
of the exponent. -/
@[expose] def naiveLoop (m b : Nat) : Nat → Nat → Nat
  | 0, c => c
  | k + 1, c => naiveLoop m b k (c * b % m)

@[expose] def modexpNaive (b e m : Nat) : Nat := if m = 1 then 0 else naiveLoop m b e 1

end WriteExecute.Arith
