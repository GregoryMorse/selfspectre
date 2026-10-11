module
public import WriteExecute.Spec.Machine
public import WriteExecute.Spec.Confinement
public import WriteExecute.Spec.Universal
public import WriteExecute.Spec.Arith
public import WriteExecute.Spec.AES
public import WriteExecute.Spec.Spectre

public section

namespace WriteExecute.Paper

open WriteExecute

/-- C01: one step is a function of the three words at the program counter alone, with at most one store
(`effect`); there is no data read, register or stack. -/
@[expose] def ReadFree : Prop := ∀ s : WE.State,
  WE.step s =
    ((WE.effect s.pc (s.mem s.pc) (s.mem (s.pc + 1)) (s.mem (s.pc + 2))).1,
     ⟨(WE.effect s.pc (s.mem s.pc) (s.mem (s.pc + 1)) (s.mem (s.pc + 2))).2.1,
      match (WE.effect s.pc (s.mem s.pc) (s.mem (s.pc + 1)) (s.mem (s.pc + 2))).2.2 with
      | none => s.mem
      | some (a, v) => write s.mem a v⟩)

/-- C02: every finite-alphabet Turing machine is simulated step for step (`Q + 2` Write-Execute steps per
step) by the unbounded blank-cell image; halting, divergence and the tape are preserved and the image
never faults. -/
@[expose] def TuringComplete : Prop := ∀ (A Q : Nat) (M : TM.Machine A Q) (cfg : TM.Configuration A Q),
  (WE.Halts (Universal.encode M cfg) ↔ TM.Halts M cfg) ∧
  (WE.Diverges (Universal.encode M cfg) ↔ TM.Diverges M cfg) ∧
  ¬ WE.Faults (Universal.encode M cfg) ∧
  (∀ (n : Nat) (cfg' : TM.Configuration A Q), TM.run M n cfg = some cfg' →
    WE.run (n * (Q + 2)) (Universal.encode M cfg) = (WE.Status.running, Universal.encode M cfg')) ∧
  (∀ input : List (Fin A),
    (WE.Halts (Universal.initial M input) ↔ TM.Halts M (TM.initialConfiguration M input)) ∧
    (WE.Diverges (Universal.initial M input) ↔ TM.Diverges M (TM.initialConfiguration M input)))

/-- C03: the finite image of `N` cells is exact while the head stays inside it, halting there is faithful,
and the first step out of the image faults. -/
@[expose] def FiniteRealization : Prop := ∀ (A Q : Nat) (M : TM.Machine A Q) (N : Nat),
  (∀ (n : Nat) (cfg cfg' : TM.Configuration A Q), TM.run M n cfg = some cfg' →
    (∀ k, k < n → ∀ c1, TM.run M k cfg = some c1 → 0 ≤ c1.head ∧ c1.head < (N : Int)) →
    WE.run (n * (Q + 2)) (Universal.encodeB M N cfg) = (WE.Status.running, Universal.encodeB M N cfg')) ∧
  (∀ (cfg fin : TM.Configuration A Q) (n : Nat), TM.run M n cfg = some fin → TM.step M fin = none →
    (∀ k, k < n → ∀ c1, TM.run M k cfg = some c1 → 0 ≤ c1.head ∧ c1.head < (N : Int)) →
    (0 ≤ fin.head ∧ fin.head < (N : Int)) → WE.Halts (Universal.encodeB M N cfg)) ∧
  (∀ (cfg fin fin' : TM.Configuration A Q) (n : Nat), TM.run M n cfg = some fin →
    TM.step M fin = some fin' →
    (∀ k, k < n → ∀ c1, TM.run M k cfg = some c1 → 0 ≤ c1.head ∧ c1.head < (N : Int)) →
    (0 ≤ fin.head ∧ fin.head < (N : Int)) → ¬ (0 ≤ fin'.head ∧ fin'.head < (N : Int)) →
    WE.Faults (Universal.encodeB M N cfg))

/-- C04: a run that only fetches inside a finite address list keeps its memory off a finite target list
unchanged and all fetched and stored values inside finite lists. -/
@[expose] def Confinement : Prop := ∀ (A : List Int) (s0 : WE.State), WE.Confined A s0 →
  ∀ (n : Nat) (s : WE.State), WE.run n s0 = (WE.Status.running, s) →
    s.pc ∈ A ∧ (∀ x ∈ WE.fetchWords A, s.mem x ∈ WE.valueList A s0) ∧
    (∀ x, x ∉ WE.targetList A s0 → s.mem x = s0.mem x) ∧
    (∀ x ∈ WE.targetList A s0, s.mem x ∈ WE.allValues A s0)

/-- C05-C06: the jump-table lookup `[JMP e; ...; e: MOV res f; JMP ret]` computes the table function, and
the 8-bit tables of writeexc.asm (NOT, NZ, SHL, SHR, INC, DEC, SUB, ADD with carry) compute the
operations they are named for. -/
@[expose] def Primitives : Prop :=
  (∀ (m : Int → Int) (c e res ret f : Int), m c = 2 → m (c + 1) = e - (c + 2) →
    m e = 1 → m (e + 1) = res - (e + 3) → m (e + 2) = f → m (e + 3) = 2 → m (e + 4) = ret - (e + 5) →
    res ≠ e + 3 → res ≠ e + 4 →
    WE.run 3 ⟨c, m⟩ = (WE.Status.running, ⟨ret, write m res f⟩)) ∧
  (∀ i, i < 256 → Arith.tNot i = 255 - i) ∧
  (∀ i, Arith.tNZ i = if i = 0 then 0 else 1) ∧
  (∀ o, o < 9 → ∀ i, i < 256 → Arith.tShlLo o i < 256 ∧ Arith.tShlLo o i % 2 ^ o = 0 ∧
    Arith.tShlHi o i < 2 ^ o ∧ Arith.tShlHi o i * 256 + Arith.tShlLo o i = i * 2 ^ o) ∧
  (∀ o i h, o < 9 → i < 256 → h < 2 ^ o → (Arith.tShlLo o i ^^^ h) = Arith.tShlLo o i + h) ∧
  (∀ o, o < 9 → ∀ i, i < 256 → Arith.tShrHi o i < 2 ^ (8 - o) ∧ Arith.tShrLo o i < 256 ∧
    Arith.tShrLo o i = (i % 2 ^ o) * 2 ^ (8 - o) ∧ Arith.tShrHi o i = i / 2 ^ o) ∧
  (∀ o a j, o < 9 → a < 256 → j < 256 → (Arith.tShrHi o a ^^^ Arith.tShrLo o j) = Arith.tShrHi o a + Arith.tShrLo o j) ∧
  (∀ i, i < 256 → Arith.tIncLo i + 256 * Arith.tIncHi i = i + 1 ∧ Arith.tIncLo i < 256 ∧ Arith.tIncHi i < 2) ∧
  (∀ i, i < 256 → Arith.tDecLo i + 1 = i + 256 * Arith.tDecBor i ∧ Arith.tDecLo i < 256 ∧
    Arith.tDecBor i < 2 ∧ (Arith.tDecBor i = 1 → i = 0)) ∧
  (∀ a b, a < 256 → b < 256 → Arith.tSubLo a b + b = a + 256 * Arith.tSubBor a b ∧
    Arith.tSubLo a b < 256 ∧ Arith.tSubBor a b < 2) ∧
  (∀ a b, Arith.tAddLo a b = (a + b) % 256) ∧
  (∀ a b, a < 256 → b < 256 → Arith.tAddCry a b = (a + b) / 256)

/-- C07-C12: wide arithmetic built from the tables (any width ADD, SUB, SHL, SHR, XOR; 32 x 32 -> 64
multiplication; 64 / 32 division with remainder-overflow bit; two-step modular reduction; modular
exponentiation with the multiplication count; the legacy `mulmod` is wrong). -/
@[expose] def Arithmetic : Prop :=
  (∀ n x y, Arith.addN n x y = (x + y) % 256 ^ n) ∧
  (∀ n x y, Arith.subN n x y = (x % 256 ^ n + 256 ^ n - y % 256 ^ n) % 256 ^ n) ∧
  (∀ n x c, Arith.shlN n x c = (x * 2 ^ c) % 256 ^ n) ∧
  (∀ n x c, Arith.shrN n x c = (x % 256 ^ n) / 2 ^ c) ∧
  (∀ n x y, Arith.xorN n x y = (x ^^^ y) % 256 ^ n) ∧
  (∀ x y, y < 2 ^ 32 → Arith.mul32 x y = (x * y) % 2 ^ 64) ∧
  (∀ x y, x < 2 ^ 32 → y < 2 ^ 32 → Arith.mul32 x y = x * y) ∧
  (∀ x y, x < 2 ^ 64 → 0 < y → y < 2 ^ 32 → Arith.doDivision x y = ((x / y) % 2 ^ 32, x % y)) ∧
  (∀ a b m, 0 < m → Arith.mulmodFixed a b m = (a * b) % m) ∧
  Arith.mulmodLegacy 65536 65536 3 ≠ (65536 * 65536) % 3 ∧
  (∀ b e m, 2 ≤ m → e < 2 ^ 32 → Arith.modexpAsm b e m = b ^ e % m) ∧
  (∀ b e m, 1 ≤ m → e < 2 ^ 32 → Arith.modexpRef b e m = b ^ e % m) ∧
  (∀ b e m, 1 ≤ m → Arith.modexpNaive b e m = b ^ e % m) ∧
  (∀ e, 1 ≤ e → e < 2 ^ 32 → Arith.mulCount 32 e = Nat.log2 e + 1 + Arith.popcount 32 e)

/-- C13-C15: the S-box is the field inverse followed by the affine map, `Te4` repeats it in each byte, the
Write-Execute AES procedure computes the FIPS-197 cipher from the expanded key, and the specification
reproduces the FIPS-197 Appendix C.1 known answer. -/
@[expose] def AESResult : Prop :=
  (∀ x, x < 256 → AES.sbox x = AES.sboxAlg x) ∧
  (∀ x, x < 256 → AES.te4Lit x = AES.sbox x * 0x01010101) ∧
  (∀ (w pt : List Nat), pt.length = 16 → (∀ i, pt.getD i 0 < 256) → ∀ idx, idx < 16 →
    AES.weCipher (fun i => pt.getD i 0) w idx = (AES.cipher w pt).getD idx 0) ∧
  AES.aes128 [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f]
    [0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff] =
    [0x69, 0xc4, 0xe0, 0xd8, 0x6a, 0x7b, 0x04, 0x30, 0xd8, 0xcd, 0xb7, 0x80, 0x70, 0xb4, 0xc5, 0x5a]

/-- C19-C20: Fig. 1 selects the malicious index exactly when `j % 6 = 0` (32- and 64-bit `size_t`), and the
probe order `(i * 167 + 13) & 255` is a permutation of `0 .. 255`. -/
@[expose] def SpectreArithmetic : Prop :=
  (∀ (j : Nat) (t m : BitVec 32), Spectre.selectIdx 32 j t m = if j % 6 = 0 then m else t) ∧
  (∀ (j : Nat) (t m : BitVec 64), Spectre.selectIdx 64 j t m = if j % 6 = 0 then m else t) ∧
  (∀ i, i < 256 → Spectre.mixIdx i < 256) ∧
  (∀ a b, a < 256 → b < 256 → Spectre.mixIdx a = Spectre.mixIdx b → a = b) ∧
  (∀ j, j < 256 → ∃ i, i < 256 ∧ Spectre.mixIdx i = j)

end WriteExecute.Paper
