module
public import WriteExecute.Spec.Machine
public import WriteExecute.Spec.Confinement
public import WriteExecute.Spec.Universal
public import WriteExecute.Spec.Arith
public import WriteExecute.Spec.AES
public import WriteExecute.Spec.Speculation

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

/-- C19, C23 (Fig. 1, Sec. 2): take the branch predictor as an abstract parameter that guesses "taken"
after `k <= 5` consecutive "taken" outcomes, whatever its earlier state. In every round of the PoC's
training loop (`for (j = 29; j >= 0; j--)`, five in-bounds calls before each malicious call), at each of
the five malicious calls (`j % 6 = 0`) the predictor guesses "taken" although the guard is false. Fig. 1's
branch-free select makes the guard true exactly at the other calls (32- and 64-bit `size_t`), and the
textbook 2-bit counter satisfies the assumption. -/
@[expose] def Mistraining : Prop :=
  (∀ (P : Speculation.Predictor) (k : Nat), P.Trains k → k ≤ 5 → ∀ (s0 : P.S) (j : Nat),
      j ≤ 29 → j % 6 = 0 →
      P.predict (P.after s0 (Speculation.historyBefore j)) = true ∧ Speculation.guardAt j = false) ∧
  (∀ (j : Nat) (t m : BitVec 32) (size : Nat), t.toNat < size → size ≤ m.toNat →
      ((Spectre.selectIdx 32 j t m).toNat < size ↔ Speculation.guardAt j = true)) ∧
  (∀ (j : Nat) (t m : BitVec 64) (size : Nat), t.toNat < size → size ≤ m.toNat →
      ((Spectre.selectIdx 64 j t m).toNat < size ↔ Speculation.guardAt j = true)) ∧
  Speculation.counter2.Trains 3

/-- C24 (Fig. 2): a mispredicted victim whose body is the probe `temp &= array2[array1[x] * 512]` leaves
the architectural state unchanged and adds the page of the secret byte to the cache. Starting from a cleared
probe array (the paper flushes all 256 pages first), the reload phase, timing the pages in the order
`mixIdx`, finds exactly that one page, so two runs have the same reload hits exactly when the secret bytes
agree (mod 256). From an initially populated cache nothing is claimed beyond the first part. -/
@[expose] def VictimLeak : Prop :=
  (∀ (W : Nat) (t : Speculation.TState) (a : Int), 1 ≤ W →
      t.s.mem t.s.pc = 4 → t.s.mem (t.s.pc + 1) = a - (t.s.pc + 2) →
      (Speculation.branch W true false 1 t).s = t.s ∧
      (Speculation.branch W true false 1 t).touched = (t.s.mem a % 256) :: t.touched) ∧
  (∀ (W : Nat) (t : Speculation.TState) (a : Int), 1 ≤ W → t.touched = [] →
      t.s.mem t.s.pc = 4 → t.s.mem (t.s.pc + 1) = a - (t.s.pc + 2) →
      Speculation.probeHits (Speculation.branch W true false 1 t).touched = [(t.s.mem a % 256).toNat]) ∧
  (∀ (W : Nat) (t1 t2 : Speculation.TState) (a : Int), 1 ≤ W →
      t1.touched = [] → t2.touched = [] →
      t1.s.mem t1.s.pc = 4 → t2.s.mem t2.s.pc = 4 →
      t1.s.mem (t1.s.pc + 1) = a - (t1.s.pc + 2) → t2.s.mem (t2.s.pc + 1) = a - (t2.s.pc + 2) →
      (Speculation.probeHits (Speculation.branch W true false 1 t1).touched =
        Speculation.probeHits (Speculation.branch W true false 1 t2).touched ↔
        t1.s.mem a % 256 = t2.s.mem a % 256))

/-- C25 (Sec. 3, Tables 1-2, Fig. 4): the speculation depth, for a hidden computation of `k` steps followed by
one probe. Touch-trace boundary (any initial cache): the probe's page is added to the touch trace exactly
when the window covers all `k + 1` steps. Observable leak (cleared probe array, as the PoC flushes it): the
reload finds no page when `W <= k` and exactly the probed page when `W >= k + 1`. Monotonicity: the touch
trace of a longer window extends that of a shorter one (the earlier touches are kept). -/
@[expose] def WindowDepth : Prop :=
  (∀ (k : Nat) (s u : WE.State) (l : List Int), WE.run k s = (WE.Status.running, u) → u.mem u.pc = 4 →
      (∀ W, W ≤ k → (Speculation.branch W true false (k + 1) ⟨s, l⟩).touched = l) ∧
      (∀ W, k + 1 ≤ W → (Speculation.branch W true false (k + 1) ⟨s, l⟩).touched =
        (u.mem (u.pc + 2 + u.mem (u.pc + 1)) % 256) :: l)) ∧
  (∀ (k : Nat) (s u : WE.State), WE.run k s = (WE.Status.running, u) → u.mem u.pc = 4 →
      (∀ W, W ≤ k → Speculation.probeHits (Speculation.branch W true false (k + 1) ⟨s, []⟩).touched = []) ∧
      (∀ W, k + 1 ≤ W → Speculation.probeHits (Speculation.branch W true false (k + 1) ⟨s, []⟩).touched =
        [(u.mem (u.pc + 2 + u.mem (u.pc + 1)) % 256).toNat])) ∧
  (∀ (W d n : Nat) (t : Speculation.TState), ∃ l,
      (Speculation.branch (W + d) true false n t).touched = l ++ (Speculation.branch W true false n t).touched)

/-- C26 (Secs. 3-4): the hidden state. On the transient machine, `n` Write-Execute steps without a probe
compute exactly the ideal Write-Execute run and leave the touch trace unchanged; a mispredicted body of `n`
such steps with a window `W >= n` is squashed without any trace (architectural state and touch trace both
restored). Every Turing computation of `n` steps is carried out on the transient machine in `n (Q + 2)`
steps in the same way. -/
@[expose] def HiddenComputation : Prop :=
  (∀ (n : Nat) (s u : WE.State) (l : List Int), WE.run n s = (WE.Status.running, u) →
      Speculation.trun n ⟨s, l⟩ = (WE.Status.running, ⟨u, l⟩) ∧
      ∀ W, n ≤ W → Speculation.branch W true false n ⟨s, l⟩ = ⟨s, l⟩) ∧
  (∀ (A Q : Nat) (M : TM.Machine A Q) (cfg cfg' : TM.Configuration A Q) (n : Nat) (l : List Int),
      TM.run M n cfg = some cfg' →
      Speculation.trun (n * (Q + 2)) ⟨Universal.encode M cfg, l⟩ =
        (WE.Status.running, ⟨Universal.encode M cfg', l⟩))

/-- Self-Spectre under the leakage contract: mistraining, victim leak, window depth, hidden computation. -/
@[expose] def SelfSpectre : Prop := Mistraining ∧ VictimLeak ∧ WindowDepth ∧ HiddenComputation

end WriteExecute.Paper
