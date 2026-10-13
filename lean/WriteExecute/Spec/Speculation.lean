module
public import WriteExecute.Spec.Machine
public import WriteExecute.Spec.Spectre

public section

namespace WriteExecute.Speculation

open WriteExecute

/-! A leakage-contract model of the paper's Self-Spectre half (Sections 2 and 3). It does not model any
processor. It states what the hardware is *assumed* to do, as in hardware-software leakage contracts:

* a conditional branch is guessed by a predictor, which is a parameter;
* when the guess is "taken" but the guard is false, the body runs on the wrong path for at most `W`
  steps (the speculation window, a parameter);
* the wrong path is squashed: the architectural state is restored, but the cache keeps the pages the
  wrong path touched.

Pipelines, caches, timings and the window size of real processors are not specified here. -/

/-- Machine state of the contract machine: the Write-Execute state and the probe-array pages brought into
the cache (newest first; page `v` is the 512-byte page `array2[v * 512]`). -/
structure TState where
  s : WE.State
  touched : List Int

/-- One transient step. Opcode `4`, `[4, rel]`, is the probe `temp &= array2[mem[pc + 2 + rel] * 512]`: it
reads one word and brings the page indexed by its low byte into the cache. Every other word is a
Write-Execute instruction, so a transient run reads nothing but its fetch window until it probes. -/
@[expose] def tstep (t : TState) : WE.Status × TState :=
  if t.s.mem t.s.pc = 4 then
    (.running, ⟨⟨t.s.pc + 2, t.s.mem⟩, (t.s.mem (t.s.pc + 2 + t.s.mem (t.s.pc + 1)) % 256) :: t.touched⟩)
  else
    ((WE.step t.s).1, ⟨(WE.step t.s).2, t.touched⟩)

/-- Run at most `n` transient steps, stopping at the first non-running status. -/
@[expose] def trun : Nat → TState → WE.Status × TState
  | 0, t => (.running, t)
  | n + 1, t =>
    match tstep t with
    | (.running, u) => trun n u
    | r => r

/-- A conditional branch whose guarded body has at most `n` steps. `pred` is the predictor's guess and
`actual` the value of the guard. A true guard runs the body architecturally. A false guard guessed
"taken" runs the body on the wrong path for at most `W` steps and then squashes it: the architectural
state is restored and only the cache footprint survives. A false guard guessed "not taken" does nothing. -/
@[expose] def branch (W : Nat) (pred actual : Bool) (n : Nat) (t : TState) : TState :=
  if actual then (trun n t).2
  else if pred then ⟨t.s, (trun (min W n) t).2.touched⟩
  else t

/-- A branch predictor: an abstract state, a guess and an update. -/
structure Predictor where
  S : Type
  predict : S → Bool
  update : S → Bool → S

@[expose] def Predictor.after (P : Predictor) (s : P.S) (l : List Bool) : P.S := l.foldl P.update s

/-- The mistraining assumption: after `k` or more consecutive "taken" outcomes the predictor guesses
"taken", whatever its earlier history. -/
@[expose] def Predictor.Trains (P : Predictor) (k : Nat) : Prop :=
  ∀ (s : P.S) (m : Nat), k ≤ m → P.predict (P.after s (List.replicate m true)) = true

/-- The textbook 2-bit saturating counter's update. -/
@[expose] def ctrUpdate (c : Nat) (b : Bool) : Nat := if b then min 3 (c + 1) else c - 1

/-- The textbook 2-bit saturating counter (an example of a predictor satisfying the assumption). -/
@[expose] def counter2 : Predictor := ⟨Nat, fun c => decide (2 ≤ c), ctrUpdate⟩

/-- Fig. 1's schedule: the call with loop variable `j` uses the malicious index exactly when `j % 6 = 0`,
so its guard `x < array1_size` is false exactly then. -/
@[expose] def guardAt (j : Nat) : Bool := decide (j % 6 ≠ 0)

/-- The guards of the calls made before the call with loop variable `j` in one round of the PoC's
training loop `for (j = 29; j >= 0; j--)` (spectre.c): the calls with loop variables `29, 28, ..., j + 1`,
in time order. -/
@[expose] def historyBefore (j : Nat) : List Bool := (List.range (29 - j)).map (fun i => guardAt (29 - i))

/-- Reload phase: the 256 pages are timed in the order `mixIdx i`; the pages found in the cache. -/
@[expose] def probeHits (touched : List Int) : List Nat :=
  (List.range 256).filterMap (fun i =>
    if touched.contains ((Spectre.mixIdx i : Nat) : Int) then some (Spectre.mixIdx i) else none)

end WriteExecute.Speculation
