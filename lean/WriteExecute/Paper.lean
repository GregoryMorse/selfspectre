module
public import WriteExecute.Spec.Paper
public import WriteExecute.Model.ReadFree
public import WriteExecute.Model.Confinement
public import WriteExecute.Model.Lookup
public import WriteExecute.Universal.Unbounded
public import WriteExecute.Universal.Bounded
public import WriteExecute.Arith.Tables
public import WriteExecute.Arith.Add
public import WriteExecute.Arith.Sub
public import WriteExecute.Arith.Shift
public import WriteExecute.Arith.Mul
public import WriteExecute.Arith.Div
public import WriteExecute.Arith.Reduce
public import WriteExecute.Arith.ModExp
public import WriteExecute.AES.Checks
public import WriteExecute.AES.Basic
public import WriteExecute.AES.Equiv
public import WriteExecute.AES.Vectors
public import WriteExecute.Spectre.Mix
public import WriteExecute.Spectre.Select
public import WriteExecute.Speculation.Contract

public section

/-! Proofs of the selected statement `Spec/Paper.lean`, each from the development's existing theorems. -/

namespace WriteExecute.Paper

open WriteExecute

theorem readFree : ReadFree := fun s => WE.step_eq_effect s

theorem turingComplete : TuringComplete := by
  intro A Q M cfg
  exact ⟨Universal.halts_iff M cfg, Universal.diverges_iff M cfg, Universal.never_faults M cfg,
    fun n cfg' h => Universal.simulate M n cfg cfg' h,
    fun input => ⟨Universal.universal_halts_iff M input, Universal.universal_diverges_iff M input⟩⟩

theorem finiteRealization : FiniteRealization := by
  intro A Q M N
  exact ⟨fun n cfg cfg' h hin => Universal.bounded_simulate M N n cfg cfg' h hin,
    fun cfg fin n hn hs hin hfin => Universal.bounded_halts M N cfg fin n hn hs hin hfin,
    fun cfg fin fin' n hn hs hin hfin hout => Universal.bounded_faults M N cfg fin fin' n hn hs hin hfin hout⟩

theorem confinement : Confinement := by
  intro A s0 hc n s h
  have i := WE.confinement hc n s h
  exact ⟨i.pc, i.fetch, i.off, i.tgt⟩

theorem primitives : Primitives :=
  ⟨fun m c e res ret f hj hd h1 h2 h3 h4 h5 hr3 hr4 =>
      WE.lookup_correct m c e res ret f hj hd h1 h2 h3 h4 h5 hr3 hr4,
    Arith.tNot_spec, Arith.tNZ_spec, Arith.shl_split,
    fun o i h ho hi hh => Arith.shl_xor o i h ho hi hh,
    Arith.shr_split,
    fun o a j ho ha hj => Arith.shr_xor o a j ho ha hj,
    fun i hi => Arith.inc_spec i hi, fun i hi => Arith.dec_spec i hi,
    fun a b ha hb => Arith.sub_spec a b ha hb, Arith.addLo_spec,
    fun a b ha hb => Arith.addCry_spec a b ha hb⟩

theorem arithmetic : Arithmetic :=
  ⟨Arith.addN_spec, Arith.subN_spec, Arith.shlN_spec, Arith.shrN_spec, Arith.xorN_spec,
    fun x y hy => Arith.mul32_spec x y hy, fun x y hx hy => Arith.mul32_exact x y hx hy,
    fun x y hx hy0 hy => Arith.doDivision_spec x y hx hy0 hy,
    fun a b m hm => Arith.mulmodFixed_spec a b m hm, Arith.mulmodLegacy_wrong,
    fun b e m hm he => Arith.modexpAsm_spec b e m hm he,
    fun b e m hm he => Arith.modexpRef_spec b e m hm he,
    fun b e m hm => Arith.modexpNaive_spec b e m hm,
    fun e h1 h2 => Arith.mulCount_log2 e h1 h2⟩

theorem aesResult : AESResult :=
  ⟨AES.sbox_alg, AES.te4_lit,
    fun w pt hpt hb idx hidx => AES.weCipher_eq w pt hpt hb idx hidx, AES.fips197_c1⟩

theorem mistraining : Mistraining :=
  ⟨fun P k hP hk s0 j h6 hj => Speculation.mistrain P k hP hk s0 j h6 hj,
    fun j t m size ht hm => Speculation.select_guard_32 j t m size ht hm,
    fun j t m size ht hm => Speculation.select_guard_64 j t m size ht hm,
    Speculation.counter2_trains⟩

theorem victimLeak : VictimLeak := by
  refine ⟨fun W t a hW h4 hr => ?_, fun W t a hW hc h4 hr => ?_,
    fun W t1 t2 a hW hc1 hc2 h41 h42 hr1 hr2 => ?_⟩
  · rw [Speculation.branch_one W hW t a h4 hr]
    exact ⟨rfl, rfl⟩
  · rw [Speculation.branch_one W hW t a h4 hr, hc]
    exact Speculation.hits_single _
  · rw [Speculation.branch_one W hW t1 a h41 hr1, Speculation.branch_one W hW t2 a h42 hr2, hc1, hc2,
      Speculation.hits_single, Speculation.hits_single]
    have h1 : 0 ≤ t1.s.mem a % 256 := by omega
    have h2 : 0 ≤ t2.s.mem a % 256 := by omega
    simp only [List.cons.injEq, and_true]
    omega

theorem windowDepth : WindowDepth :=
  ⟨fun k s u l h h4 => Speculation.leak_after k s u l h h4,
    fun W d n t => Speculation.branch_mono W d n t⟩

theorem hiddenComputation : HiddenComputation :=
  ⟨fun n s u l h => Speculation.hidden n s u l h,
    fun A Q M cfg cfg' n l h =>
      Speculation.trun_run (n * (Q + 2)) _ _ l (Universal.simulate M n cfg cfg' h)⟩

theorem selfSpectre : SelfSpectre := ⟨mistraining, victimLeak, windowDepth, hiddenComputation⟩

/-- Supporting (not selected): C19-C20, index arithmetic of the paper's Fig. 1 and probe order. -/
theorem spectreArithmetic :
    (∀ (j : Nat) (t m : BitVec 32), Spectre.selectIdx 32 j t m = if j % 6 = 0 then m else t) ∧
    (∀ (j : Nat) (t m : BitVec 64), Spectre.selectIdx 64 j t m = if j % 6 = 0 then m else t) ∧
    (∀ i, i < 256 → Spectre.mixIdx i < 256) ∧
    (∀ a b, a < 256 → b < 256 → Spectre.mixIdx a = Spectre.mixIdx b → a = b) ∧
    (∀ j, j < 256 → ∃ i, i < 256 ∧ Spectre.mixIdx i = j) :=
  ⟨Spectre.select_32, Spectre.select_64, fun i hi => (Spectre.mix_perm i hi).1,
    Spectre.mix_injective, Spectre.mix_surjective⟩

end WriteExecute.Paper
