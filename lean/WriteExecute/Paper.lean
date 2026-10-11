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

theorem spectreArithmetic : SpectreArithmetic :=
  ⟨Spectre.select_32, Spectre.select_64, fun i hi => (Spectre.mix_perm i hi).1,
    Spectre.mix_injective, Spectre.mix_surjective⟩

end WriteExecute.Paper
