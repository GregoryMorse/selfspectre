module
public import WriteExecute.Paper
public section
namespace PalomarWE
/-- Principal mathematical claims, each from its existing proof in `WriteExecute.Paper`. -/
theorem mathematical_result : WriteExecute.Paper.ReadFree ∧ WriteExecute.Paper.TuringComplete ∧
    WriteExecute.Paper.FiniteRealization ∧ WriteExecute.Paper.Confinement ∧
    WriteExecute.Paper.Primitives ∧ WriteExecute.Paper.Arithmetic ∧ WriteExecute.Paper.AESResult ∧
    WriteExecute.Paper.SelfSpectre :=
  ⟨WriteExecute.Paper.readFree, WriteExecute.Paper.turingComplete, WriteExecute.Paper.finiteRealization,
    WriteExecute.Paper.confinement, WriteExecute.Paper.primitives, WriteExecute.Paper.arithmetic,
    WriteExecute.Paper.aesResult, WriteExecute.Paper.selfSpectre⟩
end PalomarWE
