module
public import WriteExecute.X86.LayoutData

public section

namespace WriteExecute.X86

/-- C17 (Fig. 7), the conditional jump. After SHL1 has stored `2c` (`c ∈ {0,1}`) into the low word of the
`rel32` of `carryNretval: jmp nocryN+8000h`, the jump lands on `nocryN + 2c`: for `c = 0` on the 2-byte
short jump `nocryN` (to the copy loop), for `c = 1` just past it, on `hascarryN`. -/
theorem carry_branch (mode : Mode) (m : Mem) (C r c : Nat) (hc : c ≤ 1) (hr : r < 128)
    (hC : C + 20 < 2 ^ 30)
    (hj : Code m C (enc (.jmp32 32768))) (hn : Code m (C + 5) (enc (.jmp8 r))) :
    let m' := wr m (C + 1) 2 (2 * c)
    step mode (C, m') = some (C + 5 + 2 * c, m') ∧
    (c = 0 → runN mode 2 (C, m') = some (C + 7 + r, m')) ∧
    (c = 1 → C + 5 + 2 * c = C + 7) := by
  intro m'
  have hj' : Code m' C (enc (.jmp32 (2 * c))) :=
    patch_jmp32_word m C 32768 (2 * c) (by omega) (by omega) hj
  have s1 := step_jmp32 mode m' C (2 * c) (by omega) hj'
  refine ⟨by rw [s1], fun h0 => ?_, fun h1 => by omega⟩
  subst h0
  have hn' : Code m' (C + 5) (enc (.jmp8 r)) :=
    Code_frame' hn (by simp only [Ins.len]; omega)
  have s2 := step_jmp8 mode m' (C + 5) r hr hn'
  have s1' : step mode (C, m') = some (C + 5, m') := by simpa using s1
  simp only [runN, s1', s2, Option.bind_some]

end WriteExecute.X86
