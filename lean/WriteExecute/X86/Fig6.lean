module
public import WriteExecute.X86.NotTable

public section

namespace WriteExecute.X86

/-! Fig. 6: the XOR double lookup and the re-executable copy loop of `WriteExecXOR`. -/

theorem enc_jmp32_mid (v : Nat) (hv : v < 65536) :
    enc (.jmp32 (256 * v)) = [0xE9, 0] ++ le 2 v ++ [0] := by
  simp only [enc, le]
  simp only [List.cons.injEq, List.cons_append, List.nil_append, true_and, and_true]
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- Writing word `w` at `+2` of `jmp 256*v` (the middle two bytes of `rel32`) gives `jmp 256*w`. -/
theorem patch_jmp32_mid (m : Mem) (a v w : Nat) (hv : v < 65536) (hw : w < 65536)
    (h : Code m a (enc (.jmp32 (256 * v)))) :
    Code (wr m (a + 2) 2 w) a (enc (.jmp32 (256 * w))) := by
  rw [enc_jmp32_mid v hv] at h
  have := Code_patch m [0xE9, 0] [0] 2 v w a (a + 2) (by simp) h
  rw [enc_jmp32_mid w hw]; exact this

theorem enc_movW_dispmid (c w i : Nat) (hc : c < 256) (hw : w < 65536) :
    enc (.movW (c + 256 * w) i) = [0x66, 0xC7, 0x05, c] ++ le 2 w ++ ([0] ++ le 2 i) := by
  simp only [enc, le]
  simp only [List.cons.injEq, List.cons_append, List.nil_append, true_and, and_true]
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- Writing word `w` at `+4` of a `mov word ptr [disp32], imm16` whose displacement is `c < 256` (the middle
bytes of `disp32`) gives displacement `c + 256 w`. -/
theorem patch_movW_dispmid (m : Mem) (a c w i : Nat) (hc : c < 256) (hw : w < 65536)
    (h : Code m a (enc (.movW c i))) :
    Code (wr m (a + 4) 2 w) a (enc (.movW (c + 256 * w) i)) := by
  have h0 : Code m a (enc (.movW (c + 256 * 0) i)) := by simpa using h
  rw [enc_movW_dispmid c 0 i hc (by omega)] at h0
  have := Code_patch m [0x66, 0xC7, 0x05, c] ([0] ++ le 2 i) 2 0 w a (a + 4) (by simp) h0
  rw [enc_movW_dispmid c w i hc hw]; exact this



theorem Code_wr_out {m : Mem} {e n v a : Nat} {bs : List Nat} (hd : a + bs.length ≤ e ∨ e + n ≤ a)
    (h : Code m a bs) : Code (wr m e n v) a bs := Code_frame m e n v bs a h hd

/-- Carry a `Code` fact over any number of writes that miss it. -/
macro "cfr" : tactic => `(tactic| (repeat' (first | assumption |
  (refine Code_wr_out (by simp only [List.length_append, enc_len, Ins.len, List.length_replicate, jmpTo_length, ↓reduceIte]; omega) ?_))))

theorem enc_jmp8_byte (r : Nat) (hr : r < 256) : enc (.jmp8 r) = [0xEB] ++ le 1 r ++ [] := by
  simp only [enc, le]; simp [Nat.mod_eq_of_lt hr]

/-- Patching the `rel8` of `jmp8`. -/
theorem patch_jmp8 (m : Mem) (a r r' : Nat) (hr : r < 256) (hr' : r' < 256) (h : Code m a (enc (.jmp8 r))) :
    Code (wr m (a + 1) 1 r') a (enc (.jmp8 r')) := by
  rw [enc_jmp8_byte r hr] at h
  have := Code_patch m [0xEB] [] 1 r r' a (a + 1) (by simp) h
  rw [enc_jmp8_byte r' hr']; exact this

theorem step_jmp8_neg (mode : Mode) (m : Mem) (pc r : Nat) (hr : 128 ≤ r) (hr' : r < 256)
    (hpc : 256 ≤ pc + 2 + r) (h : Code m pc (enc (.jmp8 r))) :
    step mode (pc, m) = some (pc + 2 + r - 256, m) := by
  have hd := decode_enc m pc (.jmp8 r) (by simp [Wf]; omega) h
  have hs : sext 8 r = (r : Int) - 256 := by
    have : ¬ r < 2 ^ (8 - 1) := by omega
    simp only [sext, this, ite_false]; omega
  simp [step, hd, hs, tgt]
  omega

/-- The shared prologue of `xorarg1`/`xorarg2`/`notarg`: patch the argument byte `k` into the table jump, the
destination `D` into the result `mov`, and the return jump; jump to the table of shift-by-`c` entries; nine steps
later execution is at `A + 32` and the word `k * 2^c` has been stored at `D` (and in the result entry). -/
theorem arg_stage (mode : Mode) (m : Mem) (A S R D k c d0 w0 r0 : Nat)
    (hk : k < 256) (hc : c ≤ 7) (hR : R = S + 5 + 65536) (hord : R + 14 ≤ A) (hAD : A + 32 ≤ D)
    (hAb : A + 32 < 2 ^ 30) (hD : D + 2 < 2 ^ 30)
    (i0 : Code m A (enc (.movB (fld mode A 7 (S + 2)) k)))
    (i1 : Code m (A + 7) (enc (.movD (fld mode (A + 7) 10 (R + 3)) (fld mode R 9 D))))
    (i2 : Code m (A + 17) (enc (.movD (fld mode (A + 17) 10 (R + 9 + 1)) (jrel (R + 9) (A + 32)))))
    (i3 : Code m (A + 27) (enc (.jmp32 (jrel (A + 27) S))))
    (iX : Code m S (enc (.jmp32 (256 * 128))))
    (iT : ∀ j, j < 256 → Code m (S + 5 + 256 * j)
      (enc (.movW (fld mode (S + 5 + 256 * j) 9 (R + 7)) (j * 2 ^ c)) ++
        enc (.jmp32 (jrel (S + 5 + 256 * j + 9) R))))
    (iR : Code m R (enc (.movW d0 w0)))
    (iS : Code m (R + 9) (enc (.jmp32 r0))) :
    runN mode 9 (A, m) = some (A + 32,
      wr (wr (wr (wr (wr m (S + 2) 1 k) (R + 3) 4 (fld mode R 9 D)) (R + 9 + 1) 4 (jrel (R + 9) (A + 32)))
        (R + 7) 2 (k * 2 ^ c)) D 2 (k * 2 ^ c)) := by
  have hX : S + 2 ≤ R := by omega
  let m1 := wr m (S + 2) 1 k
  have hm1 : m1 = wr m (S + 2) 1 k := rfl
  let m2 := wr m1 (R + 3) 4 (fld mode R 9 D)
  have hm2 : m2 = wr m1 (R + 3) 4 (fld mode R 9 D) := rfl
  let m3 := wr m2 (R + 9 + 1) 4 (jrel (R + 9) (A + 32))
  have hm3 : m3 = wr m2 (R + 9 + 1) 4 (jrel (R + 9) (A + 32)) := rfl
  have a1 : step mode (A, m) = some (A + 7, m1) :=
    step_movB mode m A (S + 2) k (by omega) (by omega) hk i0
  have c1 : Code m1 (A + 7) (enc (.movD (fld mode (A + 7) 10 (R + 3)) (fld mode R 9 D))) :=
    Code_frame' i1 (by fz)
  have a2 : step mode (A + 7, m1) = some (A + 17, m2) :=
    step_movD mode m1 (A + 7) (R + 3) _ (by omega) (by omega)
      (fld_lt mode R 9 _ (by omega)) c1
  have c2 : Code m2 (A + 17) (enc (.movD (fld mode (A + 17) 10 (R + 9 + 1)) (jrel (R + 9) (A + 32)))) :=
    Code_frame' (Code_frame' i2 (by fz)) (by fz)
  have a3 : step mode (A + 17, m2) = some (A + 27, m3) :=
    step_movD mode m2 (A + 17) (R + 9 + 1) _ (by omega) (by omega) (jrel_lt _ _) c2
  have c3 : Code m3 (A + 27) (enc (.jmp32 (jrel (A + 27) S))) :=
    Code_frame' (Code_frame' (Code_frame' i3 (by fz)) (by fz)) (by fz)
  have a4 : step mode (A + 27, m3) = some (S, m3) :=
    step_jmp32_to mode m3 (A + 27) S (by omega) (by omega) c3
  have A4 : runN mode 4 (A, m) = some (S, m3) := by
    simp only [runN, a1, a2, a3, a4, Option.bind_some]
  have hA : Code m3 S (enc (.jmp32 (256 * k))) :=
    Code_frame' (Code_frame' (patch_jmp32_byte m S 128 k (by omega) hk iX) (by fz)) (by fz)
  have hT : ∀ j, j < 256 → Code m3 (S + 5 + 256 * j)
      (enc (.movW (fld mode (S + 5 + 256 * j) 9 (R + 7)) (j * 2 ^ c)) ++
        enc (.jmp32 (jrel (S + 5 + 256 * j + 9) R))) := fun j hj =>
    Code_frame2 (Code_frame2 (Code_frame2 (iT j hj) (by fz)) (by fz)) (by fz)
  have hR' : Code m3 R (enc (.movW (fld mode R 9 D) w0)) :=
    Code_frame' (patch_movW_disp m1 R d0 _ w0 (Code_frame' iR (by fz))) (by fz)
  have hS' : Code m3 (R + 9) (enc (.jmp32 (jrel (R + 9) (A + 32)))) :=
    patch_jmp32 m2 (R + 9) r0 _ (Code_frame' (Code_frame' iS (by fz)) (by fz))
  have B5 := shl_lookup mode m3 S R k c D w0 (A + 32) hR hk hc (by omega) hD (by omega)
    (Or.inr (by omega)) hA hT hR' hS'
  have e : 9 = 4 + 5 := rfl
  rw [e, runN_add, A4]
  simpa using B5

end WriteExecute.X86
