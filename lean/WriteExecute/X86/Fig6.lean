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

/-- Writing word `w` at `+4` of a `mov word ptr [disp32], imm16` whose displacement is `c + 256 w0`, `c < 256`
(replacing the middle bytes of `disp32`) gives displacement `c + 256 w`. -/
theorem patch_movW_dispmid (m : Mem) (a c w0 w i : Nat) (hc : c < 256) (hw0 : w0 < 65536) (hw : w < 65536)
    (h : Code m a (enc (.movW (c + 256 * w0) i))) :
    Code (wr m (a + 4) 2 w) a (enc (.movW (c + 256 * w) i)) := by
  rw [enc_movW_dispmid c w0 i hc hw0] at h
  have := Code_patch m [0x66, 0xC7, 0x05, c] ([0] ++ le 2 i) 2 w0 w a (a + 4) (by simp) h
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

/-- The copy loop of `WriteExecXOR` (x64), seven steps from `xorargshl1` (`H1 = A + 90`): the first pass stores
`32 k1` into the `rel32` of `xorj`, retargets the store at `xorargshl2`, and loops back through `xorhead`, which
disables the loop; the second pass stores `32 k1` into the middle of the displacement of `xorargshl2`. -/
theorem xor_loop_x64 (m : Mem) (A k1 : Nat) (hk : k1 < 256) (hbig : A + 200 < 2 ^ 30)
    (c1 : Code m (A + 90) (enc (.movW (fld Mode.x64 (A + 90) 9 (A + 122)) (k1 * 32))))
    (c2 : Code m (A + 99) (enc (.movD (fld Mode.x64 (A + 99) 10 (A + 93)) (fld Mode.x64 (A + 90) 9 (A + 115)))))
    (c3 : Code m (A + 109) (enc (.jmp8 228)))
    (c4 : Code m (A + 83) (enc (.movB (fld Mode.x64 (A + 83) 7 (A + 110)) 0))) :
    runN Mode.x64 7 (A + 90, m) = some (A + 111,
      wr (wr (wr (wr (wr m (A + 122) 2 (k1 * 32)) (A + 93) 4 (fld Mode.x64 (A + 90) 9 (A + 115)))
        (A + 110) 1 0) (A + 115) 2 (k1 * 32)) (A + 93) 4 (fld Mode.x64 (A + 90) 9 (A + 115))) := by
  have hv : k1 * 32 < 65536 := by omega
  let V2 := fld Mode.x64 (A + 90) 9 (A + 115)
  have hV2 : V2 < 2 ^ 32 := fld_lt _ _ _ _ (by omega)
  let ma := wr m (A + 122) 2 (k1 * 32)
  let mb := wr ma (A + 93) 4 V2
  let mc := wr mb (A + 110) 1 0
  let md := wr mc (A + 115) 2 (k1 * 32)
  let me := wr md (A + 93) 4 V2
  have s1 : step Mode.x64 (A + 90, m) = some (A + 99, ma) :=
    step_movW Mode.x64 m (A + 90) (A + 122) _ (by omega) (by omega) hv c1
  have ca2 : Code ma (A + 99) (enc (.movD (fld Mode.x64 (A + 99) 10 (A + 93)) V2)) :=
    Code_frame' c2 (by fz)
  have s2 : step Mode.x64 (A + 99, ma) = some (A + 109, mb) :=
    step_movD Mode.x64 ma (A + 99) (A + 93) _ (by omega) (by omega) hV2 ca2
  have cb3 : Code mb (A + 109) (enc (.jmp8 228)) := Code_frame' (Code_frame' c3 (by fz)) (by fz)
  have s3 : step Mode.x64 (A + 109, mb) = some (A + 83, mb) := by
    have := step_jmp8_neg Mode.x64 mb (A + 109) 228 (by omega) (by omega) (by omega) cb3
    rw [this, show A + 109 + 2 + 228 - 256 = A + 83 by omega]
  have cb4 : Code mb (A + 83) (enc (.movB (fld Mode.x64 (A + 83) 7 (A + 110)) 0)) :=
    Code_frame' (Code_frame' c4 (by fz)) (by fz)
  have s4 : step Mode.x64 (A + 83, mb) = some (A + 90, mc) :=
    step_movB Mode.x64 mb (A + 83) (A + 110) 0 (by omega) (by omega) (by omega) cb4
  have cb1 : Code mb (A + 90) (enc (.movW V2 (k1 * 32))) := by
    have := patch_movW_disp ma (A + 90) _ V2 (k1 * 32) (Code_frame' c1 (by fz))
    rw [show A + 90 + 3 = A + 93 by omega] at this
    exact this
  have cc1 : Code mc (A + 90) (enc (.movW (fld Mode.x64 (A + 90) 9 (A + 115)) (k1 * 32))) :=
    Code_frame' cb1 (by fz)
  have s5 : step Mode.x64 (A + 90, mc) = some (A + 99, md) :=
    step_movW Mode.x64 mc (A + 90) (A + 115) _ (by omega) (by omega) hv cc1
  have cd2 : Code md (A + 99) (enc (.movD (fld Mode.x64 (A + 99) 10 (A + 93)) V2)) :=
    Code_frame' (Code_frame' (Code_frame' ca2 (by fz)) (by fz)) (by fz)
  have s6 : step Mode.x64 (A + 99, md) = some (A + 109, me) :=
    step_movD Mode.x64 md (A + 99) (A + 93) _ (by omega) (by omega) hV2 cd2
  have ce3 : Code me (A + 109) (enc (.jmp8 0)) := by
    have := patch_jmp8 mb (A + 109) 228 0 (by omega) (by omega) cb3
    rw [show A + 109 + 1 = A + 110 by omega] at this
    exact Code_frame' (Code_frame' this (by fz)) (by fz)
  have s7 : step Mode.x64 (A + 109, me) = some (A + 111, me) := by
    have := step_jmp8 Mode.x64 me (A + 109) 0 (by omega) ce3
    rw [this, show A + 109 + 2 + 0 = A + 111 by omega]
  simp only [runN, s1, s2, s3, s4, s5, s6, s7, Option.bind_some]
  rfl

/-- The tail of `WriteExecXOR` (x64), seven steps from `xorargshl2` (`H2 = A + 111`): the store patches the `rel32` of
the group jump `xorarg1_{k1}` with `16 k2`, `xorj` jumps to that group (stride `8192`), the group jumps to
entry `k2`, which stores `k1 xor k2` into `xorres`, which stores it at `Dd` and returns to `Dd - 1`. -/
theorem xor_tail_x64 (m : Mem) (A k1 k2 N Dd v0 b0 : Nat) (hk1 : k1 < 256) (hk2 : k2 < 256)
    (hbig : A + 2 ^ 22 < 2 ^ 30) (hN : N = A + 125 + 2 ^ 21) (hDd : N + 12 ≤ Dd) (hDb : Dd + 1 < 2 ^ 30)
    (hv0 : v0 < 65536) (hb0 : b0 < 256)
    (t1 : Code m (A + 111) (enc (.movW (fld Mode.x64 (A + 111) 9 (A + 126 + 8192 * k1)) (k2 * 16))))
    (t2 : Code m (A + 120) (enc (.jmp32 (jrel (A + 120) (A + 125 + 8192 * k1)))))
    (t3 : Code m (A + 125 + 8192 * k1) (enc (.jmp32 v0)))
    (t4 : Code m (A + 125 + 8192 * k1 + 5 + 16 * k2)
      (enc (.movB (fld Mode.x64 (A + 125 + 8192 * k1 + 5 + 16 * k2) 7 (N + 6)) (k1 ^^^ k2)) ++
        enc (.jmp32 (jrel (A + 125 + 8192 * k1 + 5 + 16 * k2 + 7) N))))
    (tN : Code m N (enc (.movB (fld Mode.x64 N 7 Dd) b0)))
    (tR : Code m (N + 7) (enc (.jmp32 (jrel (N + 7) (Dd - 1))))) :
    runN Mode.x64 7 (A + 111, m) = some (Dd - 1,
      wr (wr (wr m (A + 126 + 8192 * k1) 2 (k2 * 16)) (N + 6) 1 (k1 ^^^ k2)) Dd 1 (k1 ^^^ k2)) := by
  have hx : k1 ^^^ k2 < 256 := by
    have := Nat.xor_lt_two_pow (n := 8) (x := k1) (y := k2) (by omega) (by omega)
    simpa using this
  have hw : k2 * 16 < 65536 := by omega
  let ma := wr m (A + 126 + 8192 * k1) 2 (k2 * 16)
  let mc := wr ma (N + 6) 1 (k1 ^^^ k2)
  let md := wr mc Dd 1 (k1 ^^^ k2)
  have s1 : step Mode.x64 (A + 111, m) = some (A + 120, ma) :=
    step_movW Mode.x64 m (A + 111) (A + 126 + 8192 * k1) _ (by omega) (by omega) hw t1
  have ca2 : Code ma (A + 120) (enc (.jmp32 (jrel (A + 120) (A + 125 + 8192 * k1)))) :=
    Code_frame' t2 (by fz)
  have s2 : step Mode.x64 (A + 120, ma) = some (A + 125 + 8192 * k1, ma) :=
    step_jmp32_to Mode.x64 ma (A + 120) _ (by omega) (by omega) ca2
  have ca3 : Code ma (A + 125 + 8192 * k1) (enc (.jmp32 (k2 * 16))) := by
    have := patch_jmp32_word m (A + 125 + 8192 * k1) v0 (k2 * 16) hv0 hw t3
    rw [show A + 125 + 8192 * k1 + 1 = A + 126 + 8192 * k1 by omega] at this
    exact this
  have s3 : step Mode.x64 (A + 125 + 8192 * k1, ma) = some (A + 125 + 8192 * k1 + 5 + 16 * k2, ma) := by
    have := step_jmp32 Mode.x64 ma (A + 125 + 8192 * k1) (k2 * 16) (by omega) ca3
    rw [this, show A + 125 + 8192 * k1 + 5 + k2 * 16 = A + 125 + 8192 * k1 + 5 + 16 * k2 by omega]
  obtain ⟨e1, e2⟩ := (Code_append m _ _ _).1 t4
  rw [enc_len] at e2
  simp only [Ins.len] at e2
  have ca4 : Code ma (A + 125 + 8192 * k1 + 5 + 16 * k2)
      (enc (.movB (fld Mode.x64 (A + 125 + 8192 * k1 + 5 + 16 * k2) 7 (N + 6)) (k1 ^^^ k2))) :=
    Code_frame' e1 (by fz)
  have s4 : step Mode.x64 (A + 125 + 8192 * k1 + 5 + 16 * k2, ma) =
      some (A + 125 + 8192 * k1 + 5 + 16 * k2 + 7, mc) :=
    step_movB Mode.x64 ma _ (N + 6) _ (by omega) (by omega) hx ca4
  have cc5 : Code mc (A + 125 + 8192 * k1 + 5 + 16 * k2 + 7)
      (enc (.jmp32 (jrel (A + 125 + 8192 * k1 + 5 + 16 * k2 + 7) N))) :=
    Code_frame' (Code_frame' e2 (by fz)) (by fz)
  have s5 : step Mode.x64 (A + 125 + 8192 * k1 + 5 + 16 * k2 + 7, mc) = some (N, mc) :=
    step_jmp32_to Mode.x64 mc _ N (by omega) (by omega) cc5
  have cc6 : Code mc N (enc (.movB (fld Mode.x64 N 7 Dd) (k1 ^^^ k2))) :=
    patch_movB_imm ma N _ b0 _ hb0 hx (Code_frame' tN (by fz))
  have s6 : step Mode.x64 (N, mc) = some (N + 7, md) :=
    step_movB Mode.x64 mc N Dd _ (by omega) (by omega) hx cc6
  have cd7 : Code md (N + 7) (enc (.jmp32 (jrel (N + 7) (Dd - 1)))) :=
    Code_frame' (Code_frame' (Code_frame' tR (by fz)) (by fz)) (by fz)
  have s7 : step Mode.x64 (N + 7, md) = some (Dd - 1, md) :=
    step_jmp32_to Mode.x64 md (N + 7) (Dd - 1) (by omega) (by omega) cd7
  simp only [runN, s1, s2, s3, s4, s5, s6, s7, Option.bind_some]
  rfl

end WriteExecute.X86
