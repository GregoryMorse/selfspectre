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

/-- The copy loop of `WriteExecXOR` (both builds), seven steps from `xorargshl1` (`H1 = A + 90`): the first pass stores
`32 k1` into the `rel32` of `xorj`, retargets the store at `xorargshl2`, and loops back through `xorhead`, which
disables the loop; the second pass stores `32 k1` at `T2` (x64: the middle of the displacement of `xorargshl2`; x86: the `rel32` of `xorargshl2jmp`). -/
theorem xor_loop (mode : Mode) (m : Mem) (A J T2 k1 : Nat) (hk : k1 < 256) (hbig : A + 200 < 2 ^ 30)
    (hJ : J < 2 ^ 30) (hJd : J + 2 ≤ A + 83 ∨ A + 111 ≤ J) (hT : T2 < 2 ^ 30) (hTd : T2 + 2 ≤ A + 83 ∨ A + 111 ≤ T2)
    (c1 : Code m (A + 90) (enc (.movW (fld mode (A + 90) 9 J) (k1 * 32))))
    (c2 : Code m (A + 99) (enc (.movD (fld mode (A + 99) 10 (A + 93)) (fld mode (A + 90) 9 T2))))
    (c3 : Code m (A + 109) (enc (.jmp8 228)))
    (c4 : Code m (A + 83) (enc (.movB (fld mode (A + 83) 7 (A + 110)) 0))) :
    runN mode 7 (A + 90, m) = some (A + 111,
      wr (wr (wr (wr (wr m J 2 (k1 * 32)) (A + 93) 4 (fld mode (A + 90) 9 T2))
        (A + 110) 1 0) T2 2 (k1 * 32)) (A + 93) 4 (fld mode (A + 90) 9 T2)) := by
  have hv : k1 * 32 < 65536 := by omega
  let V2 := fld mode (A + 90) 9 T2
  have hV2 : V2 < 2 ^ 32 := fld_lt _ _ _ _ (by omega)
  let ma := wr m J 2 (k1 * 32)
  let mb := wr ma (A + 93) 4 V2
  let mc := wr mb (A + 110) 1 0
  let md := wr mc T2 2 (k1 * 32)
  let me := wr md (A + 93) 4 V2
  have s1 : step mode (A + 90, m) = some (A + 99, ma) :=
    step_movW mode m (A + 90) J _ (by omega) (by omega) hv c1
  have ca2 : Code ma (A + 99) (enc (.movD (fld mode (A + 99) 10 (A + 93)) V2)) :=
    Code_frame' c2 (by fz)
  have s2 : step mode (A + 99, ma) = some (A + 109, mb) :=
    step_movD mode ma (A + 99) (A + 93) _ (by omega) (by omega) hV2 ca2
  have cb3 : Code mb (A + 109) (enc (.jmp8 228)) := Code_frame' (Code_frame' c3 (by fz)) (by fz)
  have s3 : step mode (A + 109, mb) = some (A + 83, mb) := by
    have := step_jmp8_neg mode mb (A + 109) 228 (by omega) (by omega) (by omega) cb3
    rw [this, show A + 109 + 2 + 228 - 256 = A + 83 by omega]
  have cb4 : Code mb (A + 83) (enc (.movB (fld mode (A + 83) 7 (A + 110)) 0)) :=
    Code_frame' (Code_frame' c4 (by fz)) (by fz)
  have s4 : step mode (A + 83, mb) = some (A + 90, mc) :=
    step_movB mode mb (A + 83) (A + 110) 0 (by omega) (by omega) (by omega) cb4
  have cb1 : Code mb (A + 90) (enc (.movW V2 (k1 * 32))) := by
    have := patch_movW_disp ma (A + 90) _ V2 (k1 * 32) (Code_frame' c1 (by fz))
    rw [show A + 90 + 3 = A + 93 by omega] at this
    exact this
  have cc1 : Code mc (A + 90) (enc (.movW (fld mode (A + 90) 9 T2) (k1 * 32))) :=
    Code_frame' cb1 (by fz)
  have s5 : step mode (A + 90, mc) = some (A + 99, md) :=
    step_movW mode mc (A + 90) T2 _ (by omega) (by omega) hv cc1
  have cd2 : Code md (A + 99) (enc (.movD (fld mode (A + 99) 10 (A + 93)) V2)) :=
    Code_frame' (Code_frame' (Code_frame' ca2 (by fz)) (by fz)) (by fz)
  have s6 : step mode (A + 99, md) = some (A + 109, me) :=
    step_movD mode md (A + 99) (A + 93) _ (by omega) (by omega) hV2 cd2
  have ce3 : Code me (A + 109) (enc (.jmp8 0)) := by
    have := patch_jmp8 mb (A + 109) 228 0 (by omega) (by omega) cb3
    rw [show A + 109 + 1 = A + 110 by omega] at this
    exact Code_frame' (Code_frame' this (by fz)) (by fz)
  have s7 : step mode (A + 109, me) = some (A + 111, me) := by
    have := step_jmp8 mode me (A + 109) 0 (by omega) ce3
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

/-! Composition of the three phases. -/

theorem wr_apply_out' (m : Mem) (e n v x : Nat) (h : x < e ∨ e + n ≤ x) : wr m e n v x = m x :=
  wr_apply_out m e n v x (by omega)

/-- A memory that agrees with `m` on the bytes of a code fragment still holds that fragment. -/
theorem Code_ext (m m' : Mem) : ∀ (a : Nat) (bs : List Nat), Code m a bs →
    (∀ x, a ≤ x → x < a + bs.length → m' x = m x) → Code m' a bs
  | _, [], _, _ => trivial
  | a, b :: bs, h, hag => by
    refine ⟨?_, Code_ext m m' (a + 1) bs h.2 (fun x h1 h2 => hag x (by omega) (by simp at h2 ⊢; omega))⟩
    rw [hag a (by omega) (by simp)]; exact h.1

/-- Carry the code fact `h` over any chain of writes that miss it. -/
macro "cext " h:term : tactic => `(tactic| (
  refine Code_ext _ _ _ _ $h ?_
  intro x hx1 hx2
  try simp only [enc_len, Ins.len, List.length_append, List.length_replicate, jmpTo_length] at hx2
  try split at hx2
  all_goals (try simp +zetaDelta (disch := omega) only [wr_apply_out'])))

/-- The image of one `xorarg`/`notarg`-style argument stage (see `arg_stage`). -/
structure ArgImg (mode : Mode) (m : Mem) (A S R D k c d0 w0 r0 : Nat) : Prop where
  i0 : Code m A (enc (.movB (fld mode A 7 (S + 2)) k))
  i1 : Code m (A + 7) (enc (.movD (fld mode (A + 7) 10 (R + 3)) (fld mode R 9 D)))
  i2 : Code m (A + 17) (enc (.movD (fld mode (A + 17) 10 (R + 9 + 1)) (jrel (R + 9) (A + 32))))
  i3 : Code m (A + 27) (enc (.jmp32 (jrel (A + 27) S)))
  iX : Code m S (enc (.jmp32 (256 * 128)))
  iT : ∀ j, j < 256 → Code m (S + 5 + 256 * j)
      (enc (.movW (fld mode (S + 5 + 256 * j) 9 (R + 7)) (j * 2 ^ c)) ++
        enc (.jmp32 (jrel (S + 5 + 256 * j + 9) R)))
  iR : Code m R (enc (.movW d0 w0))
  iS : Code m (R + 9) (enc (.jmp32 r0))

theorem ArgImg.ext {mode : Mode} {m m' : Mem} {A S R D k c d0 w0 r0 : Nat}
    (h : ArgImg mode m A S R D k c d0 w0 r0) (hR : R = S + 5 + 65536)
    (hag : ∀ x, (A ≤ x ∧ x < A + 32) ∨ (S ≤ x ∧ x < R + 14) → m' x = m x) :
    ArgImg mode m' A S R D k c d0 w0 r0 where
  i0 := Code_ext m m' _ _ h.i0 (fun x h1 h2 => hag x (by simp only [enc_len, Ins.len] at h2; omega))
  i1 := Code_ext m m' _ _ h.i1 (fun x h1 h2 => hag x (by simp only [enc_len, Ins.len] at h2; omega))
  i2 := Code_ext m m' _ _ h.i2 (fun x h1 h2 => hag x (by simp only [enc_len, Ins.len] at h2; omega))
  i3 := Code_ext m m' _ _ h.i3 (fun x h1 h2 => hag x (by simp only [enc_len, Ins.len] at h2; omega))
  iX := Code_ext m m' _ _ h.iX (fun x h1 h2 => hag x (by simp only [enc_len, Ins.len] at h2; omega))
  iT := fun j hj => Code_ext m m' _ _ (h.iT j hj) (fun x h1 h2 => hag x (by
    simp only [List.length_append, enc_len, Ins.len] at h2; omega))
  iR := Code_ext m m' _ _ h.iR (fun x h1 h2 => hag x (by simp only [enc_len, Ins.len] at h2; omega))
  iS := Code_ext m m' _ _ h.iS (fun x h1 h2 => hag x (by simp only [enc_len, Ins.len] at h2; omega))

/-- The image of `WriteExecXOR` (x64 build) at the entry `xorarg1 = A` with the wrapper-patched arguments `k1`, `k2`.
Every instruction field that the procedure overwrites may hold any stale value (`d01 .. b0`, `v`), so the procedure is
re-executable; `S5`/`S4` are the `WriteExecSHL5`/`WriteExecSHL4` tables, `N = xorres`, `Dd` the result byte. -/
structure XorImg64 (m : Mem) (A S5 S4 N Dd k1 k2 d01 w01 r01 d02 w02 r02 d1 c1 rL c2s wH wJ b0 : Nat)
    (v : Nat → Nat) : Prop where
  a1 : ArgImg Mode.x64 m A S5 (S5 + 5 + 65536) (A + 97) k1 5 d01 w01 r01
  a2 : ArgImg Mode.x64 m (A + 32) S4 (S4 + 5 + 65536) (A + 118) k2 4 d02 w02 r02
  p1 : Code m (A + 64) (enc (.movD (fld Mode.x64 (A + 64) 10 (A + 93)) (fld Mode.x64 (A + 90) 9 (A + 122))))
  p2 : Code m (A + 74) (enc (.movB (fld Mode.x64 (A + 74) 7 (A + 110)) 228))
  p3 : Code m (A + 81) (enc (.jmp8 7))
  xh : Code m (A + 83) (enc (.movB (fld Mode.x64 (A + 83) 7 (A + 110)) 0))
  h1 : Code m (A + 90) (enc (.movW d1 c1))
  h1b : Code m (A + 99) (enc (.movD (fld Mode.x64 (A + 99) 10 (A + 93)) (fld Mode.x64 (A + 90) 9 (A + 115))))
  xl : Code m (A + 109) (enc (.jmp8 rL))
  h2 : Code m (A + 111) (enc (.movW (6 + 256 * wH) c2s))
  xj : Code m (A + 120) (enc (.jmp32 (256 * wJ)))
  gj : ∀ i, i < 256 → Code m (A + 125 + 8192 * i) (enc (.jmp32 (v i)))
  ent : ∀ i j, i < 256 → j < 256 → Code m (A + 125 + 8192 * i + 5 + 16 * j)
    (enc (.movB (fld Mode.x64 (A + 125 + 8192 * i + 5 + 16 * j) 7 (N + 6)) (i ^^^ j)) ++
      enc (.jmp32 (jrel (A + 125 + 8192 * i + 5 + 16 * j + 7) N)))
  iN : Code m N (enc (.movB (fld Mode.x64 N 7 Dd) b0))
  iRet : Code m (N + 7) (enc (.jmp32 (jrel (N + 7) (Dd - 1))))

/-- C18 (Fig. 6), x64 build of the published `writeexc.asm`: for every pair of argument bytes `k1`, `k2`, execution from
`xorarg1` reaches the return jump target `Dd - 1` after `35` steps, having stored `k1 xor k2` at `Dd`; every write is
to an instruction field. -/
theorem xor_exec_x64 (m : Mem) (A S5 S4 N Dd k1 k2 d01 w01 r01 d02 w02 r02 d1 c1 rL c2s wH wJ b0 : Nat)
    (v : Nat → Nat) (hk1 : k1 < 256) (hk2 : k2 < 256)
    (hord4 : S4 + 5 + 65536 + 14 ≤ S5) (hord5 : S5 + 5 + 65536 + 14 ≤ A)
    (hbig : A + 2 ^ 22 < 2 ^ 30) (hN : N = A + 125 + 2 ^ 21) (hDd : N + 12 ≤ Dd) (hDb : Dd + 1 < 2 ^ 30)
    (hv : ∀ i, i < 256 → v i < 65536) (hwH : wH < 65536) (hwJ : wJ < 65536) (hb0 : b0 < 256)
    (hrL : rL < 256)
    (img : XorImg64 m A S5 S4 N Dd k1 k2 d01 w01 r01 d02 w02 r02 d1 c1 rL c2s wH wJ b0 v) :
    ∃ mEnd, runN Mode.x64 35 (A, m) = some (Dd - 1, mEnd) ∧ mEnd Dd = k1 ^^^ k2 ∧
      ∀ x, ¬(x = S5 + 2 ∨ (S5 + 5 + 65536 + 3 ≤ x ∧ x < S5 + 5 + 65536 + 9) ∨
        (S5 + 5 + 65536 + 10 ≤ x ∧ x < S5 + 5 + 65536 + 14) ∨ x = S4 + 2 ∨
        (S4 + 5 + 65536 + 3 ≤ x ∧ x < S4 + 5 + 65536 + 9) ∨
        (S4 + 5 + 65536 + 10 ≤ x ∧ x < S4 + 5 + 65536 + 14) ∨
        (A + 93 ≤ x ∧ x < A + 99) ∨ x = A + 110 ∨ (A + 115 ≤ x ∧ x < A + 117) ∨ (A + 118 ≤ x ∧ x < A + 120) ∨
        (A + 122 ≤ x ∧ x < A + 124) ∨ (A + 126 + 8192 * k1 ≤ x ∧ x < A + 128 + 8192 * k1) ∨
        x = N + 6 ∨ x = Dd) → mEnd x = m x := by
  have hx : k1 ^^^ k2 < 256 := by
    have := Nat.xor_lt_two_pow (n := 8) (x := k1) (y := k2) (by omega) (by omega)
    simpa using this
  -- stage 1
  let m1a := wr m (S5 + 2) 1 k1
  let m1b := wr m1a (S5 + 5 + 65536 + 3) 4 (fld Mode.x64 (S5 + 5 + 65536) 9 (A + 97))
  let m1c := wr m1b (S5 + 5 + 65536 + 9 + 1) 4 (jrel (S5 + 5 + 65536 + 9) (A + 32))
  let m1d := wr m1c (S5 + 5 + 65536 + 7) 2 (k1 * 2 ^ 5)
  let m1 := wr m1d (A + 97) 2 (k1 * 2 ^ 5)
  have R1 : runN Mode.x64 9 (A, m) = some (A + 32, m1) :=
    arg_stage Mode.x64 m A S5 (S5 + 5 + 65536) (A + 97) k1 5 d01 w01 r01 hk1 (by omega) rfl (by omega)
      (by omega) (by omega) (by omega) img.a1.i0 img.a1.i1 img.a1.i2 img.a1.i3 img.a1.iX img.a1.iT
      img.a1.iR img.a1.iS
  -- stage 2
  have a2' : ArgImg Mode.x64 m1 (A + 32) S4 (S4 + 5 + 65536) (A + 118) k2 4 d02 w02 r02 :=
    img.a2.ext rfl (fun x hx => by simp (disch := omega) only [m1, m1d, m1c, m1b, m1a, wr_apply_out'])
  let m2a := wr m1 (S4 + 2) 1 k2
  let m2b := wr m2a (S4 + 5 + 65536 + 3) 4 (fld Mode.x64 (S4 + 5 + 65536) 9 (A + 118))
  let m2c := wr m2b (S4 + 5 + 65536 + 9 + 1) 4 (jrel (S4 + 5 + 65536 + 9) (A + 32 + 32))
  let m2d := wr m2c (S4 + 5 + 65536 + 7) 2 (k2 * 2 ^ 4)
  let m2 := wr m2d (A + 118) 2 (k2 * 2 ^ 4)
  have R2 : runN Mode.x64 9 (A + 32, m1) = some (A + 32 + 32, m2) :=
    arg_stage Mode.x64 m1 (A + 32) S4 (S4 + 5 + 65536) (A + 118) k2 4 d02 w02 r02 hk2 (by omega) rfl (by omega)
      (by omega) (by omega) (by omega) a2'.i0 a2'.i1 a2'.i2 a2'.i3 a2'.iX a2'.iT a2'.iR a2'.iS
  have hA32 : A + 32 + 32 = A + 64 := by omega
  rw [hA32] at R2
  -- the three patches
  let V1 := fld Mode.x64 (A + 90) 9 (A + 122)
  have hV1 : V1 < 2 ^ 32 := fld_lt _ _ _ _ (by omega)
  let mp1 := wr m2 (A + 93) 4 V1
  let mF := wr mp1 (A + 110) 1 228
  have cp1 : Code m2 (A + 64) (enc (.movD (fld Mode.x64 (A + 64) 10 (A + 93)) V1)) := by
    cext img.p1
  have P1 : step Mode.x64 (A + 64, m2) = some (A + 74, mp1) :=
    step_movD Mode.x64 m2 (A + 64) (A + 93) V1 (by omega) (by omega) hV1 cp1
  have cp2 : Code mp1 (A + 74) (enc (.movB (fld Mode.x64 (A + 74) 7 (A + 110)) 228)) := by
    cext img.p2
  have P2 : step Mode.x64 (A + 74, mp1) = some (A + 81, mF) :=
    step_movB Mode.x64 mp1 (A + 74) (A + 110) 228 (by omega) (by omega) (by omega) cp2
  have cp3 : Code mF (A + 81) (enc (.jmp8 7)) := by
    cext img.p3
  have P3 : step Mode.x64 (A + 81, mF) = some (A + 90, mF) := by
    have := step_jmp8 Mode.x64 mF (A + 81) 7 (by omega) cp3
    rw [this]
  -- the loop
  have cL1 : Code mF (A + 90) (enc (.movW (fld Mode.x64 (A + 90) 9 (A + 122)) (k1 * 32))) := by
    have X1 : Code m1d (A + 90) (enc (.movW d1 c1)) := by cext img.h1
    have X2 : Code m1 (A + 90) (enc (.movW d1 (k1 * 2 ^ 5))) := by
      have := patch_movW_imm m1d (A + 90) d1 c1 (k1 * 2 ^ 5) X1
      rw [show A + 90 + 7 = A + 97 by omega] at this
      exact this
    have X3 : Code m2 (A + 90) (enc (.movW d1 (k1 * 2 ^ 5))) := by cext X2
    have X4 : Code mp1 (A + 90) (enc (.movW V1 (k1 * 2 ^ 5))) := by
      have := patch_movW_disp m2 (A + 90) d1 V1 (k1 * 2 ^ 5) X3
      rw [show A + 90 + 3 = A + 93 by omega] at this
      exact this
    have X5 : Code mF (A + 90) (enc (.movW V1 (k1 * 2 ^ 5))) := by cext X4
    exact X5
  have cL2 : Code mF (A + 99) (enc (.movD (fld Mode.x64 (A + 99) 10 (A + 93)) (fld Mode.x64 (A + 90) 9 (A + 115)))) := by
    cext img.h1b
  have cL3 : Code mF (A + 109) (enc (.jmp8 228)) := by
    have := patch_jmp8 mp1 (A + 109) rL 228 hrL (by omega) (by cext img.xl)
    rw [show A + 109 + 1 = A + 110 by omega] at this
    exact this
  have cL4 : Code mF (A + 83) (enc (.movB (fld Mode.x64 (A + 83) 7 (A + 110)) 0)) := by
    cext img.xh
  have RL := xor_loop Mode.x64 mF A (A + 122) (A + 115) k1 hk1 (by omega) (by omega) (by omega) (by omega) (by omega) cL1 cL2 cL3 cL4
  let V2 := fld Mode.x64 (A + 90) 9 (A + 115)
  let ML1 := wr mF (A + 122) 2 (k1 * 32)
  let ML2 := wr ML1 (A + 93) 4 V2
  let ML3 := wr ML2 (A + 110) 1 0
  let ML4 := wr ML3 (A + 115) 2 (k1 * 32)
  let ML5 := wr ML4 (A + 93) 4 V2
  -- the tail
  have t1 : Code ML5 (A + 111) (enc (.movW (fld Mode.x64 (A + 111) 9 (A + 126 + 8192 * k1)) (k2 * 16))) := by
    have Y1 : Code m2d (A + 111) (enc (.movW (6 + 256 * wH) c2s)) := by cext img.h2
    have Y2 : Code m2 (A + 111) (enc (.movW (6 + 256 * wH) (k2 * 2 ^ 4))) := by
      have := patch_movW_imm m2d (A + 111) _ c2s (k2 * 2 ^ 4) Y1
      rw [show A + 111 + 7 = A + 118 by omega] at this
      exact this
    have Y3 : Code ML3 (A + 111) (enc (.movW (6 + 256 * wH) (k2 * 2 ^ 4))) := by cext Y2
    have Y4 : Code ML4 (A + 111) (enc (.movW (6 + 256 * (k1 * 32)) (k2 * 2 ^ 4))) := by
      have := patch_movW_dispmid ML3 (A + 111) 6 wH (k1 * 32) (k2 * 2 ^ 4) (by omega) hwH (by omega) Y3
      rw [show A + 111 + 4 = A + 115 by omega] at this
      exact this
    have Y5 : Code ML5 (A + 111) (enc (.movW (6 + 256 * (k1 * 32)) (k2 * 2 ^ 4))) := by cext Y4
    have e1 : fld Mode.x64 (A + 111) 9 (A + 126 + 8192 * k1) = 6 + 256 * (k1 * 32) := by
      simp only [fld]; omega
    rw [e1]
    exact Y5
  have t2 : Code ML5 (A + 120) (enc (.jmp32 (jrel (A + 120) (A + 125 + 8192 * k1)))) := by
    have Z1 : Code mF (A + 120) (enc (.jmp32 (256 * wJ))) := by cext img.xj
    have Z2 : Code ML1 (A + 120) (enc (.jmp32 (256 * (k1 * 32)))) := by
      have := patch_jmp32_mid mF (A + 120) wJ (k1 * 32) hwJ (by omega) Z1
      rw [show A + 120 + 2 = A + 122 by omega] at this
      exact this
    have Z3 : Code ML5 (A + 120) (enc (.jmp32 (256 * (k1 * 32)))) := by cext Z2
    have e2 : jrel (A + 120) (A + 125 + 8192 * k1) = 256 * (k1 * 32) := by
      simp only [jrel]; omega
    rw [e2]
    exact Z3
  have t3 : Code ML5 (A + 125 + 8192 * k1) (enc (.jmp32 (v k1))) := by cext img.gj k1 hk1
  have t4 : Code ML5 (A + 125 + 8192 * k1 + 5 + 16 * k2)
      (enc (.movB (fld Mode.x64 (A + 125 + 8192 * k1 + 5 + 16 * k2) 7 (N + 6)) (k1 ^^^ k2)) ++
        enc (.jmp32 (jrel (A + 125 + 8192 * k1 + 5 + 16 * k2 + 7) N))) := by
    cext img.ent k1 k2 hk1 hk2
  have tN : Code ML5 N (enc (.movB (fld Mode.x64 N 7 Dd) b0)) := by cext img.iN
  have tR : Code ML5 (N + 7) (enc (.jmp32 (jrel (N + 7) (Dd - 1)))) := by cext img.iRet
  have RT := xor_tail_x64 ML5 A k1 k2 N Dd (v k1) b0 hk1 hk2 hbig hN hDd hDb (hv k1 hk1) hb0 t1 t2 t3 t4 tN tR
  let mEnd := wr (wr (wr ML5 (A + 126 + 8192 * k1) 2 (k2 * 16)) (N + 6) 1 (k1 ^^^ k2)) Dd 1 (k1 ^^^ k2)
  have RA : runN Mode.x64 (9 + (9 + (1 + (1 + (1 + (7 + 7)))))) (A, m) = some (Dd - 1, mEnd) :=
    runN_trans Mode.x64 R1 (runN_trans Mode.x64 R2 (runN_trans Mode.x64 (runN_one _ _ _ P1)
      (runN_trans Mode.x64 (runN_one _ _ _ P2) (runN_trans Mode.x64 (runN_one _ _ _ P3)
        (runN_trans Mode.x64 RL RT)))))
  refine ⟨mEnd, RA, ?_, ?_⟩
  · have : mEnd Dd = (k1 ^^^ k2) / 256 ^ (Dd - Dd) % 256 := wr_apply_in _ _ _ _ _ ⟨Nat.le_refl _, by omega⟩
    rw [this]; simp; omega
  · intro x hx
    simp +zetaDelta (disch := omega) only [wr_apply_out']

/-- The tail of `WriteExecXOR` (x86), ten steps from `xorargshl2jmp` (`A + 111`): the patched jump selects entry `k1`
of the `DEFINEXORJMP` table, which patches the store operand of `xorargshl2` to the group jump `xorarg1_{k1}`; the store
patches that jump with `16 k2`; `xorj` jumps to the group, which jumps to entry `k2`, which stores `k1 xor k2` into
`xorres`, which stores it at `Dd` and returns to `Dd - 1`. -/
theorem xor_tail_x86 (m : Mem) (A k1 k2 N Dd v0 d2 b0 : Nat) (hk1 : k1 < 256) (hk2 : k2 < 256)
    (hbig : A + 2 ^ 22 < 2 ^ 30) (hN : N = A + 8322 + 2 ^ 21) (hDd : N + 12 ≤ Dd) (hDb : Dd + 1 < 2 ^ 30)
    (hv0 : v0 < 65536) (hb0 : b0 < 256)
    (u1 : Code m (A + 111) (enc (.jmp32 (k1 * 32))))
    (u2 : Code m (A + 116 + 32 * k1)
      (enc (.movD (fld Mode.x86 (A + 116 + 32 * k1) 10 (A + 8311)) (A + 8323 + 8192 * k1)) ++
        jmpTo (decide (k1 < 252)) (A + 116 + 32 * k1 + 10) (A + 8308)))
    (u3 : Code m (A + 8308) (enc (.movW d2 (k2 * 16))))
    (u4 : Code m (A + 8317) (enc (.jmp32 (jrel (A + 8317) (A + 8322 + 8192 * k1)))))
    (u5 : Code m (A + 8322 + 8192 * k1) (enc (.jmp32 v0)))
    (u6 : Code m (A + 8322 + 8192 * k1 + 5 + 16 * k2)
      (enc (.movB (fld Mode.x86 (A + 8322 + 8192 * k1 + 5 + 16 * k2) 7 (N + 6)) (k1 ^^^ k2)) ++
        enc (.jmp32 (jrel (A + 8322 + 8192 * k1 + 5 + 16 * k2 + 7) N))))
    (uN : Code m N (enc (.movB (fld Mode.x86 N 7 Dd) b0)))
    (uR : Code m (N + 7) (enc (.jmp32 (jrel (N + 7) (Dd - 1))))) :
    runN Mode.x86 10 (A + 111, m) = some (Dd - 1,
      wr (wr (wr (wr m (A + 8311) 4 (A + 8323 + 8192 * k1)) (A + 8323 + 8192 * k1) 2 (k2 * 16))
        (N + 6) 1 (k1 ^^^ k2)) Dd 1 (k1 ^^^ k2)) := by
  have hx : k1 ^^^ k2 < 256 := by
    have := Nat.xor_lt_two_pow (n := 8) (x := k1) (y := k2) (by omega) (by omega)
    simpa using this
  have hw : k2 * 16 < 65536 := by omega
  let ma := wr m (A + 8311) 4 (A + 8323 + 8192 * k1)
  let mb := wr ma (A + 8323 + 8192 * k1) 2 (k2 * 16)
  let mc := wr mb (N + 6) 1 (k1 ^^^ k2)
  let md := wr mc Dd 1 (k1 ^^^ k2)
  have s1 : step Mode.x86 (A + 111, m) = some (A + 116 + 32 * k1, m) := by
    have := step_jmp32 Mode.x86 m (A + 111) (k1 * 32) (by omega) u1
    rw [this, show A + 111 + 5 + k1 * 32 = A + 116 + 32 * k1 by omega]
  obtain ⟨e1, e2⟩ := (Code_append m _ _ _).1 u2
  rw [enc_len] at e2
  simp only [Ins.len] at e2
  have s2 : step Mode.x86 (A + 116 + 32 * k1, m) = some (A + 116 + 32 * k1 + 10, ma) :=
    step_movD Mode.x86 m _ (A + 8311) _ (by omega) (by omega) (by omega) e1
  have ca3 : Code ma (A + 116 + 32 * k1 + 10) (jmpTo (decide (k1 < 252)) (A + 116 + 32 * k1 + 10) (A + 8308)) := by
    cext e2
  have s3 : step Mode.x86 (A + 116 + 32 * k1 + 10, ma) = some (A + 8308, ma) :=
    step_jmpTo Mode.x86 ma _ _ _ (by omega) (by omega) (fun hn => by
      have : ¬ k1 < 252 := by simpa using hn
      omega) ca3
  have ca4 : Code ma (A + 8308) (enc (.movW (A + 8323 + 8192 * k1) (k2 * 16))) := by
    have := patch_movW_disp m (A + 8308) d2 (A + 8323 + 8192 * k1) (k2 * 16) u3
    rw [show A + 8308 + 3 = A + 8311 by omega] at this
    exact this
  have s4 : step Mode.x86 (A + 8308, ma) = some (A + 8317, mb) :=
    step_movW Mode.x86 ma (A + 8308) (A + 8323 + 8192 * k1) _ (by omega) (by omega) hw ca4
  have cb5 : Code mb (A + 8317) (enc (.jmp32 (jrel (A + 8317) (A + 8322 + 8192 * k1)))) := by cext u4
  have s5 : step Mode.x86 (A + 8317, mb) = some (A + 8322 + 8192 * k1, mb) :=
    step_jmp32_to Mode.x86 mb (A + 8317) _ (by omega) (by omega) cb5
  have cb6 : Code mb (A + 8322 + 8192 * k1) (enc (.jmp32 (k2 * 16))) := by
    have := patch_jmp32_word ma (A + 8322 + 8192 * k1) v0 (k2 * 16) hv0 hw (by cext u5)
    rw [show A + 8322 + 8192 * k1 + 1 = A + 8323 + 8192 * k1 by omega] at this
    exact this
  have s6 : step Mode.x86 (A + 8322 + 8192 * k1, mb) = some (A + 8322 + 8192 * k1 + 5 + 16 * k2, mb) := by
    have := step_jmp32 Mode.x86 mb (A + 8322 + 8192 * k1) (k2 * 16) (by omega) cb6
    rw [this, show A + 8322 + 8192 * k1 + 5 + k2 * 16 = A + 8322 + 8192 * k1 + 5 + 16 * k2 by omega]
  obtain ⟨f1, f2⟩ := (Code_append m _ _ _).1 u6
  rw [enc_len] at f2
  simp only [Ins.len] at f2
  have cb7 : Code mb (A + 8322 + 8192 * k1 + 5 + 16 * k2)
      (enc (.movB (fld Mode.x86 (A + 8322 + 8192 * k1 + 5 + 16 * k2) 7 (N + 6)) (k1 ^^^ k2))) := by cext f1
  have s7 : step Mode.x86 (A + 8322 + 8192 * k1 + 5 + 16 * k2, mb) =
      some (A + 8322 + 8192 * k1 + 5 + 16 * k2 + 7, mc) :=
    step_movB Mode.x86 mb _ (N + 6) _ (by omega) (by omega) hx cb7
  have cc8 : Code mc (A + 8322 + 8192 * k1 + 5 + 16 * k2 + 7)
      (enc (.jmp32 (jrel (A + 8322 + 8192 * k1 + 5 + 16 * k2 + 7) N))) := by cext f2
  have s8 : step Mode.x86 (A + 8322 + 8192 * k1 + 5 + 16 * k2 + 7, mc) = some (N, mc) :=
    step_jmp32_to Mode.x86 mc _ N (by omega) (by omega) cc8
  have cc9 : Code mc N (enc (.movB (fld Mode.x86 N 7 Dd) (k1 ^^^ k2))) := by
    have := patch_movB_imm mb N _ b0 _ hb0 hx (by cext uN)
    exact this
  have s9 : step Mode.x86 (N, mc) = some (N + 7, md) :=
    step_movB Mode.x86 mc N Dd _ (by omega) (by omega) hx cc9
  have cd10 : Code md (N + 7) (enc (.jmp32 (jrel (N + 7) (Dd - 1)))) := by cext uR
  have s10 : step Mode.x86 (N + 7, md) = some (Dd - 1, md) :=
    step_jmp32_to Mode.x86 md (N + 7) (Dd - 1) (by omega) (by omega) cd10
  simp only [runN, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, Option.bind_some]
  rfl

/-- The image of `WriteExecXOR` (x86 build) at the entry `xorarg1 = A` (absolute addresses); see `XorImg64`.
`ej` is the `DEFINEXORJMP` table (32-byte entries, near jumps below index `0fch`, short jumps from there on). -/
structure XorImg86 (m : Mem) (A S5 S4 N Dd k1 k2 d01 w01 r01 d02 w02 r02 d1 c1 rL vJ d2 c2s wJ b0 : Nat)
    (v : Nat → Nat) : Prop where
  a1 : ArgImg Mode.x86 m A S5 (S5 + 5 + 65536) (A + 97) k1 5 d01 w01 r01
  a2 : ArgImg Mode.x86 m (A + 32) S4 (S4 + 5 + 65536) (A + 8315) k2 4 d02 w02 r02
  p1 : Code m (A + 64) (enc (.movD (fld Mode.x86 (A + 64) 10 (A + 93)) (fld Mode.x86 (A + 90) 9 (A + 8319))))
  p2 : Code m (A + 74) (enc (.movB (fld Mode.x86 (A + 74) 7 (A + 110)) 228))
  p3 : Code m (A + 81) (enc (.jmp8 7))
  xh : Code m (A + 83) (enc (.movB (fld Mode.x86 (A + 83) 7 (A + 110)) 0))
  h1 : Code m (A + 90) (enc (.movW d1 c1))
  h1b : Code m (A + 99) (enc (.movD (fld Mode.x86 (A + 99) 10 (A + 93)) (fld Mode.x86 (A + 90) 9 (A + 112))))
  xl : Code m (A + 109) (enc (.jmp8 rL))
  jj : Code m (A + 111) (enc (.jmp32 vJ))
  ej : ∀ i, i < 256 → Code m (A + 116 + 32 * i)
    (enc (.movD (fld Mode.x86 (A + 116 + 32 * i) 10 (A + 8311)) (A + 8323 + 8192 * i)) ++
      jmpTo (decide (i < 252)) (A + 116 + 32 * i + 10) (A + 8308))
  h2 : Code m (A + 8308) (enc (.movW d2 c2s))
  xj : Code m (A + 8317) (enc (.jmp32 (256 * wJ)))
  gj : ∀ i, i < 256 → Code m (A + 8322 + 8192 * i) (enc (.jmp32 (v i)))
  ent : ∀ i j, i < 256 → j < 256 → Code m (A + 8322 + 8192 * i + 5 + 16 * j)
    (enc (.movB (fld Mode.x86 (A + 8322 + 8192 * i + 5 + 16 * j) 7 (N + 6)) (i ^^^ j)) ++
      enc (.jmp32 (jrel (A + 8322 + 8192 * i + 5 + 16 * j + 7) N)))
  iN : Code m N (enc (.movB (fld Mode.x86 N 7 Dd) b0))
  iRet : Code m (N + 7) (enc (.jmp32 (jrel (N + 7) (Dd - 1))))

/-- C18 (Fig. 6), x86 build of the published `writeexc.asm`: for every pair of argument bytes `k1`, `k2`, execution from
`xorarg1` reaches the return jump target `Dd - 1` after `38` steps, having stored `k1 xor k2` at `Dd`; every write is
to an instruction field. -/
theorem xor_exec_x86 (m : Mem) (A S5 S4 N Dd k1 k2 d01 w01 r01 d02 w02 r02 d1 c1 rL vJ d2 c2s wJ b0 : Nat)
    (v : Nat → Nat) (hk1 : k1 < 256) (hk2 : k2 < 256)
    (hord4 : S4 + 5 + 65536 + 14 ≤ S5) (hord5 : S5 + 5 + 65536 + 14 ≤ A)
    (hbig : A + 2 ^ 22 < 2 ^ 30) (hN : N = A + 8322 + 2 ^ 21) (hDd : N + 12 ≤ Dd) (hDb : Dd + 1 < 2 ^ 30)
    (hv : ∀ i, i < 256 → v i < 65536) (hvJ : vJ < 65536) (hwJ : wJ < 65536) (hb0 : b0 < 256)
    (hrL : rL < 256)
    (img : XorImg86 m A S5 S4 N Dd k1 k2 d01 w01 r01 d02 w02 r02 d1 c1 rL vJ d2 c2s wJ b0 v) :
    ∃ mEnd, runN Mode.x86 38 (A, m) = some (Dd - 1, mEnd) ∧ mEnd Dd = k1 ^^^ k2 ∧
      ∀ x, ¬(x = S5 + 2 ∨ (S5 + 5 + 65536 + 3 ≤ x ∧ x < S5 + 5 + 65536 + 9) ∨
        (S5 + 5 + 65536 + 10 ≤ x ∧ x < S5 + 5 + 65536 + 14) ∨ x = S4 + 2 ∨
        (S4 + 5 + 65536 + 3 ≤ x ∧ x < S4 + 5 + 65536 + 9) ∨
        (S4 + 5 + 65536 + 10 ≤ x ∧ x < S4 + 5 + 65536 + 14) ∨
        (A + 93 ≤ x ∧ x < A + 99) ∨ x = A + 110 ∨ (A + 112 ≤ x ∧ x < A + 114) ∨
        (A + 8311 ≤ x ∧ x < A + 8317) ∨ (A + 8319 ≤ x ∧ x < A + 8321) ∨
        (A + 8323 + 8192 * k1 ≤ x ∧ x < A + 8325 + 8192 * k1) ∨ x = N + 6 ∨ x = Dd) → mEnd x = m x := by
  have hx : k1 ^^^ k2 < 256 := by
    have := Nat.xor_lt_two_pow (n := 8) (x := k1) (y := k2) (by omega) (by omega)
    simpa using this
  -- stage 1
  let m1a := wr m (S5 + 2) 1 k1
  let m1b := wr m1a (S5 + 5 + 65536 + 3) 4 (fld Mode.x86 (S5 + 5 + 65536) 9 (A + 97))
  let m1c := wr m1b (S5 + 5 + 65536 + 9 + 1) 4 (jrel (S5 + 5 + 65536 + 9) (A + 32))
  let m1d := wr m1c (S5 + 5 + 65536 + 7) 2 (k1 * 2 ^ 5)
  let m1 := wr m1d (A + 97) 2 (k1 * 2 ^ 5)
  have R1 : runN Mode.x86 9 (A, m) = some (A + 32, m1) :=
    arg_stage Mode.x86 m A S5 (S5 + 5 + 65536) (A + 97) k1 5 d01 w01 r01 hk1 (by omega) rfl (by omega)
      (by omega) (by omega) (by omega) img.a1.i0 img.a1.i1 img.a1.i2 img.a1.i3 img.a1.iX img.a1.iT
      img.a1.iR img.a1.iS
  -- stage 2
  have a2' : ArgImg Mode.x86 m1 (A + 32) S4 (S4 + 5 + 65536) (A + 8315) k2 4 d02 w02 r02 :=
    img.a2.ext rfl (fun x hx => by simp (disch := omega) only [m1, m1d, m1c, m1b, m1a, wr_apply_out'])
  let m2a := wr m1 (S4 + 2) 1 k2
  let m2b := wr m2a (S4 + 5 + 65536 + 3) 4 (fld Mode.x86 (S4 + 5 + 65536) 9 (A + 8315))
  let m2c := wr m2b (S4 + 5 + 65536 + 9 + 1) 4 (jrel (S4 + 5 + 65536 + 9) (A + 32 + 32))
  let m2d := wr m2c (S4 + 5 + 65536 + 7) 2 (k2 * 2 ^ 4)
  let m2 := wr m2d (A + 8315) 2 (k2 * 2 ^ 4)
  have R2 : runN Mode.x86 9 (A + 32, m1) = some (A + 32 + 32, m2) :=
    arg_stage Mode.x86 m1 (A + 32) S4 (S4 + 5 + 65536) (A + 8315) k2 4 d02 w02 r02 hk2 (by omega) rfl (by omega)
      (by omega) (by omega) (by omega) a2'.i0 a2'.i1 a2'.i2 a2'.i3 a2'.iX a2'.iT a2'.iR a2'.iS
  have hA32 : A + 32 + 32 = A + 64 := by omega
  rw [hA32] at R2
  -- the three patches
  let V1 := fld Mode.x86 (A + 90) 9 (A + 8319)
  have hV1 : V1 < 2 ^ 32 := fld_lt _ _ _ _ (by omega)
  let mp1 := wr m2 (A + 93) 4 V1
  let mF := wr mp1 (A + 110) 1 228
  have cp1 : Code m2 (A + 64) (enc (.movD (fld Mode.x86 (A + 64) 10 (A + 93)) V1)) := by
    cext img.p1
  have P1 : step Mode.x86 (A + 64, m2) = some (A + 74, mp1) :=
    step_movD Mode.x86 m2 (A + 64) (A + 93) V1 (by omega) (by omega) hV1 cp1
  have cp2 : Code mp1 (A + 74) (enc (.movB (fld Mode.x86 (A + 74) 7 (A + 110)) 228)) := by
    cext img.p2
  have P2 : step Mode.x86 (A + 74, mp1) = some (A + 81, mF) :=
    step_movB Mode.x86 mp1 (A + 74) (A + 110) 228 (by omega) (by omega) (by omega) cp2
  have cp3 : Code mF (A + 81) (enc (.jmp8 7)) := by
    cext img.p3
  have P3 : step Mode.x86 (A + 81, mF) = some (A + 90, mF) := by
    have := step_jmp8 Mode.x86 mF (A + 81) 7 (by omega) cp3
    rw [this]
  -- the loop
  have cL1 : Code mF (A + 90) (enc (.movW (fld Mode.x86 (A + 90) 9 (A + 8319)) (k1 * 32))) := by
    have X1 : Code m1d (A + 90) (enc (.movW d1 c1)) := by cext img.h1
    have X2 : Code m1 (A + 90) (enc (.movW d1 (k1 * 2 ^ 5))) := by
      have := patch_movW_imm m1d (A + 90) d1 c1 (k1 * 2 ^ 5) X1
      rw [show A + 90 + 7 = A + 97 by omega] at this
      exact this
    have X3 : Code m2 (A + 90) (enc (.movW d1 (k1 * 2 ^ 5))) := by cext X2
    have X4 : Code mp1 (A + 90) (enc (.movW V1 (k1 * 2 ^ 5))) := by
      have := patch_movW_disp m2 (A + 90) d1 V1 (k1 * 2 ^ 5) X3
      rw [show A + 90 + 3 = A + 93 by omega] at this
      exact this
    have X5 : Code mF (A + 90) (enc (.movW V1 (k1 * 2 ^ 5))) := by cext X4
    exact X5
  have cL2 : Code mF (A + 99) (enc (.movD (fld Mode.x86 (A + 99) 10 (A + 93)) (fld Mode.x86 (A + 90) 9 (A + 112)))) := by
    cext img.h1b
  have cL3 : Code mF (A + 109) (enc (.jmp8 228)) := by
    have := patch_jmp8 mp1 (A + 109) rL 228 hrL (by omega) (by cext img.xl)
    rw [show A + 109 + 1 = A + 110 by omega] at this
    exact this
  have cL4 : Code mF (A + 83) (enc (.movB (fld Mode.x86 (A + 83) 7 (A + 110)) 0)) := by
    cext img.xh
  have RL := xor_loop Mode.x86 mF A (A + 8319) (A + 112) k1 hk1 (by omega) (by omega) (by omega) (by omega) (by omega) cL1 cL2 cL3 cL4
  let V2 := fld Mode.x86 (A + 90) 9 (A + 112)
  let ML1 := wr mF (A + 8319) 2 (k1 * 32)
  let ML2 := wr ML1 (A + 93) 4 V2
  let ML3 := wr ML2 (A + 110) 1 0
  let ML4 := wr ML3 (A + 112) 2 (k1 * 32)
  let ML5 := wr ML4 (A + 93) 4 V2
  -- the tail
  have u1 : Code ML5 (A + 111) (enc (.jmp32 (k1 * 32))) := by
    have Y1 : Code ML3 (A + 111) (enc (.jmp32 vJ)) := by cext img.jj
    have Y2 : Code ML4 (A + 111) (enc (.jmp32 (k1 * 32))) := by
      have := patch_jmp32_word ML3 (A + 111) vJ (k1 * 32) hvJ (by omega) Y1
      rw [show A + 111 + 1 = A + 112 by omega] at this
      exact this
    cext Y2
  have u2 : Code ML5 (A + 116 + 32 * k1)
      (enc (.movD (fld Mode.x86 (A + 116 + 32 * k1) 10 (A + 8311)) (A + 8323 + 8192 * k1)) ++
        jmpTo (decide (k1 < 252)) (A + 116 + 32 * k1 + 10) (A + 8308)) := by
    cext img.ej k1 hk1
  have u3 : Code ML5 (A + 8308) (enc (.movW d2 (k2 * 16))) := by
    have Y1 : Code m2d (A + 8308) (enc (.movW d2 c2s)) := by cext img.h2
    have Y2 : Code m2 (A + 8308) (enc (.movW d2 (k2 * 2 ^ 4))) := by
      have := patch_movW_imm m2d (A + 8308) d2 c2s (k2 * 2 ^ 4) Y1
      rw [show A + 8308 + 7 = A + 8315 by omega] at this
      exact this
    cext Y2
  have u4 : Code ML5 (A + 8317) (enc (.jmp32 (jrel (A + 8317) (A + 8322 + 8192 * k1)))) := by
    have Z1 : Code mF (A + 8317) (enc (.jmp32 (256 * wJ))) := by cext img.xj
    have Z2 : Code ML1 (A + 8317) (enc (.jmp32 (256 * (k1 * 32)))) := by
      have := patch_jmp32_mid mF (A + 8317) wJ (k1 * 32) hwJ (by omega) Z1
      rw [show A + 8317 + 2 = A + 8319 by omega] at this
      exact this
    have Z3 : Code ML5 (A + 8317) (enc (.jmp32 (256 * (k1 * 32)))) := by cext Z2
    have e2 : jrel (A + 8317) (A + 8322 + 8192 * k1) = 256 * (k1 * 32) := by
      simp only [jrel]; omega
    rw [e2]
    exact Z3
  have u5 : Code ML5 (A + 8322 + 8192 * k1) (enc (.jmp32 (v k1))) := by cext img.gj k1 hk1
  have u6 : Code ML5 (A + 8322 + 8192 * k1 + 5 + 16 * k2)
      (enc (.movB (fld Mode.x86 (A + 8322 + 8192 * k1 + 5 + 16 * k2) 7 (N + 6)) (k1 ^^^ k2)) ++
        enc (.jmp32 (jrel (A + 8322 + 8192 * k1 + 5 + 16 * k2 + 7) N))) := by
    cext img.ent k1 k2 hk1 hk2
  have uN : Code ML5 N (enc (.movB (fld Mode.x86 N 7 Dd) b0)) := by cext img.iN
  have uR : Code ML5 (N + 7) (enc (.jmp32 (jrel (N + 7) (Dd - 1)))) := by cext img.iRet
  have RT := xor_tail_x86 ML5 A k1 k2 N Dd (v k1) d2 b0 hk1 hk2 hbig hN hDd hDb (hv k1 hk1) hb0 u1 u2 u3 u4 u5 u6 uN uR
  let mEnd := wr (wr (wr (wr ML5 (A + 8311) 4 (A + 8323 + 8192 * k1)) (A + 8323 + 8192 * k1) 2 (k2 * 16))
    (N + 6) 1 (k1 ^^^ k2)) Dd 1 (k1 ^^^ k2)
  have RA : runN Mode.x86 (9 + (9 + (1 + (1 + (1 + (7 + 10)))))) (A, m) = some (Dd - 1, mEnd) :=
    runN_trans Mode.x86 R1 (runN_trans Mode.x86 R2 (runN_trans Mode.x86 (runN_one _ _ _ P1)
      (runN_trans Mode.x86 (runN_one _ _ _ P2) (runN_trans Mode.x86 (runN_one _ _ _ P3)
        (runN_trans Mode.x86 RL RT)))))
  refine ⟨mEnd, RA, ?_, ?_⟩
  · have : mEnd Dd = (k1 ^^^ k2) / 256 ^ (Dd - Dd) % 256 := wr_apply_in _ _ _ _ _ ⟨Nat.le_refl _, by omega⟩
    rw [this]; simp; omega
  · intro x hx
    simp +zetaDelta (disch := omega) only [wr_apply_out']

end WriteExecute.X86
