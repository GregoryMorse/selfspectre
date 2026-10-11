module
public import WriteExecute.X86.Patch

public section

namespace WriteExecute.X86

theorem enc_len (ins : Ins) : (enc ins).length = ins.len := by
  cases ins <;> simp [enc, Ins.len, le_bound]

/-- A stride-256 SHL table (`shlarg` jump, 256 entries, `shlres`, `shlret`): with the argument byte `k`
patched into the jump, five steps store the word `k * 2^c` at `D` and continue at `Ret`. -/
theorem shl_lookup (mode : Mode) (m : Mem) (A R k c D w0 Ret : Nat) (hRd : R = A + 5 + 65536)
    (hk : k < 256) (hc : c ≤ 7) (hB : R + 14 < 2 ^ 30) (hD : D + 2 < 2 ^ 30) (hRet : Ret < 2 ^ 30)
    (hDdis : D + 2 ≤ A ∨ R + 14 ≤ D)
    (hA : Code m A (enc (.jmp32 (256 * k))))
    (hT : ∀ j, j < 256 → Code m (A + 5 + 256 * j)
      (enc (.movW (fld mode (A + 5 + 256 * j) 9 (R + 7)) (j * 2 ^ c)) ++
        enc (.jmp32 (jrel (A + 5 + 256 * j + 9) R))))
    (hR : Code m R (enc (.movW (fld mode R 9 D) w0)))
    (hS : Code m (R + 9) (enc (.jmp32 (jrel (R + 9) Ret)))) :
    runN mode 5 (A, m) = some (Ret, wr (wr m (R + 7) 2 (k * 2 ^ c)) D 2 (k * 2 ^ c)) := by
  have hv : k * 2 ^ c < 65536 := by
    have h2c : 2 ^ c ≤ 2 ^ 7 := Nat.pow_le_pow_right (by omega) hc
    have := Nat.mul_le_mul (show k ≤ 255 by omega) h2c
    omega
  obtain ⟨hE1, hE2⟩ := (Code_append m _ _ _).1 (hT k hk)
  rw [enc_len] at hE2
  simp only [Ins.len] at hE2
  have s1 : step mode (A, m) = some (A + 5 + 256 * k, m) := by
    have := step_jmp32 mode m A (256 * k) (by omega) hA
    simpa using this
  have s2 := step_movW mode m (A + 5 + 256 * k) (R + 7) (k * 2 ^ c) (by omega) (by omega) hv hE1
  have hE2' : Code (wr m (R + 7) 2 (k * 2 ^ c)) (A + 5 + 256 * k + 9)
      (enc (.jmp32 (jrel (A + 5 + 256 * k + 9) R))) := by
    apply Code_frame _ _ _ _ _ _ hE2
    rw [enc_len]; simp only [Ins.len]; omega
  have s3 := step_jmp32_to mode (wr m (R + 7) 2 (k * 2 ^ c)) (A + 5 + 256 * k + 9) R
    (by omega) (by omega) hE2'
  have hR' := patch_movW_imm m R _ w0 (k * 2 ^ c) hR
  have s4 := step_movW mode (wr m (R + 7) 2 (k * 2 ^ c)) R D (k * 2 ^ c) (by omega) (by omega) hv hR'
  have hS' : Code (wr (wr m (R + 7) 2 (k * 2 ^ c)) D 2 (k * 2 ^ c)) (R + 9)
      (enc (.jmp32 (jrel (R + 9) Ret))) := by
    apply Code_frame _ _ _ _ _ _ _ (by rw [enc_len]; simp only [Ins.len]; omega)
    apply Code_frame _ _ _ _ _ _ hS
    rw [enc_len]; simp only [Ins.len]; omega
  have s5 := step_jmp32_to mode _ (R + 9) Ret (by omega) hRet hS'
  simp only [runN, s1, s2, s3, s4, s5, Option.bind_some]

/-- `jmp N` as assembled by MASM: `rel32` (near) or `rel8` (short). -/
@[expose] def jmpTo (near : Bool) (A N : Nat) : List Nat :=
  if near then enc (.jmp32 (jrel A N)) else enc (.jmp8 (N - (A + 2)))

theorem step_jmpTo (mode : Mode) (m : Mem) (near : Bool) (a N : Nat) (ha : a < 2 ^ 30)
    (hN : N < 2 ^ 30) (hs : near = false → a + 2 ≤ N ∧ N - (a + 2) < 128)
    (h : Code m a (jmpTo near a N)) : step mode (a, m) = some (N, m) := by
  cases near with
  | true => exact step_jmp32_to mode m a N ha hN h
  | false =>
    have := step_jmp8 mode m a (N - (a + 2)) (hs rfl).2 h
    rw [this]; congr 2; have := hs rfl; omega

theorem jmpTo_len (near : Bool) (A N : Nat) : (jmpTo near A N).length ≤ 5 := by
  cases near <;> simp [jmpTo, enc_len, Ins.len]

theorem nop_slide (mode : Mode) (m : Mem) : ∀ (s P : Nat), Code m P (List.replicate s 0x90) →
    runN mode s (P, m) = some (P + s, m)
  | 0, P, _ => by simp [runN]
  | s + 1, P, h => by
    have h1 : Code m P (enc .nop) := by simpa [enc, List.replicate, Code] using h.1
    have h2 : step mode (P, m) = some (P + 1, m) := step_nop mode m P h1
    have := nop_slide mode m s (P + 1) h.2
    simp only [runN, h2, Option.bind_some, this]
    congr 2; omega

/-- A table-16 entry (`mov byte [N+6], v; jmp N; nops`) reached from `P` through a NOP slide of
`E - P` bytes stores `v` at `N+6` and continues at `N`. -/
theorem table16_lookup (mode : Mode) (m : Mem) (P E N v t : Nat) (near : Bool) (hPE : P ≤ E)
    (hE : E + 14 < 2 ^ 30) (hN : N + 6 < 2 ^ 30) (hv : v < 256) (hdis : E + 14 ≤ N + 6)
    (hs : near = false → E + 9 ≤ N ∧ N - (E + 9) < 128)
    (hslide : Code m P (List.replicate (E - P) 0x90))
    (hEntry : Code m E (enc (.movB (fld mode E 7 (N + 6)) v) ++ (jmpTo near (E + 7) N ++ List.replicate t 0x90))) :
    runN mode (E - P + 2) (P, m) = some (N, wr m (N + 6) 1 v) := by
  have sl := nop_slide mode m (E - P) P hslide
  obtain ⟨h1, h2⟩ := (Code_append m _ _ _).1 hEntry
  rw [enc_len] at h2
  simp only [Ins.len] at h2
  obtain ⟨h3, -⟩ := (Code_append m _ _ _).1 h2
  have s1 := step_movB mode m E (N + 6) v (by omega) (by omega) hv h1
  have h3' : Code (wr m (N + 6) 1 v) (E + 7) (jmpTo near (E + 7) N) := by
    apply Code_frame _ _ _ _ _ _ h3
    have := jmpTo_len near (E + 7) N
    omega
  have s2 := step_jmpTo mode _ near (E + 7) N (by omega) (by omega) (by intro hn; have := hs hn; omega) h3'
  have e : P + (E - P) = E := by omega
  rw [runN_add, sl, e]
  simp only [Option.bind_some, runN, s1, s2]

end WriteExecute.X86
