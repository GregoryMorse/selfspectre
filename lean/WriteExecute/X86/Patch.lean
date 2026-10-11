module
public import WriteExecute.X86.Basic

public section

namespace WriteExecute.X86

theorem wr_le (m : Mem) (e N V : Nat) :
    ∀ (n i : Nat), i + n ≤ N → Code (wr m e N V) (e + i) (le n (V / 256 ^ i))
  | 0, i, _ => trivial
  | n + 1, i, h => by
    refine ⟨?_, ?_⟩
    · have hc : e ≤ e + i ∧ e + i < e + N := by omega
      simp only [wr, hc, and_self, ite_true, Nat.add_sub_cancel_left]
    · have := wr_le m e N V n (i + 1) (by omega)
      rw [show e + i + 1 = e + (i + 1) by omega]
      rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul] at this
      exact this

theorem wr_code (m : Mem) (e n v : Nat) : Code (wr m e n v) e (le n v) := by
  have := wr_le m e n v n 0 (by omega)
  simpa using this

theorem Code_patch (m : Mem) (pre post : List Nat) (n v v' a e : Nat) (he : e = a + pre.length)
    (h : Code m a (pre ++ le n v ++ post)) : Code (wr m e n v') a (pre ++ le n v' ++ post) := by
  simp only [List.append_assoc, Code_append] at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Code_frame m e n v' pre a h1 (Or.inl (by omega)), ?_, ?_⟩
  · subst he; exact wr_code m _ n v'
  · rw [le_bound] at h3 ⊢
    exact Code_frame m e n v' post _ h3 (Or.inr (by omega))

theorem enc_movB_imm (d i : Nat) (hi : i < 256) :
    enc (.movB d i) = ([0xC6, 0x05] ++ le 4 d) ++ (le 1 i ++ []) := by
  simp [enc, le, Nat.mod_eq_of_lt hi]
theorem enc_movB_disp (d i : Nat) : enc (.movB d i) = [0xC6, 0x05] ++ le 4 d ++ ([i] ++ []) := by
  simp [enc]
theorem enc_movW_imm (d i : Nat) : enc (.movW d i) = ([0x66, 0xC7, 0x05] ++ le 4 d) ++ (le 2 i ++ []) := by
  simp [enc]
theorem enc_movW_disp (d i : Nat) : enc (.movW d i) = [0x66, 0xC7, 0x05] ++ le 4 d ++ (le 2 i ++ []) := by
  simp [enc]
theorem enc_movD_imm (d i : Nat) : enc (.movD d i) = ([0xC7, 0x05] ++ le 4 d) ++ (le 4 i ++ []) := by
  simp [enc]
theorem enc_movD_disp (d i : Nat) : enc (.movD d i) = [0xC7, 0x05] ++ le 4 d ++ (le 4 i ++ []) := by
  simp [enc]
theorem enc_jmp32_rel (r : Nat) : enc (.jmp32 r) = [0xE9] ++ le 4 r ++ [] := by simp [enc]

theorem patch_movB_imm (m : Mem) (a d i i' : Nat) (hi0 : i < 256) (hi : i' < 256) (h : Code m a (enc (.movB d i))) :
    Code (wr m (a + 6) 1 i') a (enc (.movB d i')) := by
  have h' : Code m a (([0xC6, 0x05] ++ le 4 d) ++ le 1 i ++ []) := by
    rw [enc_movB_imm d i hi0] at h; simpa [List.append_assoc] using h
  have := Code_patch m ([0xC6, 0x05] ++ le 4 d) [] 1 i i' a (a + 6) (by simp [le_bound]) h'
  rw [enc_movB_imm d i' hi]
  simpa [List.append_assoc] using this

theorem patch_movW_imm (m : Mem) (a d i i' : Nat) (h : Code m a (enc (.movW d i))) :
    Code (wr m (a + 7) 2 i') a (enc (.movW d i')) := by
  have h' : Code m a (([0x66, 0xC7, 0x05] ++ le 4 d) ++ le 2 i ++ []) := by
    rw [enc_movW_imm] at h; simpa [List.append_assoc] using h
  have := Code_patch m ([0x66, 0xC7, 0x05] ++ le 4 d) [] 2 i i' a (a + 7) (by simp [le_bound]) h'
  rw [enc_movW_imm]
  simpa [List.append_assoc] using this

theorem patch_movW_disp (m : Mem) (a d d' i : Nat) (h : Code m a (enc (.movW d i))) :
    Code (wr m (a + 3) 4 d') a (enc (.movW d' i)) := by
  have h' : Code m a ([0x66, 0xC7, 0x05] ++ le 4 d ++ (le 2 i ++ [])) := by
    rw [enc_movW_disp] at h; exact h
  have := Code_patch m [0x66, 0xC7, 0x05] (le 2 i ++ []) 4 d d' a (a + 3) (by simp) (by
    simpa [List.append_assoc] using h')
  rw [enc_movW_disp]
  simpa [List.append_assoc] using this

theorem patch_movD_disp (m : Mem) (a d d' i : Nat) (h : Code m a (enc (.movD d i))) :
    Code (wr m (a + 2) 4 d') a (enc (.movD d' i)) := by
  have h' : Code m a ([0xC7, 0x05] ++ le 4 d ++ (le 4 i ++ [])) := by
    rw [enc_movD_disp] at h; exact h
  have := Code_patch m [0xC7, 0x05] (le 4 i ++ []) 4 d d' a (a + 2) (by simp) (by
    simpa [List.append_assoc] using h')
  rw [enc_movD_disp]
  simpa [List.append_assoc] using this

theorem patch_jmp32 (m : Mem) (a r r' : Nat) (h : Code m a (enc (.jmp32 r))) :
    Code (wr m (a + 1) 4 r') a (enc (.jmp32 r')) := by
  have h' : Code m a ([0xE9] ++ le 4 r ++ []) := by rw [enc_jmp32_rel] at h; exact h
  have := Code_patch m [0xE9] [] 4 r r' a (a + 1) (by simp) h'
  rw [enc_jmp32_rel]; exact this

theorem enc_jmp32_byte (k : Nat) (hk : k < 256) :
    enc (.jmp32 (256 * k)) = [0xE9, 0] ++ le 1 k ++ [0, 0] := by
  simp only [enc, le]
  simp only [List.cons.injEq, List.cons_append, List.nil_append, List.append_nil, true_and, and_true]
  refine ⟨by omega, by omega, by omega, by omega⟩

theorem enc_jmp32_word (w : Nat) (hw : w < 65536) :
    enc (.jmp32 w) = [0xE9] ++ le 2 w ++ [0, 0] := by
  simp only [enc, le]
  simp only [List.cons.injEq, List.cons_append, List.nil_append, List.append_nil, true_and, and_true]
  exact ⟨by omega, by omega⟩

/-- Writing byte `k` at `+2` of `jmp 256*j` (j < 256) gives `jmp 256*k`. -/
theorem patch_jmp32_byte (m : Mem) (a j k : Nat) (hj : j < 256) (hk : k < 256)
    (h : Code m a (enc (.jmp32 (256 * j)))) :
    Code (wr m (a + 2) 1 k) a (enc (.jmp32 (256 * k))) := by
  rw [enc_jmp32_byte j hj] at h
  have h' : Code m a ([0xE9, 0] ++ le 1 j ++ [0, 0]) := h
  have := Code_patch m [0xE9, 0] [0, 0] 1 j k a (a + 2) (by simp) h'
  rw [enc_jmp32_byte k hk]; exact this

/-- Writing word `w` at `+1` of `jmp v` (v < 65536) gives `jmp w`. -/
theorem patch_jmp32_word (m : Mem) (a v w : Nat) (hv : v < 65536) (hw : w < 65536)
    (h : Code m a (enc (.jmp32 v))) :
    Code (wr m (a + 1) 2 w) a (enc (.jmp32 w)) := by
  rw [enc_jmp32_word v hv] at h
  have := Code_patch m [0xE9] [0, 0] 2 v w a (a + 1) (by simp) h
  rw [enc_jmp32_word w hw]; exact this

end WriteExecute.X86
