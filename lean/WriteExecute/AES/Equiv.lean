module
public import WriteExecute.AES.Basic

public section

namespace WriteExecute.AES

open WriteExecute.Arith

theorem mix_row (u : St) (c r : Nat) (hc : c < 4) (hr : r < 4) :
    (mixColumns u).getD (4 * c + r) 0 =
      mulc (tcoef 0 r) (u.getD (4 * c) 0) ^^^ mulc (tcoef 1 r) (u.getD (4 * c + 1) 0) ^^^
        mulc (tcoef 2 r) (u.getD (4 * c + 2) 0) ^^^ mulc (tcoef 3 r) (u.getD (4 * c + 3) 0) := by
  have hf : 4 * c + r < 16 := by omega
  have e1 : (4 * c + r) / 4 = c := by omega
  have e2 : (4 * c + r) % 4 = r := by omega
  simp only [mixColumns, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hf,
    Option.map_some, Option.getD_some, e1, e2]
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp [mixCol, mulc, tcoef]

theorem nvalInv_nval : ∀ f, f < 16 → nvalInv (nval (f + 1)) = f + 1 := by decide
/-- C22: the asm's position formulas `nval`/`nvalInv` are mutually inverse bijections on 1..16. -/
theorem nval_nvalInv : ∀ q, q < 16 → nval (nvalInv (q + 1)) = q + 1 := by decide

theorem pos_src : ∀ c, c < 4 → ∀ j, j < 4 → nval (4 * ((c + j) % 4) + j + 1) = 4 * c + j + 1 := by
  decide

/-- Key bytes: memory byte `4 (f/4) + 3 - f%4` of round key `r` is byte `f` of the FIPS round key. -/
theorem keyRel (w : List Nat) (r f : Nat) (hf : f < 16) :
    keyMem w r (4 * (f / 4) + 3 - f % 4) = (roundKey w r).getD f 0 := by
  have e1 : (4 * (f / 4) + 3 - f % 4) / 4 = f / 4 := by omega
  have e2 : (4 * (f / 4) + 3 - f % 4) % 4 = 3 - f % 4 := by omega
  simp [keyMem, roundKey, List.getD_eq_getElem?_getD, hf, e1, e2]

theorem keyMem_lt (w : List Nat) (r j : Nat) : keyMem w r j < 256 := and255_lt _

theorem weState_lt (inp : Nat → Nat) (w : List Nat) (hinp : ∀ i, inp i < 256) :
    ∀ n p, weState inp w n p < 256
  | 0, p => by
    simp only [weState, weInit]
    exact xor_lt256 (hinp _) (keyMem_lt _ _ _)
  | n + 1, p => by
    simp only [weState, weRound, weOut, lbyte]
    exact xor_lt256 (xor_lt256 (xor_lt256 (xor_lt256 (keyMem_lt _ _ _) (and255_lt _)) (and255_lt _))
      (and255_lt _)) (and255_lt _)

theorem te_byte (k x r : Nat) (hk : k < 4) (hx : x < 256) (hr : r < 4) :
    lbyte (teLit k x) (4 - r) = mulc (tcoef k r) (sbox x) := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
  · obtain ⟨h1, h2, h3, h4⟩ := te0_bytes x hx
    rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 by omega) with rfl | rfl | rfl | rfl <;>
      first | exact h1 | exact h2 | exact h3 | exact h4
  · obtain ⟨h1, h2, h3, h4⟩ := te1_bytes x hx
    rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 by omega) with rfl | rfl | rfl | rfl <;>
      first | exact h1 | exact h2 | exact h3 | exact h4
  · obtain ⟨h1, h2, h3, h4⟩ := te2_bytes x hx
    rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 by omega) with rfl | rfl | rfl | rfl <;>
      first | exact h1 | exact h2 | exact h3 | exact h4
  · obtain ⟨h1, h2, h3, h4⟩ := te3_bytes x hx
    rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 by omega) with rfl | rfl | rfl | rfl <;>
      first | exact h1 | exact h2 | exact h3 | exact h4

theorem round_step (w pt : List Nat) (hpt : pt.length = 16) (n : Nat) (sw : Nat → Nat)
    (hb : ∀ p, sw p < 256)
    (hinv : ∀ f, f < 16 → sw (nval (f + 1)) = (rounds w pt n).getD f 0) :
    ∀ f, f < 16 → weRound sw (keyMem w (n + 1)) (nval (f + 1)) = (rounds w pt (n + 1)).getD f 0 := by
  intro f hf
  obtain ⟨c, r, hc, hr, rfl⟩ : ∃ c r, c < 4 ∧ r < 4 ∧ f = 4 * c + r :=
    ⟨f / 4, f % 4, by omega, by omega, by omega⟩
  have hs : (rounds w pt n).length = 16 := rounds_length w pt hpt n
  have hsw : ∀ j, j < 4 → sw (4 * c + j + 1) = (rounds w pt n).getD (4 * ((c + j) % 4) + j) 0 := by
    intro j hj
    have := hinv (4 * ((c + j) % 4) + j) (by omega)
    rw [pos_src c hc j hj] at this
    exact this
  have a0 : sw (4 * c + 1) = (rounds w pt n).getD (4 * ((c + 0) % 4) + 0) 0 := hsw 0 (by omega)
  have a1 : sw (4 * c + 2) = (rounds w pt n).getD (4 * ((c + 1) % 4) + 1) 0 := hsw 1 (by omega)
  have a2 : sw (4 * c + 3) = (rounds w pt n).getD (4 * ((c + 2) % 4) + 2) 0 := hsw 2 (by omega)
  have a3 : sw (4 * c + 4) = (rounds w pt n).getD (4 * ((c + 3) % 4) + 3) 0 := hsw 3 (by omega)
  have sh : ∀ j, j < 4 →
      (shiftRows (subBytes (rounds w pt n))).getD (4 * c + j) 0 =
        sbox ((rounds w pt n).getD (4 * ((c + j) % 4) + j) 0) := by
    intro j hj
    rw [shiftRows_getD _ _ (by omega), subBytes_getD _ _ (by omega)]
    have : (4 * c + j + 4 * ((4 * c + j) % 4)) % 16 = 4 * ((c + j) % 4) + j := by omega
    rw [this]
  have s0 : (shiftRows (subBytes (rounds w pt n))).getD (4 * c) 0 =
      sbox ((rounds w pt n).getD (4 * ((c + 0) % 4) + 0) 0) := sh 0 (by omega)
  simp only [rounds, fipsRound]
  rw [addRoundKey_getD _ _ _ (by rw [mixColumns_length]; omega) (by rw [roundKey_length]; omega),
    mix_row _ c r hc hr, s0, sh 1 (by omega), sh 2 (by omega), sh 3 (by omega),
    ← keyRel w (n + 1) (4 * c + r) hf]
  simp only [weRound, nvalInv_nval _ hf, weOut]
  have e1 : (4 * c + r + 1 - 1) / 4 = c := by omega
  have e2 : 4 - (4 * c + r + 1 - 1) % 4 = 4 - r := by omega
  have e3 : 4 * c + (4 - r) - 1 = 4 * ((4 * c + r) / 4) + 3 - (4 * c + r) % 4 := by omega
  rw [e1, e2, e3, a0, a1, a2, a3]
  rw [te_byte 0 _ r (by omega) (a0 ▸ hb _) hr, te_byte 1 _ r (by omega) (a1 ▸ hb _) hr,
    te_byte 2 _ r (by omega) (a2 ▸ hb _) hr, te_byte 3 _ r (by omega) (a3 ▸ hb _) hr]
  ac_rfl

theorem init_inv (w pt : List Nat) (hpt : pt.length = 16) :
    ∀ f, f < 16 → weState (fun i => pt.getD i 0) w 0 (nval (f + 1)) = (rounds w pt 0).getD f 0 := by
  intro f hf
  simp only [weState, weInit, nvalInv_nval _ hf, Nat.add_sub_cancel, rounds]
  rw [addRoundKey_getD _ _ _ (by omega) (by rw [roundKey_length]; omega), keyRel w 0 f hf]

theorem state_inv (w pt : List Nat) (hpt : pt.length = 16) (hb : ∀ i, pt.getD i 0 < 256) :
    ∀ n f, f < 16 → weState (fun i => pt.getD i 0) w n (nval (f + 1)) = (rounds w pt n).getD f 0
  | 0 => init_inv w pt hpt
  | n + 1 => by
    intro f hf
    have := round_step w pt hpt n (weState (fun i => pt.getD i 0) w n)
      (weState_lt _ w hb n) (state_inv w pt hpt hb n) f hf
    exact this

theorem sbox_and255 (x : Nat) (hx : x < 256) : te4Lit x &&& 255 = sbox x := by
  rw [te4_lit x hx, and255]
  have := sbox_lt x hx
  omega

theorem src_pos : ∀ idx, idx < 16 → nval ((idx + 4 * (idx % 4)) % 16 + 1) = idx + 1 := by decide

/-- C15: the Write-Execute AES procedure computes the FIPS-197 cipher (given the expanded key). -/
theorem weCipher_eq (w pt : List Nat) (hpt : pt.length = 16) (hb : ∀ i, pt.getD i 0 < 256)
    (idx : Nat) (hidx : idx < 16) :
    weCipher (fun i => pt.getD i 0) w idx = (cipher w pt).getD idx 0 := by
  have hs9 := rounds_length w pt hpt 9
  have hinv := state_inv w pt hpt hb 9 ((idx + 4 * (idx % 4)) % 16) (by omega)
  rw [src_pos idx hidx] at hinv
  unfold weCipher weFinal cipher
  rw [addRoundKey_getD _ _ _ (by rw [shiftRows_length]; omega) (by rw [roundKey_length]; omega),
    shiftRows_getD _ _ hidx, subBytes_getD _ _ (by omega), Nat.add_sub_cancel, ← hinv,
    sbox_and255 _ (weState_lt _ w hb 9 _), keyRel w 10 idx hidx]

end WriteExecute.AES
