module
public import WriteExecute.AES.Basic

public section

/-! C21: the AES-NI sequence of Fig. 3 / `AES_encrypt_intrin` (spectreopt.c): `pxor` with round key 0, nine
`aesenc`, one `aesenclast`. The instructions follow the Intel SDM pseudocode (ShiftRows, SubBytes,
MixColumns, xor with the round key; the last round omits MixColumns). Round keys are 16-byte blocks in
FIPS order; the key schedule instruction `aeskeygenassist` is not modeled. -/

namespace WriteExecute.AES

/-- `AESENC`: ShiftRows, SubBytes, MixColumns, xor round key (SDM order). -/
@[expose] def aesenc (s rk : St) : St := addRoundKey (mixColumns (subBytes (shiftRows s))) rk

/-- `AESENCLAST`: ShiftRows, SubBytes, xor round key. -/
@[expose] def aesenclast (s rk : St) : St := addRoundKey (subBytes (shiftRows s)) rk

/-- `pxor` with `rk 0` followed by `r` `aesenc` instructions with `rk 1 .. rk r`. -/
@[expose] def niRounds (rk : Nat → St) (pt : St) : Nat → St
  | 0 => addRoundKey pt (rk 0)
  | r + 1 => aesenc (niRounds rk pt r) (rk (r + 1))

@[expose] def aesNi (rk : Nat → St) (pt : St) : St := aesenclast (niRounds rk pt 9) (rk 10)

theorem subBytes_shiftRows (s : St) (h : s.length = 16) :
    subBytes (shiftRows s) = shiftRows (subBytes s) := by
  unfold subBytes shiftRows
  simp only [List.map_map]
  apply List.map_congr_left
  intro i hi
  have hi' : i < 16 := List.mem_range.mp hi
  have hj : (i + 4 * (i % 4)) % 16 < s.length := by omega
  simp [Function.comp, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem niRounds_eq (w pt : List Nat) (hpt : pt.length = 16) :
    ∀ n, niRounds (roundKey w) pt n = rounds w pt n
  | 0 => rfl
  | n + 1 => by
    have ih := niRounds_eq w pt hpt n
    have hl := rounds_length w pt hpt n
    show aesenc (niRounds (roundKey w) pt n) (roundKey w (n + 1)) = fipsRound (roundKey w (n + 1)) (rounds w pt n)
    rw [ih]
    unfold aesenc fipsRound
    rw [subBytes_shiftRows _ hl]

/-- C21: with the FIPS-197 round keys, the AES-NI sequence computes AES-128. -/
theorem aesNi_eq (w pt : List Nat) (hpt : pt.length = 16) : aesNi (roundKey w) pt = cipher w pt := by
  unfold aesNi aesenclast cipher
  rw [niRounds_eq w pt hpt 9, subBytes_shiftRows _ (rounds_length w pt hpt 9)]

end WriteExecute.AES
