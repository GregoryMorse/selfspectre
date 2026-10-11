module
public import WriteExecute.Spec.AESData

public section

/-! AES-128 (FIPS-197) and the Write-Execute AES procedure (writeexc.asm: WriteExecAESLookup).
States are lists of 16 bytes in FIPS order (byte `4c + r` is row `r` of column `c`). -/

namespace WriteExecute.AES

/-! GF(2^8) and the S-box. -/

@[expose] def xtime (x : Nat) : Nat := ((x <<< 1) ^^^ (if x &&& 128 ≠ 0 then 0x1b else 0)) &&& 255

@[expose] def gmulAux : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | k + 1, a, b => (if b % 2 = 1 then a else 0) ^^^ gmulAux k (xtime a) (b / 2)

@[expose] def gmul (a b : Nat) : Nat := gmulAux 8 a b

@[expose] def gpow (x : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => gmul x (gpow x n)

@[expose] def rotl8 (b n : Nat) : Nat := ((b <<< n) ||| (b >>> (8 - n))) &&& 255

/-- The S-box of FIPS-197 (table `sboxTab`); `sbox_alg` proves it is the inverse in GF(2^8)
followed by the affine map. -/
@[expose] def sbox (x : Nat) : Nat := sboxTab.getD x 0

/-- Multiplicative inverse in GF(2^8) (`x^254`, with `0 ↦ 0`) followed by the affine map. -/
@[expose] def sboxAlg (x : Nat) : Nat :=
  let b := gpow x 254
  b ^^^ rotl8 b 1 ^^^ rotl8 b 2 ^^^ rotl8 b 3 ^^^ rotl8 b 4 ^^^ 0x63

/-! The cipher. -/

abbrev St := List Nat

@[expose] def subBytes (s : St) : St := s.map sbox
@[expose] def shiftRows (s : St) : St := (List.range 16).map fun i => s.getD ((i + 4 * (i % 4)) % 16) 0
@[expose] def mixCol (a0 a1 a2 a3 : Nat) : Nat × Nat × Nat × Nat :=
  (xtime a0 ^^^ (xtime a1 ^^^ a1) ^^^ a2 ^^^ a3,
   a0 ^^^ xtime a1 ^^^ (xtime a2 ^^^ a2) ^^^ a3,
   a0 ^^^ a1 ^^^ xtime a2 ^^^ (xtime a3 ^^^ a3),
   (xtime a0 ^^^ a0) ^^^ a1 ^^^ a2 ^^^ xtime a3)
@[expose] def mixColumns (s : St) : St := (List.range 16).map fun i =>
  let c := i / 4
  let m := mixCol (s.getD (4 * c) 0) (s.getD (4 * c + 1) 0) (s.getD (4 * c + 2) 0) (s.getD (4 * c + 3) 0)
  match i % 4 with
  | 0 => m.1
  | 1 => m.2.1
  | 2 => m.2.2.1
  | _ => m.2.2.2
@[expose] def addRoundKey (s k : St) : St := List.zipWith (· ^^^ ·) s k

/-! Key expansion: 44 words, round key `r` is words `4r .. 4r+3`, most significant byte first. -/

@[expose] def subWord (w : Nat) : Nat :=
  sbox (w >>> 24 &&& 255) <<< 24 ||| sbox (w >>> 16 &&& 255) <<< 16 ||| sbox (w >>> 8 &&& 255) <<< 8 |||
    sbox (w &&& 255)
@[expose] def rotWord (w : Nat) : Nat := ((w <<< 8) ||| (w >>> 24)) &&& 0xFFFFFFFF
@[expose] def rcon (i : Nat) : Nat := (List.getD [1, 2, 4, 8, 16, 32, 64, 128, 0x1b, 0x36] (i - 1) 0) <<< 24

@[expose] def keyStep (key : St) (l : List Nat) : List Nat :=
  let n := l.length
  l ++ [if n < 4 then
      (key.getD (4 * n) 0 <<< 24) ||| (key.getD (4 * n + 1) 0 <<< 16) |||
        (key.getD (4 * n + 2) 0 <<< 8) ||| key.getD (4 * n + 3) 0
    else
      l.getD (n - 4) 0 ^^^ (if n % 4 = 0 then subWord (rotWord (l.getD (n - 1) 0)) ^^^ rcon (n / 4)
        else l.getD (n - 1) 0)]

@[expose] def keyWords (key : St) : List Nat := (List.range 44).foldl (fun l _ => keyStep key l) []

/-- Round key `r` as a state (byte `i` = byte `i % 4` of word `4r + i / 4`, most significant first). -/
@[expose] def roundKey (w : List Nat) (r : Nat) : St :=
  (List.range 16).map fun i => (w.getD (4 * r + i / 4) 0 >>> (8 * (3 - i % 4))) &&& 255

@[expose] def fipsRound (rk : St) (s : St) : St := addRoundKey (mixColumns (shiftRows (subBytes s))) rk

@[expose] def rounds (w : List Nat) (pt : St) : Nat → St
  | 0 => addRoundKey pt (roundKey w 0)
  | r + 1 => fipsRound (roundKey w (r + 1)) (rounds w pt r)

@[expose] def cipher (w : List Nat) (pt : St) : St :=
  addRoundKey (shiftRows (subBytes (rounds w pt 9))) (roundKey w 10)

@[expose] def aes128 (key pt : St) : St := cipher (keyWords key) pt

/-! The T-table cipher of spectreopt.c / writeexec.c, and the Write-Execute AES procedure. -/

@[expose] def teLit (k x : Nat) : Nat :=
  List.getD (match k with | 0 => litTe0 | 1 => litTe1 | 2 => litTe2 | _ => litTe3) x 0
@[expose] def te4Lit (x : Nat) : Nat := litTe4.getD x 0

/-- Multiplication by the MixColumns constants 1, 2, 3. -/
@[expose] def mulc (c a : Nat) : Nat := if c = 1 then a else if c = 2 then xtime a else xtime a ^^^ a

/-- Coefficient of row `r` in table `Te_k`: row `(r - k) mod 4` of the column `[2, 1, 1, 3]`. -/
@[expose] def tcoef (k r : Nat) : Nat := [2, 1, 1, 3].getD ((r + 4 - k) % 4) 0

/-- Byte `m` (1-based, least significant first) of a word. -/
@[expose] def lbyte (t m : Nat) : Nat := (t >>> (8 * (m - 1))) &&& 255

/-- Destination position (1..16) of the byte with FIPS index `qq - 1`; this is the ShiftRows
placement of the asm (`1 + ((17 - qq) * 3) mod 16`) and its inverse. -/
@[expose] def nval (qq : Nat) : Nat := 1 + ((17 - qq) * 3) % 16
@[expose] def nvalInv (p : Nat) : Nat := 1 + (16 - ((p - 1) * 11) % 16) % 16

/-- The round key bytes as stored by `AES_set_encrypt_key` on a little-endian machine:
memory byte `j` is byte `j % 4` (least significant first) of word `j / 4`. -/
@[expose] def keyMem (w : List Nat) (r j : Nat) : Nat :=
  (w.getD (4 * r + j / 4) 0 >>> (8 * (j % 4))) &&& 255

/-- AESINIT: plaintext byte `v` xor round-0 key byte, stored at `nval v`. -/
@[expose] def weInit (inp : Nat → Nat) (K : Nat → Nat) (p : Nat) : Nat :=
  let v := nvalInv p
  inp (v - 1) ^^^ K (4 * ((v - 1) / 4) + 3 - (v - 1) % 4)

/-- AESTABLE/AESXORMIX for one round: the output byte (column `c`, byte `m`) is the key byte xor the
four table words `Te0..Te3` of the four consecutive state bytes, stored at `nval qq`. -/
@[expose] def weOut (sw K : Nat → Nat) (c m : Nat) : Nat :=
  K (4 * c + m - 1) ^^^ lbyte (teLit 0 (sw (4 * c + 1))) m ^^^ lbyte (teLit 1 (sw (4 * c + 2))) m ^^^
    lbyte (teLit 2 (sw (4 * c + 3))) m ^^^ lbyte (teLit 3 (sw (4 * c + 4))) m

@[expose] def weRound (sw K : Nat → Nat) (p : Nat) : Nat :=
  let qq := nvalInv p
  weOut sw K ((qq - 1) / 4) (4 - (qq - 1) % 4)

/-- AESFIN: last round, `Te4` (the S-box byte) xor key byte `rval`. -/
@[expose] def weFinal (sw K : Nat → Nat) (v : Nat) : Nat :=
  (te4Lit (sw v) &&& 255) ^^^ K (4 * ((v - 1) / 4) + 3 - (v - 1) % 4)

/-- State after round `n` (n = 0 is after AESINIT), as a function of positions `1..16`. -/
@[expose] def weState (inp : Nat → Nat) (w : List Nat) : Nat → Nat → Nat
  | 0 => weInit inp (keyMem w 0)
  | n + 1 => weRound (weState inp w n) (keyMem w (n + 1))

@[expose] def weCipher (inp : Nat → Nat) (w : List Nat) (idx : Nat) : Nat :=
  weFinal (weState inp w 9) (keyMem w 10) (idx + 1)

end WriteExecute.AES
