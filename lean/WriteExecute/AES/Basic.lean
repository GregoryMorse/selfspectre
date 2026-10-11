module
public import WriteExecute.AES.Checks

public section

namespace WriteExecute.AES

open WriteExecute.Arith

theorem xtime_lt (x : Nat) : xtime x < 256 := by
  unfold xtime
  have := Nat.and_le_right (n := (x <<< 1) ^^^ (if x &&& 128 ≠ 0 then 0x1b else 0)) (m := 255)
  omega

theorem xor_lt256 {a b : Nat} (ha : a < 256) (hb : b < 256) : a ^^^ b < 256 :=
  Nat.xor_lt_two_pow (n := 8) ha hb

theorem and255_lt (x : Nat) : x &&& 255 < 256 := by rw [and255]; omega

theorem subBytes_length (s : St) : (subBytes s).length = s.length := by simp [subBytes]
theorem shiftRows_length (s : St) : (shiftRows s).length = 16 := by simp [shiftRows]
theorem mixColumns_length (s : St) : (mixColumns s).length = 16 := by simp [mixColumns]
theorem roundKey_length (w : List Nat) (r : Nat) : (roundKey w r).length = 16 := by simp [roundKey]
theorem addRoundKey_length (s k : St) : (addRoundKey s k).length = min s.length k.length := by
  simp [addRoundKey]

theorem rounds_length (w pt : List Nat) (h : pt.length = 16) : ∀ n, (rounds w pt n).length = 16
  | 0 => by simp [rounds, addRoundKey_length, roundKey_length, h]
  | n + 1 => by
    simp only [rounds, fipsRound, addRoundKey_length, mixColumns_length, roundKey_length]
    omega

theorem addRoundKey_getD (s k : St) (i : Nat) (hs : i < s.length) (hk : i < k.length) :
    (addRoundKey s k).getD i 0 = s.getD i 0 ^^^ k.getD i 0 := by
  have h : i < (List.zipWith (· ^^^ ·) s k).length := by simp; omega
  simp only [addRoundKey, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h,
    List.getElem?_eq_getElem hs, List.getElem?_eq_getElem hk, List.getElem_zipWith]
  rfl

theorem subBytes_getD (s : St) (i : Nat) (hs : i < s.length) :
    (subBytes s).getD i 0 = sbox (s.getD i 0) := by
  simp [subBytes, List.getD_eq_getElem?_getD, hs]

theorem shiftRows_getD (t : St) (f : Nat) (hf : f < 16) :
    (shiftRows t).getD f 0 = t.getD ((f + 4 * (f % 4)) % 16) 0 := by
  simp [shiftRows, List.getD_eq_getElem?_getD, hf]

end WriteExecute.AES
