module

public section

namespace WriteExecute.Spectre

/-- Order in which the 256 probe lines are timed (spectre.c: `mix_i = ((i * 167) + 13) & 255`). -/
@[expose] def mixIdx (i : Nat) : Nat := (i * 167 + 13) % 256

/-- Fig. 1: branch-free selection of the malicious index. `r = j % 6` (`w` is the width of `size_t`).
`(r - 1)` is a signed `int` converted to `size_t`, `~0xFFFF` the `int` complement of `0xFFFF`. -/
@[expose] def selX0 (w r : Nat) : BitVec w := BitVec.ofInt w ((r : Int) - 1) &&& ~~~(0xFFFF#w)
@[expose] def selX1 (w r : Nat) : BitVec w := selX0 w r ||| (selX0 w r >>> 16)
@[expose] def selectIdx (w j : Nat) (t m : BitVec w) : BitVec w :=
  t ^^^ (selX1 w (j % 6) &&& (m ^^^ t))

end WriteExecute.Spectre
