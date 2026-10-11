module
public import WriteExecute.X86.Fig6
public import WriteExecute.X86.LayoutData

public section

/-! Fig. 6 (C18) at the section offsets of the assembled `writeexc.obj`: published source (`x86`, `x64`) and corrected
source (`x86c`, `x64c`; the XOR code is the same, only its offset moves). -/

namespace WriteExecute.X86

/-- C18 (Fig. 6), `x86` layout of `writeexc.asm`: for every pair of argument bytes `k1`, `k2`, execution from `xorarg1`
reaches the return jump target `Dd - 1` after `38` steps, having stored `k1 xor k2` at `Dd`; every write is to an
instruction field (`XorW86`). The image fields may hold any stale value, so the procedure is re-executable. -/
theorem fig6_x86 (B0 : Nat) (m : Mem) (Dd k1 k2 d01 w01 r01 d02 w02 r02 d1 c1 rL vJ d2 c2s wJ b0 : Nat) (v : Nat → Nat)
    (hk1 : k1 < 256) (hk2 : k2 < 256) (hbig : B0 + x86_xorarg1 + 2 ^ 22 < 2 ^ 30)
    (hDd : B0 + x86_xorres + 12 ≤ Dd) (hDb : Dd + 1 < 2 ^ 30) (hv : ∀ i, i < 256 → v i < 65536)
    (hvJ : vJ < 65536) (hwJ : wJ < 65536) (hb0 : b0 < 256) (hrL : rL < 256)
    (img : XorImg86 m (B0 + x86_xorarg1) (B0 + x86_shlarg5) (B0 + x86_shlarg4) (B0 + x86_xorres) Dd k1 k2
      d01 w01 r01 d02 w02 r02 d1 c1 rL vJ d2 c2s wJ b0 v) :
    ∃ mEnd, runN Mode.x86 38 (B0 + x86_xorarg1, m) = some (Dd - 1, mEnd) ∧ mEnd Dd = k1 ^^^ k2 ∧
      ∀ x, ¬XorW86 (B0 + x86_xorarg1) (B0 + x86_shlarg5) (B0 + x86_shlarg4) (B0 + x86_xorres) Dd k1 x →
        mEnd x = m x := by
  have g := x86_xor_geometry
  have g0 := x86_geometry
  exact xor_exec_x86 m (B0 + x86_xorarg1) (B0 + x86_shlarg5) (B0 + x86_shlarg4) (B0 + x86_xorres) Dd k1 k2
    d01 w01 r01 d02 w02 r02 d1 c1 rL vJ d2 c2s wJ b0 v hk1 hk2 (by omega) (by omega) hbig (by omega) hDd hDb hv hvJ hwJ hb0 hrL img

/-- C18 (Fig. 6), `x64` layout of `writeexc.asm`: for every pair of argument bytes `k1`, `k2`, execution from `xorarg1`
reaches the return jump target `Dd - 1` after `35` steps, having stored `k1 xor k2` at `Dd`; every write is to an
instruction field (`XorW64`). The image fields may hold any stale value, so the procedure is re-executable. -/
theorem fig6_x64 (B0 : Nat) (m : Mem) (Dd k1 k2 d01 w01 r01 d02 w02 r02 d1 c1 rL c2s wH wJ b0 : Nat) (v : Nat → Nat)
    (hk1 : k1 < 256) (hk2 : k2 < 256) (hbig : B0 + x64_xorarg1 + 2 ^ 22 < 2 ^ 30)
    (hDd : B0 + x64_xorres + 12 ≤ Dd) (hDb : Dd + 1 < 2 ^ 30) (hv : ∀ i, i < 256 → v i < 65536)
    (hwH : wH < 65536) (hwJ : wJ < 65536) (hb0 : b0 < 256) (hrL : rL < 256)
    (img : XorImg64 m (B0 + x64_xorarg1) (B0 + x64_shlarg5) (B0 + x64_shlarg4) (B0 + x64_xorres) Dd k1 k2
      d01 w01 r01 d02 w02 r02 d1 c1 rL c2s wH wJ b0 v) :
    ∃ mEnd, runN Mode.x64 35 (B0 + x64_xorarg1, m) = some (Dd - 1, mEnd) ∧ mEnd Dd = k1 ^^^ k2 ∧
      ∀ x, ¬XorW64 (B0 + x64_xorarg1) (B0 + x64_shlarg5) (B0 + x64_shlarg4) (B0 + x64_xorres) Dd k1 x →
        mEnd x = m x := by
  have g := x64_xor_geometry
  have g0 := x64_geometry
  exact xor_exec_x64 m (B0 + x64_xorarg1) (B0 + x64_shlarg5) (B0 + x64_shlarg4) (B0 + x64_xorres) Dd k1 k2
    d01 w01 r01 d02 w02 r02 d1 c1 rL c2s wH wJ b0 v hk1 hk2 (by omega) (by omega) hbig (by omega) hDd hDb hv hwH hwJ hb0 hrL img

/-- C18 (Fig. 6), `x86c` layout of `writeexc.asm`: for every pair of argument bytes `k1`, `k2`, execution from `xorarg1`
reaches the return jump target `Dd - 1` after `38` steps, having stored `k1 xor k2` at `Dd`; every write is to an
instruction field (`XorW86`). The image fields may hold any stale value, so the procedure is re-executable. -/
theorem fig6_x86c (B0 : Nat) (m : Mem) (Dd k1 k2 d01 w01 r01 d02 w02 r02 d1 c1 rL vJ d2 c2s wJ b0 : Nat) (v : Nat → Nat)
    (hk1 : k1 < 256) (hk2 : k2 < 256) (hbig : B0 + x86c_xorarg1 + 2 ^ 22 < 2 ^ 30)
    (hDd : B0 + x86c_xorres + 12 ≤ Dd) (hDb : Dd + 1 < 2 ^ 30) (hv : ∀ i, i < 256 → v i < 65536)
    (hvJ : vJ < 65536) (hwJ : wJ < 65536) (hb0 : b0 < 256) (hrL : rL < 256)
    (img : XorImg86 m (B0 + x86c_xorarg1) (B0 + x86c_shlarg5) (B0 + x86c_shlarg4) (B0 + x86c_xorres) Dd k1 k2
      d01 w01 r01 d02 w02 r02 d1 c1 rL vJ d2 c2s wJ b0 v) :
    ∃ mEnd, runN Mode.x86 38 (B0 + x86c_xorarg1, m) = some (Dd - 1, mEnd) ∧ mEnd Dd = k1 ^^^ k2 ∧
      ∀ x, ¬XorW86 (B0 + x86c_xorarg1) (B0 + x86c_shlarg5) (B0 + x86c_shlarg4) (B0 + x86c_xorres) Dd k1 x →
        mEnd x = m x := by
  have g := x86c_xor_geometry
  have g0 := x86c_geometry
  exact xor_exec_x86 m (B0 + x86c_xorarg1) (B0 + x86c_shlarg5) (B0 + x86c_shlarg4) (B0 + x86c_xorres) Dd k1 k2
    d01 w01 r01 d02 w02 r02 d1 c1 rL vJ d2 c2s wJ b0 v hk1 hk2 (by omega) (by omega) hbig (by omega) hDd hDb hv hvJ hwJ hb0 hrL img

/-- C18 (Fig. 6), `x64c` layout of `writeexc.asm`: for every pair of argument bytes `k1`, `k2`, execution from `xorarg1`
reaches the return jump target `Dd - 1` after `35` steps, having stored `k1 xor k2` at `Dd`; every write is to an
instruction field (`XorW64`). The image fields may hold any stale value, so the procedure is re-executable. -/
theorem fig6_x64c (B0 : Nat) (m : Mem) (Dd k1 k2 d01 w01 r01 d02 w02 r02 d1 c1 rL c2s wH wJ b0 : Nat) (v : Nat → Nat)
    (hk1 : k1 < 256) (hk2 : k2 < 256) (hbig : B0 + x64c_xorarg1 + 2 ^ 22 < 2 ^ 30)
    (hDd : B0 + x64c_xorres + 12 ≤ Dd) (hDb : Dd + 1 < 2 ^ 30) (hv : ∀ i, i < 256 → v i < 65536)
    (hwH : wH < 65536) (hwJ : wJ < 65536) (hb0 : b0 < 256) (hrL : rL < 256)
    (img : XorImg64 m (B0 + x64c_xorarg1) (B0 + x64c_shlarg5) (B0 + x64c_shlarg4) (B0 + x64c_xorres) Dd k1 k2
      d01 w01 r01 d02 w02 r02 d1 c1 rL c2s wH wJ b0 v) :
    ∃ mEnd, runN Mode.x64 35 (B0 + x64c_xorarg1, m) = some (Dd - 1, mEnd) ∧ mEnd Dd = k1 ^^^ k2 ∧
      ∀ x, ¬XorW64 (B0 + x64c_xorarg1) (B0 + x64c_shlarg5) (B0 + x64c_shlarg4) (B0 + x64c_xorres) Dd k1 x →
        mEnd x = m x := by
  have g := x64c_xor_geometry
  have g0 := x64c_geometry
  exact xor_exec_x64 m (B0 + x64c_xorarg1) (B0 + x64c_shlarg5) (B0 + x64c_shlarg4) (B0 + x64c_xorres) Dd k1 k2
    d01 w01 r01 d02 w02 r02 d1 c1 rL c2s wH wJ b0 v hk1 hk2 (by omega) (by omega) hbig (by omega) hDd hDb hv hwH hwJ hb0 hrL img

end WriteExecute.X86
