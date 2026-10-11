# Errata policy

Preserve the published algorithm and make the smallest local correction that states its intended,
provable result. Quote the published PDF exactly (`validation/reference/tmmp-2019-0010.pdf`), never
the pre-final draft. Do not attribute extraction artifacts to the paper.

Classes: `formal` (cites Lean declarations), `mechanical` (cites layout/native evidence),
`editorial` (cites a primary source or an unambiguous internal inconsistency). The author is not
available to adjudicate; an item is recorded when the code, the architecture of the time (x86/x86-64
with MASM) or the published text itself make it very likely, or when simple code confirmation settles it.
Evidence (native tests, layout comparison) is never described as proof. Code fixes are minimal diffs
with a native re-test. Keep the published errata compact.
