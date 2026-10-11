# License check — 2026-10-11

* Project license: **MIT**, declared as `project.license: "MIT"` in `formalization.yaml`.
  The root file `LICENSE` is the standard MIT text (copyright 2019 Gregory Morse) and nothing else, so that
  GitHub's license detection reports `MIT`. (Before this audit the file also carried a notice for the
  third-party `spectre.c`, which made GitHub report `other`; that notice moved to `THIRD_PARTY_NOTICES.md`.)
  Re-check after the push: `gh api repos/GregoryMorse/selfspectre/license`.
* Vendored Lean base definitions (`lean/WriteExecute/Base/`): adapted from the author's own smcTuring
  development (CC0-1.0, commit `1ab379c2288ef5952c6e1bbdb8d655d31e5fbbd4`); see `VENDORED.md`. CC0 permits
  relicensing under MIT.
* Third-party code: `spectre.c` (Kocher et al., Spectre v1 proof of concept, reference only), see
  `THIRD_PARTY_NOTICES.md`. Dependencies (Mathlib and its packages) keep their own licenses (Apache-2.0).
* The published paper `validation/reference/tmmp-2019-0010.pdf` states "Licensed under the Creative Commons
  Attribution-NC-ND 4.0 International Public License" (p. 1). It is included unchanged, attributed and
  separately licensed for quotation by the errata; the repository's MIT license does not relicense it.
  Errata quote short excerpts of the published text with page references.
