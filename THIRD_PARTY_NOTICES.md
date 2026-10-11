# Third-party notices

The project license (MIT, see `LICENSE`) covers the original code, the Lean development and the
documents of this repository. The following material is third-party and is referenced for attribution.

`spectre.c` is the original Spectre v1 proof-of-concept from:

  Paul Kocher, Jann Horn, Anders Fogh, Daniel Genkin, Daniel Gruss,
  Werner Haas, Mike Hamburg, Moritz Lipp, Stefan Mangard, Thomas Prescher,
  Michael Schwarz, Yuval Yarom.
  "Spectre Attacks: Exploiting Speculative Execution."
  IEEE Symposium on Security & Privacy, 2019.
  https://spectreattack.com/spectre.pdf

It is included in this repository for reference purposes only, with minor
modifications to fix compilation warnings as noted in the file header.

`lean/WriteExecute/Base/{Memory,Turing,MathlibTM0}.lean` are adapted from the author's own smcTuring
development (CC0-1.0); see `lean/VENDORED.md`.

The published paper (`validation/reference/tmmp-2019-0010.pdf`) is distributed by the publisher under
the terms stated in the PDF and is not covered by the MIT license; see `lean/LICENSE_AUDIT.md`.
