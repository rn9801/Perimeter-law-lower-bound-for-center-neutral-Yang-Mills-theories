# Status

Updated: 2026-08-25

The center-neutral infinite-volume gluelump perimeter-law lower bound is
proved.  The standalone package contains the direct conjugation-span endpoint,
uniform one-link positivity, physical-length reflection propagation,
collar-aware corner closure, arbitrary rectangle transport, the public
completed-limit theorem, and the concrete strong-coupling corollary.

## Verified theorem boundary

- The neutral critical path has no transitive `YangMills.StrongCoupling` or
  `YangMills.Polymer` import.
- Strong-coupling construction appears only in downstream adapter and
  corollary modules.
- The package directly requires only the `main` branch of
  `rn9801/strong-coupling-lattice-yang-mills`.
- Headline axiom footprints contain only `propext`, `Classical.choice`, and
  `Quot.sound`.
- The critical source path contains no `sorry`, `admit`, custom axiom, or
  unsafe declaration.

## Current milestone

The remaining work is repository publication and continuing compatibility
checks against upstream `main`; there is no remaining mathematical proof gap
in the stated theorem.
