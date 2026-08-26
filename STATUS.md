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
- Strong-coupling construction appears only in downstream compatibility,
  adapter, and corollary modules.
- The package directly requires only the `main` branch of
  `rn9801/strong-coupling-lattice-yang-mills`.
- The upstream repository is unchanged. The 28 additive prerequisites needed
  by this proof are owned here under `GluelumpPerimeterLaw.Upstream.*` (19
  extensions of existing modules and nine new modules).
- Headline axiom footprints contain only `propext`, `Classical.choice`, and
  `Quot.sound`.
- The critical source path contains no `sorry`, `admit`, custom axiom, or
  unsafe declaration.

The standalone tree has 110 gluelump theorem modules, 28 compatibility
modules, and 10 focused regression modules.

## Current milestone

The standalone repository is published privately at
`rn9801/gluelump-perimeter-law`. Its committed Lake manifest resolves the
unchanged upstream `main` branch to
`bc7383d023f0c58a16312764a32422248aa42ebe`. A clean production-and-regression
build against that dependency completed successfully with 8,708 jobs.

There is no remaining mathematical proof or repository-extraction gap in the
stated theorem. If a future upstream `main` absorbs an overlaid declaration,
its downstream extension must be removed in the same compatibility update to
avoid duplicate ownership.
