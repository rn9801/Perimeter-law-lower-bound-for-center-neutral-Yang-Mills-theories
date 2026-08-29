# Status

Updated: 2026-08-29

The center-neutral infinite-volume gluelump perimeter-law lower bound is
proved.  The standalone package contains the direct conjugation-span endpoint,
uniform one-link positivity, physical-length reflection propagation,
collar-aware corner closure, arbitrary rectangle transport, the public
completed-limit theorem, and the concrete strong-coupling corollary.

Both headline theorems now assume only that the Wilson representation `rho`
is center neutral; irreducibility was removed because the proof never uses it.
The result therefore applies to reducible center-neutral representations as
well. Irreducibility remains only in the separate converse characterization
of center neutrality by existence of a nonzero screening intertwiner.

The operational endpoint has now been simplified to use a primal screening
map

```text
(ConjSpan sigma)^⊗m → rho
```

directly.  `conjSpanPhi` is `rho`-valued and transforms by the ordinary
representation action.  No active endpoint, one-link, propagation, or
headline declaration uses the former dual-target construction.  The
anti-diagonal closure uses conjugated holonomy matrix components and an exact
Wilson-loop reversal/conjugation identity, so the public real lower bound and
all theorem statements are unchanged.

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
- All repository-owned Lean sources contain no `sorry`, `admit`, `sorryAx`,
  custom `axiom` or `constant` declaration, or `unsafe` declaration. A
  compiled audit of every project declaration found no nonstandard axiom
  dependency; the five opaque definitions all have kernel-checked bodies.

The standalone tree has 110 gluelump theorem modules, 28 compatibility
modules, and 10 focused regression modules.

## Current milestone

The primal-screening migration passes:

- focused narrow builds through the endpoint, one-link, straight, corner,
  public infinite-volume, and strong-coupling layers;
- `-DautoImplicit=false` checks on the critical representation, endpoint,
  propagation, and both headline sources;
- the production-plus-regression aggregate build (8,707 jobs);
- the default `lake build` (8,695 jobs); and
- focused axiom audits, including the primal target-type guard and the two
  anti-diagonal identities.

All three headline declarations still report exactly `propext`,
`Classical.choice`, and `Quot.sound`.

The README now records this repository-wide proof-integrity audit and
distinguishes the absence of hidden internal assumptions from the explicit
mathematical hypotheses in the theorem signatures.

The README now also presents a standalone ordinary-language formulation
before any Lean statements. It defines the normalized Wilson rectangle,
center neutrality, the full-sequence completed free-boundary limit,
screening and one-link data, and the reflection interfaces, then states all
three headline theorems with their exact uniformity and quantifier scope.

The README now presents the exact Lean signatures of the main
completed-limit theorem, its concrete strong-coupling corollary, and the
model-neutral one-link-to-perimeter propagation theorem.  It also records the
full-sequence nature of the current thermodynamic-limit hypothesis and the
uniform dependencies of the perimeter rate.

The same headline section now expands the exact definitions of center
neutrality, the translation-invariant completed free-boundary limit, and the
complex and real rectangle expectations.  It also documents the reflection,
crossing-link, and coordinate-swap interfaces used by the model-neutral
propagation theorem.

## Repository publication

The standalone repository is published privately at
`rn9801/gluelump-perimeter-law`. Its committed Lake manifest resolves the
unchanged upstream `main` branch to
`bc7383d023f0c58a16312764a32422248aa42ebe`. A clean production-and-regression
build against that dependency completed successfully with 8,708 jobs.

There is no remaining mathematical proof or repository-extraction gap in the
stated theorem. If a future upstream `main` absorbs an overlaid declaration,
its downstream extension must be removed in the same compatibility update to
avoid duplicate ownership.
