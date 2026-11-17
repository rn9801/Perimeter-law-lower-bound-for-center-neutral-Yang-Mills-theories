# Status

Updated: 2026-11-17

## Paper and Lean comparison

Recorded a source-level theorem and proof comparison in
`docs/PAPER_LEAN_COMPARISON.md`, including coupling normalization, finite-volume
packaging, the quantitative statement, and the collar-aware corner argument.
Updated the manuscript's AI acknowledgment to describe mixed author/LLM writing
and the author's review and responsibility. Rebuilt the PDF. No Lean sources
changed; fresh Lean validation remains blocked by missing dependency artifacts
and the Mathlib cache network restriction.

## Targeted manuscript revisions

Clarified infinite-volume convergence through continuous local observables and
revised the three requested passages: the one-edge bound, the tensor-generation
preamble, and the alternating-tensor example. The other three flagged passages
are unchanged. Rebuilt the manuscript PDF; no Lean sources changed.

## Manuscript proofreading

Completed a readthrough of the manuscript and the separate reflection-positivity
proof draft. Corrected grammar, punctuation and typography, and removed a stray
proof-ending symbol before a deferred proof. Mathematical statements and figures
are unchanged. Stylistic suggestions were reported separately without rewriting
the flagged wording. No Lean declarations changed.
Rebuilt the illustrated PDF with `latexmk` and BibTeX: 19 pages, with all
references and citations resolved.

## Manuscript illustrations

The supplied LaTeX manuscript is stored under
`docs/Gluelump_Perimeter_Law_Lower_Bound/`. Its four existing figure
references now have vector PDF diagrams and PNG previews, with a
reproducible generator in `figures/`. The generator checks the comb
half-space conditions for the two diagonal reflections. The mathematical
text and captions are unchanged; this documentation milestone changes no
Lean declarations.
The illustrated manuscript builds successfully with `latexmk` and BibTeX
(19 pages); all four figures were inspected in the rendered document.

The center-neutral infinite-volume gluelump perimeter-law lower bound is
proved.  The standalone package contains the direct conjugation-span endpoint,
uniform one-link positivity, physical-length reflection propagation,
collar-aware corner closure, arbitrary rectangle transport, the public
completed-limit theorem, and the concrete strong-coupling corollary.

Both center-neutral headline theorems now assume only that the Wilson
representation `rho` is center neutral; irreducibility was removed because
the proof never uses it. The result therefore applies to reducible
center-neutral representations as well. Irreducibility remains only in the
separate converse characterization of center neutrality by existence of a
nonzero screening intertwiner.

The headline declarations also no longer bind Haar positivity on nonempty
open sets as a separate typeclass hypothesis. Under the existing compact,
Borel, second-countable, normalized left-invariant Haar assumptions, Mathlib
synthesizes this property. A binder-free regression check records that fact.

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

The current public API and documentation milestone passes:

- focused narrow builds through the endpoint, one-link, straight, corner,
  public infinite-volume, and strong-coupling layers;
- the binder-free normalized-Haar full-support regression;
- `-DautoImplicit=false` checks on the critical representation, endpoint,
  propagation, and both headline sources;
- the production-plus-regression aggregate build (8,705 jobs);
- the default `lake build` (8,695 jobs); and
- focused axiom audits, including the primal target-type guard and the two
  anti-diagonal identities.

All three headline declarations still report exactly `propext`,
`Classical.choice`, and `Quot.sound`.

The README now records this repository-wide proof-integrity audit and
distinguishes the absence of hidden internal assumptions from the explicit
mathematical hypotheses in the theorem signatures.

The README now presents a paper-style mathematical formulation before any
Lean statements. It gives precise LaTeX definitions of the normalized Wilson
rectangle, center neutrality, the full-sequence completed free-boundary
limit, screening and one-link data, and the reflection interfaces, followed
by the three headline theorems with their exact quantifier scope and no proof
discussion. Its 37 display formulas use fenced GitHub `math` blocks and avoid
GitHub's unsupported `\operatorname` macro; the complete mathematical section
also compiles successfully with LaTeX. The nonessential Haar full-support
aside has been omitted from the paper-style presentation.

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
`rn9801/Central-neutral-perimeter-law-lower-bound`. The README title uses the
same repository name; the existing Lake package and Lean module names remain
stable. The committed Lake manifest resolves the unchanged upstream `main`
branch to
`bc7383d023f0c58a16312764a32422248aa42ebe`. A clean production-and-regression
build against that dependency completed successfully with 8,705 jobs.

There is no remaining mathematical proof or repository-extraction gap in the
stated theorem. If a future upstream `main` absorbs an overlaid declaration,
its downstream extension must be removed in the same compatibility update to
avoid duplicate ownership.
