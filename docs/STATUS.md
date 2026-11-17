# Status

Updated: 2026-11-17

## Complete build, axiom audit, and Comparator record

The [verification record](validation/2026-11-17/README.md) now documents a
fresh rebuild of all 157 tracked Lean modules, the regression suite, and
successful kernel replay of all 157 modules. The inventory includes the
standalone `DualIrreducible` and `CenteredGibbsTower` modules that were not
covered by the earlier public-root builds. Mathematical sources, the
toolchain, and the pinned dependency manifest are unchanged.

The source scan found no `sorry`, `admit`, `sorryAx`, `native_decide`, custom
axiom/constant declarations, or unsafe code. The compiled audit checked all
2,673 project declarations: zero project axiom declarations, zero unsafe
declarations, and only `propext`, `Classical.choice`, and `Quot.sound` in
their transitive axiom dependencies. Each of the four audited headline
declarations has exactly these three standard dependencies.

Official Lean Comparator v4.30.0 accepted the actual public headline and a
proved equivalence with a separately written expanded paper contract. A
changed-statement control adding an assumption was rejected as expected.
The paper–Lean comparison links to the fixtures, reproduction procedure,
and complete logs. These are Lean-kernel checks, not an independent kernel
or a second mathematical proof.

The successful build logs retain five Lean 4.30 native-code-generation
`PANIC` diagnostics associated with `conjSpanTraceToDual`. All proof objects
were produced and passed kernel replay; execution of that auxiliary
definition's generated native code is not certified by this record.

Reproduction scripts live in `lean/scripts/`. CI now records the full
module inventory, axiom audit, and kernel replay and uploads the logs and
JSON as an artifact. The committed record is from the local run; a remote
CI result is a separate check. No environment configuration or publication
was changed for this milestone.

## Repository presentation and organization

The root README now gives a short natural-language theorem description and
links to the paper, Lean code, comparison, and project notes. The content is
organized under `paper/`, `lean/`, `comparison/`, and `docs/`; `paper/main.pdf`
is kept beside `paper/main.tex`. The Lean project and its toolchain, manifest,
and regression suite now live together under `lean/`, and CI uses that folder.
All Lean source files and the mathematical paper/figure files retain their
previous contents. Documentation links and the 19-page compiled PDF were checked.
The narrow headline build (3573 jobs) and regression suite (3587 jobs) passed
from `lean/`. Saved cloud setup instructions now use the new folder layout.

The requested repository name is
`Perimeter-law-lower-bound-for-center-neutral-Yang-Mills-theories`.
The GitHub rename remains pending: the running environment's network policy
blocks `api.github.com` (CONNECT/PATCH 403). The saved environment draft adds
that host while preserving the existing Mathlib cache domain. Applying the
running access change is required before retrying the rename; the saved draft
requires review/save and publication for future tasks. Repository visibility
has not been changed.

## Paper-aligned headline (complete)

The public headline now proves the paper's exact uniform-coupling conclusion:
one `C > 0` precedes every positive paper coupling, common translation-invariant
ordinary free-boundary limit, and rectangle. The finite law uses internal edges
and contained plaquettes; `n * beta` is proved to give the paper's character-sum
normalization. Common-limit uniqueness is derived from local observables.

The proof uses the short comb direction in the rectangle plane, establishes
both diagonal corner inequalities at every positive length, and compares with
the square of side `max(R,T)`. The fixed screening data yield an explicit
monomial/exponential seed and the `1 + beta + |log beta|` coefficient. The
strong-coupling corollary now specializes this strengthened headline.
Conservative one-edge numerical constants and implementation details are
recorded in `comparison/PAPER_LEAN_COMPARISON.md`; the manuscript is unchanged.

Validation completed with source-built dependencies:

- narrow headline build: 3573 jobs;
- public package build: 3577 jobs;
- `GluelumpPerimeterLawTests`: 3587 jobs;
- quantifier-order, all-length corner, neutral-import and standard-axiom guards;
- source placeholder/unsafe guards, overlay/module counts, and whitespace checks.

The headline uses only `propext`, `Classical.choice`, and `Quot.sound`. The
single direct dependency and locked revision are unchanged.

## Initial paper and Lean review

The earlier audit identified the qualitative headline's coupling quantifiers,
finite-law convention, and long-axis/cofinal corner geometry as differences.
The alignment milestone above resolves these headline differences and
supersedes that audit. The earlier manuscript edit clarified mixed author/LLM
writing and the author's review and responsibility; its PDF was rebuilt.

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
`paper/`. Its four existing figure
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
all-length short-axis corner closure, arbitrary rectangle transport, the
paper-convention ordinary-limit theorem, and the strong-coupling corollary.

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
