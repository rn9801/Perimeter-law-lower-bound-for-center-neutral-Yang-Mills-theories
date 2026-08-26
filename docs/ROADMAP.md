# Center-neutral gluelump perimeter law: implementation record

Updated: 2026-08-25

This is the numbered implementation and extraction record for
`CenterNeutralInfiniteVolumePerimeterLaw`. Completed tasks remain in the file
so later work can refer to stable task numbers and the original design
decisions.

## Target and completed foundation

The target is the infinite-volume theorem for a faithful action
representation `sigma`, an irreducible center-neutral Wilson representation
`rho`, positive coupling, and an arbitrary translation-invariant limit of the
completed free-boundary reflection boxes. The rate must be chosen before the
limiting measure, basepoint, coordinate plane, and rectangle side lengths.

The following difficult inputs are already formalized:

- center neutrality and faithfulness produce a nonzero conjugation-span
  screening intertwiner;
- the normalized Higgs-like endpoint `conjSpanPhi` is finite-range,
  gauge-covariant, nonzero, and pointwise bounded by one;
- the direct reflected one-bond observable has an exact gauge-fixed finite
  Gram-family factorization;
- its finite-volume expectation has a strictly positive lower bound, uniform
  over every admissible finite specification, for every `beta > 0`;
- the abstract link, site, diagonal, anti-diagonal, and rectangle
  Cauchy--Schwarz identities are proved;
- the numerical theorem
  `MeasureReflectionPropagationCertificate.perimeterLowerBound_of_seed`
  turns a positive seed and a completed reflection certificate into

  ```text
  (q^2 / D)^(2 * (R + T)) <= Re E[rectangle R T];
  ```

- the existing strong-coupling infinite-volume probability satisfies the
  completed-free-boundary local-limit and translation-invariance hypothesis.

The work recorded below was therefore an integration and geometry project
rather than a new representation-theoretic or analytic argument. Tasks 1--6
prove and audit the theorem. Task 7 records its extraction into this
standalone package.

## Critical path

Tasks 1 and 2 can begin in parallel. The main dependency chain is

```text
Tasks 1 and 2  ->  Task 3  ->  Task 4  ->  Task 5  ->  Task 6.
```

Task 7 is the repository split performed after the theorem stabilized. Its
architectural constraints guided every earlier task.

## Repository boundary

This package is separate from the strong-coupling Yang--Mills repository. It
uses that repository's `main` branch as its sole direct Lake dependency for
the common lattice, gauge, Wilson, reflection, and thermodynamic-limit
interfaces.

The resulting package dependency graph is

```text
strong-coupling-lattice-yang-mills main -> gluelump-perimeter-law
```

More explicitly:

1. The upstream repository provides sites, links, paths, plaquettes, Haar
   integration, finite specifications, Wilson actions, reflection boxes,
   reflection-positive-state interfaces, and the constructed
   thermodynamic-limit state.
2. This repository contains conjugation-span representation theory, endpoint
   fields, one-link positivity, measure-parametric propagation, the
   conditional perimeter theorem, and the thin application to the upstream
   thermodynamic-limit interface.
3. The concrete strong-coupling corollary also lives downstream. This avoids
   any reverse import from the upstream package and keeps the package graph
   acyclic.
4. The neutral gluelump critical path does not import `YangMills.Polymer`, the
   cluster expansion, `latticeStrongCouplingRadius`, or
   `centeredInfiniteVolumeMeasure`.
5. Mathematically neutral reflection APIs live upstream and are imported, not
   copied. Historical declarations still located below upstream
   `StrongCoupling` are consumed only in the named downstream adapter layer.
6. Endpoint and propagation core modules do not import strong-coupling or
   polymer implementation modules.
7. A regression computes the transitive import closure of the neutral roots
   and rejects any `StrongCoupling` or `Polymer` dependency.

The standalone module paths use `GluelumpPerimeterLaw.*`, while declaration
names remain `YangMills.Gluelump.*`. This avoids overlapping Lake's upstream
`YangMills` module ownership without changing public theorem names.

## Ultra implementation estimate

These estimates mean active Codex Ultra implementation and verification time
with uninterrupted tool access and the current repository available. They
include ordinary debugging and repeated narrow builds, but they are not a
calendar guarantee.

| Task | Expected Ultra time |
|---|---:|
| 1. One-link limit bridge | 5--9 hours |
| 2. Neutral limit/RP interface and inheritance | 14--26 hours |
| 3. Direct all-physical-length line propagation | 15--29 hours |
| 4. Direct bends, squares, and rectangle certificate | 14--26 hours |
| 5. Arbitrary geometry and headline assembly | 6--12 hours |
| 6. Independence audit and final verification | 6--12 hours |
| **Total** | **60--114 active Ultra hours** |

The realistic planning value is about **75--90 active Ultra hours**, while
**115 hours** is the current conservative budget. This corresponds to about
**7--12 serial working days**, or approximately **5--9 elapsed working days**
if independent subtasks are safely parallelized. The largest uncertainties
are Tasks 2--4: finite-box symmetry adapters, parity-dependent path casts, and
support bookkeeping. A failure to reuse the existing mixed-reflection
machinery cleanly could increase the total by a factor of roughly 1.5.

The post-theorem physical repository split in Task 7 was not included in this
historical estimate.

**Completion note (2026-08-25).**  Tasks 1--5 were completed in the same
parallel implementation run, substantially faster than this deliberately
conservative pre-implementation estimate.  The table is retained as the
historical planning estimate rather than rewritten after the fact.

## 1. Pass the direct one-link lower bound to the free-boundary limit

**Status:** Complete (2026-08-25). The uniform finite-volume positivity
theorem is now passed to every completed-free-boundary thermodynamic limit,
including literal reality and every lattice translate.

**Purpose.** Produce one tensor degree, one nonzero intertwiner, and one
positive constant before quantifying over the limiting measure. The required
quantifier order is schematically

```lean
exists m, exists T, T != 0 /\
  exists q, 0 < q /\
    forall mu,
      IsTranslationInvariantFreeBoundaryLimit
        sigma.wilsonPotential beta mu ->
      q <= Complex.re (localExpectation mu oneLinkObservable) /\
      (localExpectation mu oneLinkObservable).im = 0
```

This order ensures that the final perimeter rate cannot depend on `mu`.

**Implementation.**

1. Prove that
   `linkSymmetricSpecification G d N (Geometry.armAxis hd)` is eventually
   `ConjSpanOneLinkAdmissible` for the fixed comb endpoint.
2. Use the existing exact theorems for link symmetry and plaquette closure.
3. Prove eventual collar containment in the positive half-box.
4. Package `transverseLoop_support_has_linkCrossPlaquette_of_box` into the
   required crossing-plaquette visibility field for every comb-collar edge.
5. Obtain dynamic support from
   `support_subset_linkSymmetricSpecification_eventually`.
6. Apply `centerNeutral_exists_uniform_conjSpanOneLink_lowerBound` once, so
   `m`, `T`, and `q` remain independent of volume and of the limiting
   probability.
7. Rewrite the finite Gibbs integral as the `localExpectation` occurring in
   the completed-box sequence.
8. Pass `q <= re E_N[O]` through `hmu.localLimit` using continuity of
   `Complex.re` and closedness of `[q, infinity)`.
9. Pass the already-proved zero-imaginary-part identity through the same
   limit.
10. Add a translation corollary for cuts based at arbitrary sites; keep
    coordinate reorientation for Task 5.

**Suggested module.**
`GluelumpPerimeterLaw/OneLink/FreeBoundaryLimitLowerBound.lean`, with any
strong-coupling-specific witness kept in an adapter module instead.

**Risk.** Low. The main risk is normalization/rewrite friction between the
finite Gibbs integral and `localExpectation`, not a mathematical gap.

**Definition of done.** A focused, axiom-clean theorem states strict real
one-link positivity uniformly for every measure satisfying the limit
hypothesis. A regression checks its axiom footprint and its narrow build.

## 2. Introduce the neutral state interface and inherit reflection positivity

**Status:** Complete (2026-08-25). The neutral measure certificate and the
arbitrary completed-free-boundary-limit adapter are proved and axiom-audited.
The limit and eventual crossing-certificate declarations still physically
reside below `StrongCoupling`; moving those declarations without changing
their mathematics remains extraction hygiene rather than a theorem gap.

**Purpose.** Give the propagation engine only the properties of the measure
that it uses, without mentioning cluster expansions or a strong-coupling
radius.

**Implementation.**

1. Audit and separate generic reflection-family definitions from the
   centered strong-coupling wrappers in `SiteReflectionFamily`,
   `DiagonalFamily`, `AntiDiagonalFamily`, `ReflectionEngine`, and
   `ReflectedLine`.
2. Define a neutral measure-level certificate containing translation
   invariance; site-, link-, diagonal-, and anti-diagonal reflection
   positivity; their finite-family Cauchy--Schwarz forms; and the reality
   statements needed downstream.
3. Relocate or re-export the definition of the completed-free-boundary limit
   through a neutral `Gauge`/gluelump interface. Leave only the theorem that
   the cluster state satisfies it under `StrongCoupling`.
4. Prove the finite geometric fact that a completed link box elongated in an
   axis transverse to a site or diagonal cut has the required reflection
   symmetry. In `d >= 3`, choose the third coordinate for diagonal and
   anti-diagonal cuts.
5. For link reflection, reuse the completed box in the normal direction and
   the existing crossing-family gauge-fixed RP/CS theorem.
6. Pass all finite inequalities and zero-imaginary-part identities through
   `hmu.localLimit` using generic closed-under-limit lemmas.
7. Derive anti-diagonal RP either directly from the transverse exhaustion or
   through the proved coordinate-flip conjugacy, whichever gives the smaller
   neutral API.
8. Provide a theorem from the completed-free-boundary limit hypothesis to the
   neutral reflection-positive-state certificate.
9. Retain the existing strong-coupling theorem solely as a witness-producing
   adapter and regression example.

**Suggested modules.**

- `YangMills/Gauge/ReflectionPositiveState.lean`;
- `YangMills/Gauge/CompletedReflectionBoxes.lean`;
- `GluelumpPerimeterLaw/Interface/ThermodynamicLimit.lean`;
- `YangMills/StrongCoupling/GluelumpLimitAdapter.lean`.

The final locations may differ after the required source audit, but the
dependency direction must not.

**Risk.** Medium-high Lean geometry risk. The mathematical limit argument is
standard; the uncertain part is proving all required symmetries for the
completed boxes without duplicating centered-box infrastructure.

**Definition of done.** Propagation can consume an arbitrary certified
probability measure. The neutral certificate and generic propagation modules
have no `StrongCoupling` or `Polymer` imports, while the existing
strong-coupling state is proved to implement the interface.

## 3. Build the direct all-physical-length gluelump line family

**Status:** Complete (2026-08-25). The direct odd/even geometry is indexed by
physical bond length, its length-one member is exactly the direct one-link
seed, and the neutral measure layer proves reality, nonnegativity, adjacent
log-convexity, and the all-length power lower bound.  The completed-free-
boundary adapter combines Tasks 1 and 2 to choose the tensor degree,
nonzero screening intertwiner, and positive rate before quantifying over the
limiting measure.

**Purpose.** Construct a sequence `line : Nat -> LocalObservable d G` in
which `line 1` is literally the direct conjugation-span one-bond observable.
The older `oddStraightObservable` has physical length `2*l+1`; its index zero
is one bond and its index one is three bonds, so it cannot directly consume
Task 1.

**Implementation.**

1. Define the canonical direct endpoint at each physical line endpoint by
   translating `conjSpanPhi`; do not route through the legacy axial endpoint.
2. Define zero-length, even-length, and odd-length straight screened
   observables, or one unified physical-length family with parity lemmas.
3. Prove `line 1` is pointwise equal, up to the fixed harmless orientation
   convention, to `conjSpanReflectedOneLinkObservable`.
4. Prove the zero-length expectation is nonnegative and at most one, and prove
   the uniform upper bounds required by propagation from
   `conjSpanPhi_l2Norm_le_one`.
5. For odd physical lengths, construct the link-reflection Gram-family
   norm-square and adjacent mixed Cauchy--Schwarz certificates.
6. For even physical lengths, construct the corresponding site-reflection
   family certificates.
7. Prove the pointwise translation identities that identify each mixed
   pairing with the adjacent member of the physical-length family.
8. Use Task 2's state certificate to prove reality, nonnegativity, and
   adjacent log convexity

   ```text
   lineExpectation (n + 1)^2
     <= lineExpectation n * lineExpectation (n + 2).
   ```

9. Starting from the positive `line 1` seed, use
   `positive_of_reflectionLogConvex_of_pos` to obtain positivity at every
   length and prove the required power lower bound.
10. Keep all endpoint and path identities measure-parametric; only the final
    expectation lemmas should consume the state certificate.

**Implemented modules.**

- `GluelumpPerimeterLaw/Propagation/ConjSpanPhysicalStraight.lean` contains the
  measure-independent physical geometry and pointwise identities;
- `ConjSpanPhysicalStraightExpectation.lean` contains the neutral
  reflection-propagation theorem;
- `ConjSpanPhysicalStraightCrossing.lean` and
  `ConjSpanPhysicalStraightLimit.lean` are the one-way completed-box and
  strong-coupling-limit adapters.

The geometry and expectation import closure contains neither `StrongCoupling`
nor `Polymer`.

**Risk.** High Lean-integration risk. This is the most likely source of
parity, endpoint-cast, and translated-path proof friction. The underlying
site/link reflection argument is mathematically standard.

**Definition of done.** There is a direct-field physical-length sequence with
`line 1` definitionally or theorem-wise equal to Task 1's seed, and one-link
positivity yields a uniform power lower bound for every positive straight
length.

## 4. Port the bend, close, and rectangle propagation to the direct field

**Status:** Complete (2026-08-25).  The direct conjugation-span endpoint now
has collar-aware diagonal bending and anti-diagonal closing theorems, and the
result is packaged as a cofinal rectangle certificate.  No unsupported
short-length diagonal claim is used.

**Purpose.** Convert the long straight-line lower bound into square and then
arbitrary-rectangle Wilson-loop lower bounds for the neutral state.

**Implementation.**

1. Refactor `MeasureReflectionPropagationCertificate` or add a
   collar-aware/cofinal variant. Its current field
   `diagonalBend : forall l, ...` is stronger than the direct comb geometry,
   which naturally fits only positive or sufficiently long lengths.
2. Prefer the already-proved cofinal-square arithmetic over adding artificial
   short-line support hypotheses. Record the exact collar threshold as a
   fixed number depending only on the screening endpoint.
3. Define the direct conjugation-span bent-line family using translated and
   diagonal-pulled-back copies of `conjSpanPhi`.
4. Prove the direct endpoint and path supports lie in the required diagonal
   positive half for every length beyond the collar threshold.
5. Instantiate the generic diagonal family Cauchy--Schwarz theorem to prove
   the first bend inequality.
6. Instantiate the matrix-family anti-diagonal closing theorem. Retain the
   representation index through the reflection step so the exact denominator
   is `dim rho`.
7. Identify the reflected closure pointwise with the canonical Wilson square.
8. Port rectangle nonnegativity, zero-side upper bounds, row log convexity,
   and transpose symmetry to the neutral state using Task 2.
9. Prove the cofinal odd-square lower bound and then the arbitrary rectangle
   power lower bound.
10. Package the results as a concrete
    `MeasureReflectionPropagationCertificate`, or its collar-aware successor,
    for the direct field.

**Implemented modules.**

- `DiagonalBendingCore.lean`, `AntiDiagonalClosingCore.lean`, and
  `CornerReflectionState.lean` contain the neutral reflection-family core;
- `ConjSpanCornerGeometry.lean` and `ConjSpanCornerEndpoints.lean` contain the
  direct affine paths, endpoints, exact reflection identities, and support
  certificates;
- `ConjSpanCornerExpectation.lean` proves
  `line(length)^2 <= bent(length)` once the fixed comb collar fits, proves
  `bent(length)^2 / dim(rho) <= square(length)`, identifies the square with
  the canonical Wilson rectangle, and constructs
  `conjSpanCofinalRectangleReflectionCertificate`;
- `CofinalRectangleCertificate.lean` replaces the over-strong all-length bend
  field by odd, cofinal bend/close hypotheses and performs the existing
  cofinal-square-to-all-rectangle arithmetic;
- `RectangleReflectionCore.lean`, `RectangleGeometryCore.lean`, and
  `CanonicalRectangleExpectation.lean` supply the neutral rectangle reality,
  nonnegativity, upper bound, row log-convexity, and transpose package.

**Risk.** Medium-high. Most algebra is reusable, but support placement and the
current over-strong all-length bend interface may require careful API changes.

**Definition of done.** A theorem takes Task 3's positive one-link-powered
straight sequence and Task 2's state certificate and returns the power-form
lower bound for every positive canonical rectangle.

## 5. Transport to arbitrary geometry and prove the headline theorem

**Status:** Complete (2026-08-25).  The neutral positive-one-link theorem and
the completed-free-boundary application theorem are proved.  The latter has
exactly the public quantifier order: the screening data, power base, and
positive exponential rate are fixed before the limiting measure and all
rectangle geometry.

**Purpose.** Match the canonical propagated rectangle exactly to
`InfiniteVolume.rectangleWilsonObservable` for every basepoint and pair of
distinct coordinate axes, prove literal reality, and choose the rate with the
correct dependencies.

**Implementation.**

1. Use translation invariance to move the canonical rectangle to an arbitrary
   basepoint.
2. Derive coordinate-swap/permutation invariance from the isotropic completed
   box sequences, or parameterize the canonical construction by coordinate
   axes if that produces a cleaner neutral interface.
3. Transport the arm/transverse-axis theorem to every `a != b` and prove the
   resulting path is the target `Path.rectangleBoundary x0 a b R T`, up to
   cyclic reversal identities already valid for normalized characters.
4. Pass the reflection reality statement through the same transport and prove

   ```text
   complexRectangleWilsonExpectation mu rho x0 a b R T =
     (rectangleWilsonExpectation mu rho x0 a b R T : Complex).
   ```

5. Shrink the seed if necessary, for example by replacing `q` with
   `min q (1/2)`, so the power base is strictly between zero and one.
6. Convert the power bound to `Real.exp (-rate * 2 * (R + T))` and choose
   `rate > 0` before quantifying over `mu`, `x0`, `a`, `b`, `R`, and `T`.
7. Prove the declaration with type
   `CenterNeutralInfiniteVolumePerimeterLaw sigma rho`.
8. Add the strong-coupling corollary by applying the optional adapter witness;
   keep that corollary outside the neutral theorem's dependency chain.

**Risk.** Medium. The rate arithmetic is short; coordinate-isometry transport
and exact path equality are the likely Lean bottlenecks.

**Definition of done.** The exported main theorem has exactly the human-facing
quantifier order and conclusion, contains no real-part workaround, and its
rate depends only on `d`, `sigma`, `rho`, and `beta`.

**Implemented modules and theorem boundary.**

- `CanonicalRectangleTransport.lean` transports the canonical expectation to
  every basepoint and every ordered pair of distinct axes;
- `AxisTransport.lean` packages the finite swap generation needed for
  arbitrary coordinate planes;
- `CanonicalRectanglePerimeter.lean` transports literal reality and the power
  or exponential bound together;
- `Perimeter.lean`, `CanonicalCofinalRectangle.lean`, and
  `CanonicalCofinalPerimeterLaw.lean` convert the positive power base into an
  explicitly positive exponential rate;
- `ConjSpanPerimeterLaw.lean` proves the standalone, neutral theorem
  `conjSpanPerimeterLaw_of_positiveOneLink` from a positive direct one-bond
  seed and abstract reflection/crossing interfaces.  Its transitive closure
  contains neither `StrongCoupling` nor `Polymer`;
- `CanonicalRectangleExpectationLimit.lean` is the one-way completed-box
  adapter for rectangle crossing and coordinate-swap data;
- `InfiniteVolumePerimeterLaw.lean` proves the public theorem
  `centerNeutralInfiniteVolumePerimeterLaw`, of type
  `CenterNeutralInfiniteVolumePerimeterLaw sigma rho`;
- `StrongCouplingPerimeterLaw.lean` gives the concrete corollary
  `centeredInfiniteVolume_centerNeutralPerimeterLaw` for the existing
  cluster-constructed centered Wilson probability throughout the positive
  strong-coupling interval, so callers need not supply an abstract measure or
  limit witness.

The public theorem shrinks the uniform one-link constant to
`min q (1/2)`, uses the fixed cofinal collar base, and applies
`powerToExponentialRate`.  It also proves the complex Wilson expectation is
literally the coercion of its real coordinate before stating the lower bound;
the lower bound itself therefore contains no `Complex.re` workaround.

## 6. Independence audit, regressions, and final verification

**Status:** Complete (2026-08-25).  The neutral import boundary, theorem axiom
footprints, placeholder scan, strict elaboration checks, focused targets,
public aggregate, default build, and comprehensive regression all pass on the
integrated tree.

**Implementation.**

1. Split mixed generic/strong-coupling files where necessary and remove
   unused strong-coupling imports before extraction.
2. Keep neutral incidence and reflection-box APIs in the upstream `Lattice`
   or `Gauge` layers while preserving provenance and avoiding copied forks.
3. Add focused tests for each task, including exact theorem-type checks and
   `#print axioms` for the new public declarations.
4. Add an import regression for the standalone neutral gluelump core.
5. Scan the critical path for proof placeholders, custom axioms, and unsafe
   declarations.
6. Run narrow builds after each coherent milestone and the complete
   `lake build` at the end.
7. Run `git diff --check`, inspect the dirty worktree carefully, and update
   `STATUS.md` after every completed task.
8. Update this ledger rather than deleting completed tasks.

**Definition of done.** The main theorem and its direct dependencies build
without placeholders; axiom reports contain only accepted Lean foundations;
the full build succeeds; and the import audit demonstrates that the neutral
gluelump core is independent of polymer and strong-coupling implementation
modules.

**Verification record.**

- `GluelumpNeutralCriticalPath.lean` computes the transitive import closure of
  the neutral roots and rejects every `YangMills.StrongCoupling` or
  `YangMills.Polymer` dependency.  It includes
  `ConjSpanPerimeterLaw` as the neutral headline root.
- The separate public regressions cover
  `conjSpanPerimeterLaw_of_positiveOneLink`,
  `centerNeutralInfiniteVolumePerimeterLaw`, and
  `centeredInfiniteVolume_centerNeutralPerimeterLaw`.
- All three headline declarations, together with the representative line,
  corner, rectangle, transport, and rate theorems, report only `propext`,
  `Classical.choice`, and `Quot.sound` under `#print axioms`.
- The critical source scan contains no `sorry`, `admit`, `sorryAx`, custom
  `axiom`, or `unsafe` declaration, and `git diff --check` is clean.
- Both headline sources pass with `-DautoImplicit=false`.
- `lake build GluelumpPerimeterLaw` succeeds with 8,678 jobs against the
  prepared upstream prerequisite branch; and
- `lake build GluelumpPerimeterLawTests` succeeds with 8,687 jobs and checks
  all nine shipped regression modules.

The definitions of the completed-free-boundary limit and a few neutral
finite-box helpers still occupy historical directories below upstream
`StrongCoupling`. They are used only by named one-way adapters and are not in
the audited neutral theorem closure.

## 7. Post-theorem extraction into a separate repository

**Status:** Implementation complete locally (2026-08-25); remote publication
awaits the upstream prerequisite merge and refreshed GitHub authentication.

**Completed work.**

1. The exact theorem closure was recomputed from the neutral and public
   headline roots. The standalone production tree contains 110 modules:
   19 endpoint, 2 Lie, 32 one-link, 37 propagation, 17 representation-theory,
   and 3 top-level headline modules.
2. Twenty-three obsolete or noncritical torus, axial, and old propagation
   modules were excluded. No shipped module imports them.
3. Module imports were renamed mechanically from `YangMills.Gluelump.*` to
   `GluelumpPerimeterLaw.*`; declaration namespaces were deliberately left
   unchanged.
4. The 28 generic lattice/gauge/strong-coupling prerequisites were separated
   into an upstream-only commit. They contain no import back into this
   package.
5. The standalone package has one direct Lake requirement, the Git URL of
   `strong-coupling-lattice-yang-mills` with `rev = "main"`.
6. Nine focused regression modules, an aggregate test root, a neutral import
   audit, provenance notice, and scheduled compatibility CI were added.
7. Every one of the 110 production modules is reachable from the public
   roots; all 267 production import statements resolve; no duplicate module
   ownership or reverse package edge remains.
8. Production and regression builds pass against the locally staged upstream
   prerequisite commit, and the headline axiom audits contain only standard
   Lean foundations.

**Publication gate.** The generic prerequisite commit must first be merged
into the upstream `main` branch. The downstream Lake manifest is then
regenerated from that remote branch, followed by a fresh-clone build and the
initial push of this repository. This ordering ensures the published package
really references upstream `main`, never a temporary path or circular
adapter.
