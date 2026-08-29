# Central-neutral-perimeter-law-lower-bound

This Lean 4 project proves a center-neutral gluelump perimeter-law lower bound
for lattice Yang--Mills theory.  It is the standalone downstream companion to
[`strong-coupling-lattice-yang-mills`](https://github.com/rn9801/strong-coupling-lattice-yang-mills).

The package has exactly one direct Lake dependency: the unchanged `main`
branch of that repository. Mathlib and the established lattice, gauge,
Wilson, and strong-coupling foundations arrive transitively through it.

The 28 additive prerequisite modules developed with the gluelump proof live
in this repository under `GluelumpPerimeterLaw.Upstream.*`: 19 extend existing
upstream modules, and nine supply new reflection/limit modules. Their module
paths are downstream-owned, while their declarations intentionally remain in
the existing `YangMills.*` namespaces. No corresponding commit or branch is
required in the Strong-Coupling repository.

## The results in ordinary mathematical language

### Setup and relevant definitions

We work on the infinite cubic lattice in dimension `d`. A gauge
configuration assigns an element of a compact, Hausdorff, second-countable
topological group `G` to each positively oriented edge; traversing the edge
backwards uses the group inverse. Expectations are taken with respect to
Borel probability measures on this configuration space. All three results
assume a normalized Haar probability on `G`; the first two additionally
assume that it gives positive mass to every nonempty open set.

The action representation `sigma` and Wilson representation `rho` are
positive-dimensional continuous unitary matrix representations of `G`.
The action representation determines the real Wilson plaquette potential

```text
Phi_sigma(g) = Re((1 / dim sigma) Tr(sigma(g))),
```

while the Wilson representation determines the loop observable. Faithfulness
of `sigma` means that its homomorphism is injective. Center neutrality of
`rho` means that every element of the center of `G` acts as the identity.
Center neutrality neither makes `rho` trivial nor requires it to be
irreducible.

For a closed lattice path `C` and a configuration `A`, let

```text
W_rho(C; A) = (1 / dim rho) Tr(rho(Hol_A(C)))
```

be the normalized Wilson observable. If `C` is the boundary of a coordinate
rectangle based at `x0`, with distinct coordinate directions `a` and `b` and
positive integer side lengths `R` and `T`, then it travels `R` bonds in
direction `+a`, `T` bonds in direction `+b`, and returns along the two
negative directions. Its perimeter is `2(R + T)`. Its expectation in a
probability measure `mu` is the generally complex number

```text
W_{mu,rho}(C) = integral W_rho(C; A) dmu(A).
```

The real expectation used in the lower bound is the real part of this
integral. Each headline conclusion first proves that the complex integral is
equal to that real number, and therefore really is real, before comparing it
with a real exponential.

A local observable is a continuous complex-valued function depending on only
finitely many edge variables. A translation-invariant completed
free-boundary limit at coupling `beta` is a probability measure `mu` with two
properties:

- For every distinguished coordinate direction and every local observable,
  expectations along the **entire** corresponding sequence of completed
  link-symmetric free-boundary Gibbs boxes converge to the expectation under
  `mu`. At scale `N`, the box is `[-N,N+1]` in the distinguished direction
  and `[-N,N]` transversely, and configurations are extended by the identity
  outside the completed finite specification. The same `mu` must work for
  every distinguished direction.
- Every integer lattice translation preserves `mu`.

This is local-observable convergence, not total-variation convergence. It is
not a subsequence definition, and it does not itself assert existence or
uniqueness of the limiting probability.

A perimeter-law lower bound with rate `c > 0` means that every such rectangle
satisfies

```text
W_{mu,rho}(C) >= exp(-c * perimeter(C)).
```

When the rate is quantified before a measure or rectangle datum, the same
rate works uniformly for every later choice.

For the model-neutral theorem, the conjugation span of `sigma` is the complex
linear span of the matrices `sigma(g)`, with `G` acting by matrix
conjugation. A screening intertwiner is a complex-linear, equivariant map
from some tensor power of this conjugation representation to `rho`. The
project feeds holonomies of a fixed finite comb of local loops through this
map, then scales the result by a configuration-independent factor obtained
from a uniform norm bound, to obtain a bounded local `rho`-valued endpoint
field with the required gauge covariance.

The direct one-link gluelump observable places this endpoint on one side of a
distinguished bond, its literal link-reflected copy on the other side,
parallel-transports across the bond, and takes the Hermitian endpoint
contraction. Its one-link expectation means the real part of the resulting
integral.

A reflection-positive state is translation invariant and invariant under
reflecting any coordinate through zero. At every affine site, link,
diagonal, and antidiagonal cut it supplies positivity and
Cauchy--Schwarz; diagonal and antidiagonal pairings are also Hermitian. The
ordinary link fields apply only to gauge-invariant positive-half observables,
which is why the model-neutral theorem uses separate crossing-link
interfaces. One supplies the corresponding reality, positivity, and mixed
Cauchy--Schwarz estimates for the whole odd screened-line family, and the
other supplies them for the half-integer rectangle cuts. Rectangle axis-swap
invariance says that transposing coordinate labels leaves the origin-based
rectangular Wilson integrals unchanged.

Finally, the centered strong-coupling probability is the infinite-volume
Wilson probability constructed by the cluster expansion with constant
identity exterior data. The certified lattice strong-coupling radius is the
positive convergence radius supplied by that construction.

### Headline theorem 1: completed free-boundary limits

Fix a dimension of at least three, a faithful continuous unitary action
representation `sigma`, and a center-neutral continuous unitary Wilson
representation `rho`. For every positive real coupling `beta`, there is a
positive rate `c` such that the following holds: for every
translation-invariant completed free-boundary limit `mu` of the
`sigma`-Wilson action at `beta`, and for every coordinate rectangle with
arbitrary basepoint, distinct coordinate axes, and positive side lengths,
the normalized `rho`-Wilson expectation is real and satisfies

```text
W_{mu,rho}(C) >= exp(-c * 2(R + T)).
```

The quantifier order is `beta`, then `c`, then `mu`, then the rectangle data.
Thus, within the fixed ambient group, `c` may depend on `d`, `sigma`, `rho`,
and `beta`, but it is independent of the limiting measure, rectangle
location and orientation, and both side lengths. This theorem has no
small-coupling restriction. Outside a regime where a suitable limit has been
constructed, it is conditional on supplying one. No irreducibility
hypothesis is imposed on `rho`.

### Headline theorem 2: the concrete strong-coupling state

Under the same dimension, faithfulness, and center-neutrality assumptions,
fix any positive real coupling `beta`. There is a positive rate `c` such that,
whenever the absolute value of `beta` is smaller than the certified lattice
strong-coupling radius, the cluster-constructed centered infinite-volume
Wilson probability has real normalized `rho`-Wilson rectangle expectations
and satisfies

```text
W_{mu_beta,rho}(C) >= exp(-c * 2(R + T))
```

for every basepoint, every ordered pair of distinct coordinate axes, and all
positive side lengths. The rate is chosen after `beta` but before the
certificate that `beta` lies inside the radius and before all rectangle data;
it therefore depends only on `d`, `sigma`, `rho`, and `beta`. Unlike the
first result, this theorem supplies the limiting probability rather than
assuming it: the strong-coupling infrastructure proves that this centered
probability is a translation-invariant completed free-boundary limit.

### Headline theorem 3: model-neutral propagation from one link

Fix a probability measure `mu` on lattice gauge configurations in dimension
at least three, continuous unitary representations `sigma` and `rho`, a
tensor degree, and a screening intertwiner from that tensor power of the
conjugation span of `sigma` to `rho`. Assume that `mu` supplies the full
reflection-positive-state interface, the crossing-link positivity and
Cauchy--Schwarz interface for the whole odd screened-line family, the
corresponding half-integer-cut interface for canonical rectangles, and
invariance of rectangle expectations under coordinate-axis swaps. Finally,
assume that some `q` with `0 < q <= 1` is no larger than the direct one-link
gluelump expectation.

Then there is a positive rate `c` for which every coordinate rectangle with
positive integer side lengths, at every basepoint and in every pair of
distinct coordinate directions, has a real normalized `rho`-Wilson
expectation bounded below by

```text
exp(-c * perimeter).
```

Here `mu`, all reflection and screening data, and `q` are fixed before `c` is
chosen, so the conclusion is uniform over the rectangle data but not over
different states. This theorem assumes neither faithfulness of `sigma` nor
center neutrality or irreducibility of `rho`; it also does not explicitly
assume that the intertwiner is nonzero, because the positive seed supplies
the operational nontriviality. It contains no coupling, Gibbs-measure,
finite-volume, thermodynamic-limit, cluster-expansion, or strong-coupling-
radius hypothesis. In the proof of the first result, the center-neutral
screening construction supplies the intertwiner, while the completed-limit
adapters supply the positivity and limit inputs. That proof uses the
fixed-rate form of the same propagation machinery to retain uniformity over
`mu`. The second result then instantiates the first with the
cluster-constructed state.

## Exact Lean statements and definitions

All three results below are exported by the package root:

```lean
import GluelumpPerimeterLaw

#check YangMills.Gluelump.InfiniteVolume.centerNeutralInfiniteVolumePerimeterLaw
#check YangMills.Gluelump.InfiniteVolume.centeredInfiniteVolume_centerNeutralPerimeterLaw
#check YangMills.Gluelump.Propagation.conjSpanPerimeterLaw_of_positiveOneLink
```

### Main theorem for completed free-boundary limits

[Statement](GluelumpPerimeterLaw/InfiniteVolumePerimeterLawStatement.lean) ·
[Proof](GluelumpPerimeterLaw/InfiniteVolumePerimeterLaw.lean)

The main proof theorem is:

```lean
theorem centerNeutralInfiniteVolumePerimeterLaw
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r) :
    CenterNeutralInfiniteVolumePerimeterLaw (d := d) sigma rho
```

Ignoring only the ambient compact-group and Haar typeclass binder list, the
proposition in its conclusion is defined by the following Lean code:

```lean
def CenterNeutralInfiniteVolumePerimeterLaw
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r) : Prop :=
  3 ≤ d →
  Function.Injective sigma.ρ →
  CenterNeutral (asRepresentation rho) →
  ∀ beta : ℝ, 0 < beta →
    ∃ rate : ℝ, 0 < rate ∧
      ∀ mu : ProbabilityMeasure (Configuration d G),
        IsTranslationInvariantFreeBoundaryLimit
            sigma.wilsonPotential beta mu →
          ∀ (x0 : Site d) (a b : Fin d) (R T : ℕ),
            a ≠ b → 0 < R → 0 < T →
              complexRectangleWilsonExpectation mu rho x0 a b R T =
                  (rectangleWilsonExpectation mu rho x0 a b R T : ℂ) ∧
                Real.exp (-rate * (2 * (R + T) : ℕ)) ≤
                  rectangleWilsonExpectation mu rho x0 a b R T
```

#### Key definitions in the main statement

##### Center neutrality

[Source](GluelumpPerimeterLaw/RepresentationTheory/CenterNeutral.lean)

```lean
/-- A representation is center-neutral when every central group element acts
as the identity. -/
def CenterNeutral (rho : Representation k G V) : Prop :=
  ∀ z : G, z ∈ Subgroup.center G → rho z = LinearMap.id
```

Thus `CenterNeutral rho` says that every element of the center of `G` acts
as the identity on every vector. It does **not** say that `rho` is the trivial
representation: noncentral elements may act nontrivially. The definition
itself does not require irreducibility, and none of the three headline
theorems assumes that `rho` is irreducible.

##### Translation-invariant completed free-boundary limit

[Source](GluelumpPerimeterLaw/Upstream/StrongCoupling/FreeBoundaryInfiniteVolume.lean)

```lean
structure IsTranslationInvariantFreeBoundaryLimit
    (Φ : RealPlaquettePotential G) (β : ℝ)
    (μ : ProbabilityMeasure (Configuration d G)) : Prop where
  localLimit : ∀ (τ : Fin d) (F : LocalObservable d G),
    Tendsto (fun n ↦ localExpectation
      (linkSymmetricGibbsSequence Φ β τ n) F) atTop
      (nhds (localExpectation μ F))
  translationInvariant : ∀ v : Site d,
    Measure.map (LocalObservable.translateConfiguration (G := G) v)
        (μ : Measure (Configuration d G)) =
      (μ : Measure (Configuration d G))
```

Here:

- `LocalObservable d G` is a continuous complex observable depending on only
  finitely many lattice edges.
- `localExpectation μ F` is the integral `∫ A, F A ∂μ`.
- `linkSymmetricGibbsSequence Φ β τ n` is the completed free-boundary
  Gibbs probability adapted to reflection in the link plane
  `x_τ = 1/2`. Its underlying box is `[-n,n+1]` in direction `τ` and
  `[-n,n]` in every transverse direction; configurations are extended by the
  identity outside the completed finite specification.
- `localLimit` requires the **entire** sequence, for every orientation `τ`
  and every local observable `F`, to converge to expectations in the same
  probability `μ`. The current definition does not use subsequences.
- `translationInvariant` says that pushing `μ` forward by any integer
  lattice translation leaves it unchanged.

This is convergence tested against every local continuous observable, not a
total-variation convergence assertion. The main theorem is conditional on a
supplied `μ` and a proof of this structure; the definition does not assert
globally that such a probability exists. The strong-coupling corollary below
supplies one.

##### Rectangle observable and expectation notation

[Source](GluelumpPerimeterLaw/InfiniteVolumePerimeterLawStatement.lean)

```lean
def rectangleWilsonObservable {d r : ℕ} {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (rho : ContinuousUnitaryRepData G r)
    (x0 : Site d) (a b : Fin d) (R T : ℕ) : LocalObservable d G :=
  rho.wilsonLoop (Path.rectangleBoundary x0 a b R T)

def complexRectangleWilsonExpectation {d r : ℕ} {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] [GaugeHaarProbability G]
    (mu : ProbabilityMeasure (Configuration d G))
    (rho : ContinuousUnitaryRepData G r)
    (x0 : Site d) (a b : Fin d) (R T : ℕ) : ℂ :=
  localExpectation mu (rectangleWilsonObservable rho x0 a b R T)

def rectangleWilsonExpectation {d r : ℕ} {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] [GaugeHaarProbability G]
    (mu : ProbabilityMeasure (Configuration d G))
    (rho : ContinuousUnitaryRepData G r)
    (x0 : Site d) (a b : Fin d) (R T : ℕ) : ℝ :=
  (complexRectangleWilsonExpectation mu rho x0 a b R T).re
```

Pointwise, `rectangleWilsonObservable` is the normalized character

```lean
(r : ℂ)⁻¹ * Matrix.trace
  (rho.ρ (holonomy A (Path.rectangleBoundary x0 a b R T)))
```

The boundary travels `R` bonds in direction `+a`, then `T` in direction
`+b`, followed by `R` in direction `-a` and `T` in direction `-b`; its
perimeter is `2 * (R + T)`. The definitions themselves allow coincident axes
and zero side lengths, while the theorem assumes distinct axes and positive
side lengths.

The complex expectation is not definitionally real;
`rectangleWilsonExpectation` is only its real part. The first conclusion of
the headline theorem proves that the complex expectation equals this real
number coerced back to `ℂ`, after which the lower bound is genuinely a bound
on the expectation itself.

Thus, in dimension at least three, a faithful action representation `sigma`
and a center-neutral Wilson representation `rho` give a uniform
perimeter-law lower bound at every positive coupling, conditional on the
stated thermodynamic limit.

For every basepoint, every ordered pair of distinct coordinate axes, and all
positive side lengths, the theorem proves both

- that the Wilson-loop expectation is real; and
- that it is at least `exp (-rate * perimeter)`.

The rate depends only on `d`, `sigma`, `rho`, and `beta`. Its quantifier comes
before `mu` and all rectangle data, so it is uniform over the limiting
probability, basepoint, axes, and side lengths. The theorem itself has no
small-coupling restriction; away from strong coupling it is conditional on
the existence of a probability satisfying the full-limit hypothesis.

### Concrete strong-coupling corollary

[Source](GluelumpPerimeterLaw/StrongCouplingPerimeterLaw.lean)

```lean
theorem centeredInfiniteVolume_centerNeutralPerimeterLaw
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (hd : 3 ≤ d)
    (hsigma : Function.Injective sigma.ρ)
    (hcenter : CenterNeutral (asRepresentation rho))
    (beta : ℝ) (hbetaPos : 0 < beta) :
    ∃ rate : ℝ, 0 < rate ∧
      ∀ hbeta : ‖(beta : ℂ)‖ <
          latticeStrongCouplingRadius d sigma.wilsonPotential.bound,
        ∀ (x₀ : Site d) (a b : Fin d) (R T : ℕ),
          a ≠ b → 0 < R → 0 < T →
            complexRectangleWilsonExpectation
                (centeredInfiniteVolumeProbability
                  (fun _ ↦ (1 : Configuration d G))
                  sigma.wilsonPotential beta hbeta)
                rho x₀ a b R T =
                (rectangleWilsonExpectation
                  (centeredInfiniteVolumeProbability
                    (fun _ ↦ (1 : Configuration d G))
                    sigma.wilsonPotential beta hbeta)
                  rho x₀ a b R T : ℂ) ∧
              Real.exp (-rate * (2 * (R + T) : ℕ)) ≤
                rectangleWilsonExpectation
                  (centeredInfiniteVolumeProbability
                    (fun _ ↦ (1 : Configuration d G))
                    sigma.wilsonPotential beta hbeta)
                  rho x₀ a b R T
```

The strong-coupling infrastructure proves that the cluster-constructed
centered Wilson probability satisfies the completed-box limit hypothesis.
This supplies an unconditional application of the main theorem whenever
`beta > 0` lies inside the cluster-expansion radius. The same rate is chosen
before the radius witness and before all rectangle data.

### Model-neutral propagation theorem

[Source](GluelumpPerimeterLaw/Propagation/ConjSpanPerimeterLaw.lean)

```lean
theorem conjSpanPerimeterLaw_of_positiveOneLink
    (mu : ProbabilityMeasure (Configuration d G))
    (hstate : ReflectionPositiveState mu)
    (hd : 3 ≤ d)
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (hlineLink : ConjSpanLinkReflectionData mu hd sigma rho T
      (0 : Site d) (conjSpanCornerZeroArm hd))
    (hrectangleLink : CanonicalRectangleLinkReflectionData mu rho
      (Geometry.armAxis_ne_transverseAxis₁ hd))
    (hswap : RectangleAxisSwapInvariant mu rho)
    {q : ℝ} (hq : 0 < q) (hqOne : q ≤ 1)
    (hqseed : q ≤ conjSpanPhysicalStraightExpectation
      mu hd sigma rho T (0 : Site d) (conjSpanCornerZeroArm hd) 1) :
    ∃ rate : ℝ, 0 < rate ∧
      ∀ (x₀ : Site d) (a b : Fin d) (R S : ℕ),
        a ≠ b → 0 < R → 0 < S →
          (∫ A, rho.wilsonLoop (Path.rectangleBoundary x₀ a b R S) A
              ∂(mu : Measure (Configuration d G))) =
              ((∫ A, rho.wilsonLoop
                (Path.rectangleBoundary x₀ a b R S) A
                  ∂(mu : Measure (Configuration d G))).re : ℂ) ∧
            Real.exp (-rate * ((2 * (R + S) : ℕ) : ℝ)) ≤
              (∫ A, rho.wilsonLoop (Path.rectangleBoundary x₀ a b R S) A
                ∂(mu : Measure (Configuration d G))).re
```

This is the reusable mathematical engine. A positive direct one-link
gluelump seed, a reflection-positive state, the two gauge-fixed crossing-link
interfaces, and coordinate-swap invariance imply the real exponential
rectangle bound. This theorem contains no finite-volume exhaustion, cluster
expansion, thermodynamic-limit assumption, or strong-coupling radius.

The project-specific interfaces in this theorem mean:

- [`ReflectionPositiveState`](GluelumpPerimeterLaw/Upstream/Gauge/ReflectionPositiveState.lean)
  bundles translation and coordinate-reflection invariance together with
  positivity and Cauchy--Schwarz for site, link, diagonal, and antidiagonal
  reflection pairings at every affine cut, plus Hermitian symmetry for the
  diagonal and antidiagonal pairings. Its ordinary link fields apply to
  gauge-invariant positive-half observables; crossing gauge-covariant
  gluelump endpoints require the separate link interfaces below.
- [`ConjSpanLinkReflectionData`](GluelumpPerimeterLaw/Propagation/ConjSpanPhysicalStraightExpectation.lean)
  supplies reality, nonnegativity, and mixed Cauchy--Schwarz for the odd,
  link-centered gluelump lines. In the completed-box construction these
  inequalities are obtained by crossing-link gauge fixing.
- [`CanonicalRectangleLinkReflectionData`](GluelumpPerimeterLaw/Propagation/CanonicalRectangleExpectation.lean)
  supplies the corresponding half-integer-cut positivity and
  Cauchy--Schwarz statements for balanced and mixed coordinate caps.
- [`RectangleAxisSwapInvariant`](GluelumpPerimeterLaw/Propagation/CanonicalRectangleExpectation.lean)
  says that transposing any two coordinate labels leaves every origin-based
  rectangular Wilson-loop integral unchanged.
- `conjSpanPhysicalStraightExpectation ... length` is the real expectation
  of the direct screened line with exactly `length` arm bonds. At length one
  it is exactly the reflected one-link seed whose positive lower bound is
  assumed in `hqseed`.

Together with the action data, nonnegative coupling, and geometric
assumptions, the completed-box limit hypothesis supplies all of these
interfaces in the main proof; they are explicit assumptions only in the
model-neutral propagation theorem.

### Screening construction

The screening map is constructed directly as
`(ConjSpan sigma)^⊗m → rho`. Accordingly, the normalized Higgs-like endpoint
is `rho`-valued and transforms by the ordinary Wilson representation action;
the active construction does not pass through the algebraic dual of `rho`.

## Proof integrity

All repository-owned Lean sources are free of `sorry`, `admit`, `sorryAx`,
project-defined `axiom` or `constant` declarations, and `unsafe`
declarations. The five `noncomputable opaque` definitions each have an
explicit `:= by` body which Lean kernel-checks; opacity controls reduction
and does not introduce an axiom or proof gap.

A compiled `Lean.collectAxioms` audit of every project declaration found no
nonstandard axiom dependency. In particular, the complete axiom footprint of
each of the three headline theorems is exactly

- `propext`;
- `Classical.choice`; and
- `Quot.sound`.

These are Lean's standard foundational principles, not axioms introduced by
this project. The regression suite records the headline footprints and
rejects nonstandard axioms on the neutral critical path; CI also rejects proof
placeholders, source-level `axiom` declarations, and unsafe declarations.

This does not mean that the mathematical statements have no hypotheses. The
compact-group, representation, dimension, coupling, positivity, and limit
hypotheses are explicit in the theorem signatures above. Some reusable
auxiliary theorems likewise take explicit data or proposition interfaces as
arguments. None is installed globally or hidden as an unproved internal
assumption. See [the mathematical assumptions](docs/MATHEMATICAL_ASSUMPTIONS.md)
for the complete accounting.

## Build

```bash
lake update
lake build
lake build GluelumpPerimeterLawTests
```

Import the public API with:

```lean
import GluelumpPerimeterLaw
```

Module paths use the `GluelumpPerimeterLaw.*` prefix so Lake can distinguish
this package from the upstream `YangMills` library.  Existing declaration
namespaces remain `YangMills.Gluelump.*`.

## Upstream compatibility overlay

`GluelumpPerimeterLaw/Upstream` is an additive compatibility overlay on the
current upstream `main`; it does not replace or modify files in the dependency
checkout. When upstream `main` eventually acquires one of these declarations,
the corresponding downstream extension must be removed (and its imports
retargeted) in the same compatibility update, otherwise Lean will correctly
report a duplicate declaration. Scheduled CI updates the dependency to the
latest `main` so that transition is detected immediately.

The GitHub repository is private for now.

See [the roadmap](docs/ROADMAP.md), [the mathematical assumptions](docs/MATHEMATICAL_ASSUMPTIONS.md),
and [the status ledger](STATUS.md).

## License and provenance

The project is released under Apache-2.0. The initial standalone source and
its 28 compatibility modules were extracted from the gluelump development in
`strong-coupling-lattice-yang-mills`; individual Lean files retain their
original copyright and contributor notices. See [NOTICE](NOTICE).
