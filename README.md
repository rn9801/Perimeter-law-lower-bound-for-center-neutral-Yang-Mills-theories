# Gluelump perimeter-law lower bound

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

## Headline theorems

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
  (asRepresentation rho).IsIrreducible →
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

Thus, in dimension at least three, a faithful action representation `sigma`
and an irreducible center-neutral Wilson representation `rho` give a uniform
perimeter-law lower bound at every positive coupling, conditional on the
stated thermodynamic limit. The current
`IsTranslationInvariantFreeBoundaryLimit` hypothesis requires full-sequence
convergence: for every coordinate orientation and every local observable,
the corresponding completed-box sequence converges to the same
translation-invariant probability `mu`.

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
    (hirreducible : (asRepresentation rho).IsIrreducible)
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

### Screening construction

The screening map is constructed directly as
`(ConjSpan sigma)^⊗m → rho`. Accordingly, the normalized Higgs-like endpoint
is `rho`-valued and transforms by the ordinary Wilson representation action;
the active construction does not pass through the algebraic dual of `rho`.

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
