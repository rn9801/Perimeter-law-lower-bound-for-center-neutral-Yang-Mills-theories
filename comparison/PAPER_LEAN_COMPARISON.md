# Paper and Lean correspondence

Updated 2026-11-17. This document describes the strengthened headline and its
proof path. It supersedes the earlier audit of the qualitative headline.
The manuscript is [main.tex](../paper/main.tex);
Lean's dependency remains the locked Strong-Coupling `main` revision
`bc7383d023f0c58a16312764a32422248aa42ebe`.

## The headline statement

The paper's Theorem `thm:Main-theorem` is exported as
`YangMills.Gluelump.InfiniteVolume.centerNeutralInfiniteVolumePerimeterLaw`
in [InfiniteVolumePerimeterLaw.lean](../lean/GluelumpPerimeterLaw/InfiniteVolumePerimeterLaw.lean).
Its proposition is
`CenterNeutralInfiniteVolumePerimeterLaw`, an abbreviation for
`CenterNeutralUniformCouplingPerimeterLaw` in
[InfiniteVolumePerimeterLawStatement.lean](../lean/GluelumpPerimeterLaw/InfiniteVolumePerimeterLawStatement.lean).

With `rho` denoting the paper's Wilson representation `tau`, its quantifiers
and conclusion are:

```text
d >= 3 -> sigma faithful -> rho center neutral ->
  exists C > 0,
    for every beta > 0,
      for every common translation-invariant paper free-boundary limit mu,
        for every basepoint, distinct coordinate axes, and R,T > 0,
          E_mu[W_rho(rectangle)] is real, and
          exp(-C * (1 + beta + |log beta|) * 2*(R+T))
            <= E_mu[W_rho(rectangle)].
```

Thus **one `C` is selected before `beta`, the measure, and the rectangle**.
There is no small-coupling or irreducibility hypothesis. The normalized
Wilson observable is the same `Tr(rho(Q_loop))/dim(rho)` in both sources.
Reality is explicit in Lean, so the inequality concerns the real Wilson
expectation itself.

The group is represented in Lean by a compact Hausdorff second-countable
topological group with its Borel structure and normalized Haar probability.
The paper's compact Lie group satisfies these hypotheses. The proof uses
these topological and representation-theoretic structures; it does not use
differentiation on the group. Positive representation dimensions are fields
of `ContinuousUnitaryRepData`. Positivity of Haar measure on nonempty open
sets is synthesized from the ambient hypotheses.

## Finite-volume law and the limit assumption

[FreeBoundaryBoxes.lean](../lean/GluelumpPerimeterLaw/Upstream/StrongCoupling/FreeBoundaryBoxes.lean)
defines `freeBoundarySpecification` with exactly the paper's finite variables
and interactions:

- Dynamic edges are the positive edges internal to the site box.
- An active plaquette has all four boundary edges internal to that box.
- Both ordered axis labels `(i,j)` and `(j,i)` are retained.

`mem_freeBoundaryActivePlaquettes_iff` proves that the incident-plaquette
prefilter imposes no additional restriction on contained plaquettes.
Identity exterior data only embed each finite law in the common infinite
configuration space; a fixed local observable is eventually supported
entirely on dynamic edges.

The upstream completed-box specification is still available, but the
headline's limit assumption and finite reflection certificates now use
**ordinary internal-edge free-boundary boxes directly**. No unproved
completed-box marginal identity or additional convergence hypothesis is
needed by this proof.

The internal potential is `Re Tr(sigma(g))/n`, where `n=dim(sigma)`.
Consequently the paper's coupling `beta` corresponds to internal coupling
`n*beta`. The two oriented plaquette labels already supply the paper's factor
of two per geometric plaquette; a further factor of two would be incorrect.
[PaperFreeBoundary.lean](../lean/GluelumpPerimeterLaw/Upstream/StrongCoupling/PaperFreeBoundary.lean)
exports:

- `paperFreeBoundaryGibbsSequence` at coupling `n*beta`;
- `paperFreeBoundary_exponent_eq_character_sum`, identifying the Boltzmann
  exponent with `beta * sum_p Re character_sigma(Q_p)` over oriented plaquettes;
- `IsTranslationInvariantPaperFreeBoundaryLimit`, the ordinary local-limit
  hypothesis at that coupling.

[FreeBoundaryInfiniteVolume.lean](../lean/GluelumpPerimeterLaw/Upstream/StrongCoupling/FreeBoundaryInfiniteVolume.lean)
requires convergence of every continuous local observable along each
elongation axis to the same translation-invariant probability. This is
Assumption `as:infinite-vol`, using the local-convergence explanation after
that assumption. Its `IsTranslationInvariantFreeBoundaryLimit.unique` lemma
proves uniqueness from these limits: local continuous observables determine
the measure. Uniqueness therefore needs no extra input in the headline.

Finite site, bond, diagonal, and anti-diagonal reflection inequalities pass
to this common limit in
[FreeBoundaryReflectionPositiveState.lean](../lean/GluelumpPerimeterLaw/Upstream/StrongCoupling/FreeBoundaryReflectionPositiveState.lean).
The finite bond argument uses gauge-fixed crossing families, allowing
covariant half-observables whose glued full observable is gauge invariant,
as in the paper's Remark `rem:RP-Wilson-observables`.

## Proof correspondence

| Paper step | Lean proof used by the headline | Correspondence |
| --- | --- | --- |
| Lemmas `lm:faithful` and `lm:Intertwiner-construct` | `centerNeutral_exists_conjSpanIntertwiner` in [CenterScreening.lean](../lean/GluelumpPerimeterLaw/RepresentationTheory/CenterScreening.lean), using [TensorGeneration.lean](../lean/GluelumpPerimeterLaw/RepresentationTheory/TensorGeneration.lean) | Pass to `G/Z(G)`, detect a nonzero matrix coefficient by Stone–Weierstrass, and Haar-average a rank-one map. The degree and nonzero screening map are fixed before the coupling. |
| Definitions `def:comb`, `def:higgs-like-field`; Lemmas `lm:Higgs-field-transform`, `lm:gluelump-gauge-invariant` | [CombLoops.lean](../lean/GluelumpPerimeterLaw/Endpoint/CombLoops.lean), [ConjugationSpanField.lean](../lean/GluelumpPerimeterLaw/Endpoint/ConjugationSpanField.lean), and the screened-observable APIs | The same nested unit-height rectangles give a nonzero covariant field; distinct far edges realize independent holonomies. The normalized field has pointwise norm at most one. |
| Lemma `lm:one-edge-positivity` | [ConjugationSpanOneLinkFactorization.lean](../lean/GluelumpPerimeterLaw/OneLink/ConjugationSpanOneLinkFactorization.lean), [ConcreteOneLinkLowerBound.lean](../lean/GluelumpPerimeterLaw/OneLink/ConcreteOneLinkLowerBound.lean) | Gauge-fix crossing bonds, expand the positive kernel, extract a fixed-degree nonzero endpoint mode, compare the local collar with Haar measure by finite energy, and cancel the common remote factor. The resulting bound is independent of box size. |
| Pass the seed to infinite volume | `conjSpanOneLinkLowerConstant_le_freeBoundaryLimit` in [FreeBoundaryLimitLowerBound.lean](../lean/GluelumpPerimeterLaw/OneLink/FreeBoundaryLimitLowerBound.lean) | The same fixed screening data and explicit positive constant work eventually in ordinary free-boundary boxes and pass through local convergence; the imaginary part vanishes. |
| One edge to a straight path, equation `eq:main-straight-lower-bound` | `conjSpanPhysicalStraightExpectation_rate_power_le` in [ConjSpanPhysicalStraightExpectation.lean](../lean/GluelumpPerimeterLaw/Propagation/ConjSpanPhysicalStraightExpectation.lean), instantiated by [ConjSpanPhysicalStraightLimit.lean](../lean/GluelumpPerimeterLaw/Propagation/ConjSpanPhysicalStraightLimit.lean) | Site and bond Cauchy–Schwarz give the two parity cases of log-convexity. Together with the seed and the norm bound at length zero, this gives `g_length >= q^length`. |
| Straight path to an L shape | `paperPhysicalStraightExpectation_sq_le_cornerBent` in [PaperCorner.lean](../lean/GluelumpPerimeterLaw/Propagation/PaperCorner.lean) | Diagonal vector Cauchy–Schwarz and the norm-one comparison field give `g_length^2 <= bent_length` for **every positive length**. |
| L shape to a square, equation `eq:main-square-lower-bound` | `paperCornerBent_sq_div_dimension_le_square` and `paperSquare_lower_bound_of_line_rate` in [PaperCorner.lean](../lean/GluelumpPerimeterLaw/Propagation/PaperCorner.lean) | Anti-diagonal matrix Cauchy–Schwarz with the unnormalized Hilbert–Schmidt pairing gives `bent_length^2 / dim(rho) <= w(length,length)`, hence `q^(4*length)/dim(rho) <= w(length,length)`. |
| Squares to rectangles | `paperRectangle_lower_bound_of_line_rate` in [PaperCorner.lean](../lean/GluelumpPerimeterLaw/Propagation/PaperCorner.lean), using [CanonicalRectangleExpectation.lean](../lean/GluelumpPerimeterLaw/Propagation/CanonicalRectangleExpectation.lean) | Reflection log-convexity, nonnegativity, and the unit upper bound imply monotonicity in each side. Choose the square of side **`max(R,T)`**, as in the paper. |
| Quantitative dependence and final assembly | [CouplingLowerBound.lean](../lean/GluelumpPerimeterLaw/OneLink/CouplingLowerBound.lean), [CouplingRate.lean](../lean/GluelumpPerimeterLaw/Propagation/CouplingRate.lean), [InfiniteVolumeQuantitative.lean](../lean/GluelumpPerimeterLaw/InfiniteVolumeQuantitative.lean) | Exhibit a fixed monomial/exponential seed, dominate its logarithmic rate by `1+beta+|log beta|`, and transport the canonical rectangle to every basepoint and coordinate plane. |

### Corner geometry

The rectangle spans the arm and **short** comb directions. The long comb
direction is outside its plane, just as for the paper's `Phi^{32}` in the
`1,2` plane. The coordinate names correspond as follows:

| Paper direction | Lean direction |
| --- | --- |
| `1`, arm | `Geometry.armAxis` (`Fin` value 0) |
| `2`, short in-plane comb direction | `Geometry.transverseAxis₂` (`Fin` value 2) |
| `3`, long out-of-plane comb direction | `Geometry.transverseAxis₁` (`Fin` value 1) |

[PaperCornerEndpoints.lean](../lean/GluelumpPerimeterLaw/Propagation/PaperCornerEndpoints.lean)
proves that the in-plane comb width is one, independently of the screening
degree. Lean splits a physical length into `s=length/2` and `t=length-s`;
its affine diagonal plane has offset `-s`. Translating by `s` in the arm
direction gives the paper's diagonal through the origin and anti-diagonal at
coordinate sum `length`. Path reversals and endpoint pullbacks are tracked
explicitly. Even and odd cases are both proved and then combined.

The previous odd-square/cofinal proof remains under the qualitative helper
`centerNeutralQualitativePerimeterLaw`. It is not the proof of the new
headline. The headline has neither `m <= length` nor odd-length restrictions,
and introduces no `m+3` square-enlargement loss.

## Constants and implementation details

The theorem's bound and quantifier order match the paper. The formal
one-edge proof uses a scalar endpoint mode and conservative coefficient and
incidence estimates. It does **not** certify the sharper numerical
prefactor and decay coefficient displayed in the paper's one-edge remark.
Those particular constants are not part of the headline theorem.

Precisely, `combEndpointDegree_eq` identifies
`N = m*(m+3)`. The formal uncapped seed at internal coupling `b` is proved by
`conjSpanOneLinkLowerConstant_eq_monomial_exp` to equal

```text
Q(b) = A0 * b^N * exp(-K0*b),
A0 = A^2 / (N! * H * (2*n)^N) > 0,
K0 = 20*d*|E| >= 0.
```

Here `A=conjSpanCombScalarMass`, `H=conjSpanCombExtractionBound`, and `E` is
the fixed endpoint collar. At paper coupling `beta`, put
`A1=A0*n^N` and `K1=K0*n`. All these data are fixed independently of `beta`,
the volume, the limiting measure, and the rectangle.

`monomialCouplingConstant` takes

```text
c0 = |log A1| + N + K1 + 1 > 0,
q(beta) = exp(-c0 * (1 + beta + |log beta|)) <= Q(n*beta).
```

This choice also lies strictly between zero and one. The reflection chain
therefore gives

```text
w(R,T) >= q(beta)^(4*max(R,T)) / r,    r=dim(rho).
```

`exp_neg_couplingWeight_rectangle_le_square` uses
`4*max(R,T) <= 2*perimeter`, `perimeter >= 4`, and
`1+beta+|log beta| >= 1`. The assembly can take the coupling-independent
constant

```text
C = 2*c0 + |log r|/4 > 0.
```

Lean permits degree `m=0`; the paper chooses a positive degree. The constant
screening-field case is harmless and satisfies the same argument. The
worked `SO(3)`, odd-orthogonal, and adjoint `SU(3)` examples and the appendix's
Haar-moment calculation remain expository material outside the formal
headline's proof path.

## Validation

The following builds completed successfully with Lean 4.30.0 and the locked
upstream dependency, using source-built dependencies. Run these commands from
the repository’s `lean/` folder:

```bash
lake --no-cache build GluelumpPerimeterLaw.InfiniteVolumePerimeterLaw  # 3573 jobs
lake --no-cache build GluelumpPerimeterLaw                          # 3577 jobs
lake --no-cache build GluelumpPerimeterLawTests                     # 3587 jobs
```

The strengthened headline's complete axiom footprint is `propext`,
`Classical.choice`, and `Quot.sound`. No placeholders, custom axioms, or unsafe
proof shortcuts were introduced. The finite-law adapter and quantitative and
all-length geometric claims above are kernel-checked declarations, rather
than proposed mathematical adapters.

The regression checks pin the `exists C, forall beta, forall mu` statement,
the all-length corner APIs, the neutral module import boundary, and the
standard axiom footprint. The separate strong-coupling corollary applies the strengthened headline at
paper coupling `beta_internal/n`; it is not an assumption of the
all-positive-coupling result.
