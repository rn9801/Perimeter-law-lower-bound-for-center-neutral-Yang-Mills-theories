# Paper and Lean comparison

Reviewed on 2026-11-17 against project commit `bb329e3` and the locked
Strong-Coupling dependency `bc7383d023f0c58a16312764a32422248aa42ebe`.
The accompanying manuscript edit changes only the AI acknowledgment.

The Lean headline proves the qualitative perimeter-law conclusion using the
same main proof strategy. The paper additionally states a uniform quantitative
bound on the coupling dependence. That stronger quantifier order is not in
the Lean headline. Conventions for the action and finite-volume law also need
to be identified when translating between the two statements.

## The headline statements

The paper's main theorem, in
[main.tex](Gluelump_Perimeter_Law_Lower_Bound/main.tex), asserts a constant
`C = C(G, sigma, tau, d) > 0`, independent of the positive coupling and the
rectangle, such that

```text
E[W_tau(rectangle)] >= exp(-C * (1 + beta + |log beta|) * perimeter).
```

The corresponding Lean theorem is
`YangMills.Gluelump.InfiniteVolume.centerNeutralInfiniteVolumePerimeterLaw`
in [InfiniteVolumePerimeterLaw.lean](../GluelumpPerimeterLaw/InfiniteVolumePerimeterLaw.lean).
Its conclusion is defined in
[InfiniteVolumePerimeterLawStatement.lean](../GluelumpPerimeterLaw/InfiniteVolumePerimeterLawStatement.lean):

```text
for every beta > 0, there exists rate > 0 such that
for every common translation-invariant completed-box limit mu,
and every positive-sided coordinate rectangle,
  E_mu[W_rho(rectangle)] is real, and
  exp(-rate * perimeter) <= E_mu[W_rho(rectangle)].
```

Thus the public Lean statement has `for every beta, there exists rate`,
whereas the paper bounds all those rates using one coupling-independent `C`.
The Lean rate is chosen before the measure and rectangle, so its uniformity
in those data does match the paper.

| Item | Paper | Lean | Assessment |
| --- | --- | --- | --- |
| Dimension | `d >= 3` | `3 <= d` | Same. |
| Group | Compact Lie group | Compact Hausdorff second-countable topological group with normalized Haar probability and Borel structure | No Lie-group structure is used in the formal proof; the paper's setting supplies the topological hypotheses. |
| Action representation | Faithful continuous unitary `sigma` on nonzero `V` | Injective `sigma.ρ`, continuous unitary, positive dimension | Same representation assumption. |
| Wilson representation | Center-neutral continuous unitary `tau` on nonzero `S` | Center-neutral `rho`, continuous unitary, positive dimension | Same; neither headline requires irreducibility. |
| Wilson observable | `Tr(tau(Q_loop)) / dim(tau)` | `rho.normalizedCharacter (holonomy A loop)` | Same normalization. |
| Rectangle | Coordinate rectangle | Arbitrary basepoint, distinct ordered axes, positive natural side lengths | Same nondegenerate rectangles; perimeter is `2*(R+T)`. |
| Limit assumption | One translation-invariant local limit for every elongated coordinate-box family | `IsTranslationInvariantFreeBoundaryLimit`, for every elongation axis and every continuous local observable | Same form of convergence, subject to the finite-law convention below. |
| Reality | Implicit in the real inequality, proved in the argument | Explicit equality of the complex expectation with its real part embedded in `Complex` | Lean makes this part explicit. |

The paper's uniqueness of the common weak limit is not an extra ingredient
of the Lean proof. A prescribed sequence cannot have two different weak
limits; neither statement asserts uniqueness of all infinite-volume Gibbs
states.

## Action normalization: rescale the coupling

Let `n = dim(V)`, `beta_P` be the paper's coupling and `beta_L` the Lean
coupling. The paper uses

```text
2 * beta_P * sum_{geometric plaquettes} Re Tr(sigma(Q_p)).
```

Lean's `sigma.wilsonPotential` is `Re Tr(sigma(g)) / n`, and its Boltzmann
weight is `exp(beta_L * FiniteVolume.action ...)`. Importantly, the active
plaquette set contains BOTH ordered axis labels `(i,j)` and `(j,i)` for
each geometric plaquette. These have inverse holonomies and equal real
potentials. On the same geometric plaquette set the Lean action is therefore

```text
(2 * beta_L / n) * sum_{geometric plaquettes} Re Tr(sigma(Q_p)).
```

The conversion is **`beta_L = n * beta_P`**. It would be incorrect to insert
another factor of two after already counting both ordered axis labels.
This fixed rescaling preserves the class of bounds
`C * (1 + beta + |log beta|)`, with a changed representation-dependent `C`.

Sources in the pinned dependency:
[Wilson/Representation.lean](https://github.com/rn9801/strong-coupling-lattice-yang-mills/blob/bc7383d023f0c58a16312764a32422248aa42ebe/YangMills/Wilson/Representation.lean),
[Gauge/FiniteVolume.lean](https://github.com/rn9801/strong-coupling-lattice-yang-mills/blob/bc7383d023f0c58a16312764a32422248aa42ebe/YangMills/Gauge/FiniteVolume.lean),
and [StrongCoupling/Counting.lean](https://github.com/rn9801/strong-coupling-lattice-yang-mills/blob/bc7383d023f0c58a16312764a32422248aa42ebe/YangMills/StrongCoupling/Counting.lean)
(`incidentPlaquettes`).

## Finite-volume packaging

The paper integrates internal box edges and includes only plaquettes
contained in the box. Lean's `linkSymmetricSpecification` starts from the
same site box, includes every plaquette incident to an internal edge, and
makes all edges of those plaquettes dynamic; unused exterior edges are set
to the identity. See the pinned
[ConcreteLinkReflectionPositivity.lean](https://github.com/rn9801/strong-coupling-lattice-yang-mills/blob/bc7383d023f0c58a16312764a32422248aa42ebe/YangMills/StrongCoupling/ConcreteLinkReflectionPositivity.lean).

For these rectangular boxes there is a mathematical reconciliation: each
added geometric boundary plaquette has an outer edge belonging to no other
active geometric plaquette. Integrating that Haar variable removes the
plaquette's Boltzmann factor up to a constant independent of the remaining
variables, after grouping the two orientation labels. Repeating this for the
added plaquettes shows that the internal-edge marginal is the ordinary
free-boundary law, at the rescaled coupling above. Thus any fixed local
observable eventually sees the same expectations in both conventions.

This argument does not use strong coupling. However, I did not find a Lean
lemma identifying that marginal with the paper's internal-edge-only law.
The formal headline remains stated in terms of the completed sequence;
a literal paper-convention corollary should include this identification.
This is a missing formal adapter, rather than evidence of a different
infinite-volume physical model.

## Correspondence of proof steps

| Paper step | Lean declarations/files | Comparison |
| --- | --- | --- |
| Center neutrality gives a nonzero screening map from a tensor power of the conjugation span | [CenterScreening.lean](../GluelumpPerimeterLaw/RepresentationTheory/CenterScreening.lean), [TensorGeneration.lean](../GluelumpPerimeterLaw/RepresentationTheory/TensorGeneration.lean) | Both pass to `G/Z(G)`, use Stone--Weierstrass to detect a coefficient, and Haar-average a rank-one map. Lean uses an explicit self-duality equivalence and tensor words; it does not need irreducible decomposition. |
| Build a nonzero covariant field from nested rectangular loops | [CombLoops.lean](../GluelumpPerimeterLaw/Endpoint/CombLoops.lean), [ConjugationSpanField.lean](../GluelumpPerimeterLaw/Endpoint/ConjugationSpanField.lean) | Same literal loop-holonomy tensor construction and independent far-edge nonvanishing argument. Lean normalizes the endpoint canonically; the paper rescales `T`. |
| Gauge-fix the crossing bonds and extract a positive one-edge lower bound | [ConjugationSpanOneLinkFactorization.lean](../GluelumpPerimeterLaw/OneLink/ConjugationSpanOneLinkFactorization.lean), [ConcreteOneLinkLowerBound.lean](../GluelumpPerimeterLaw/OneLink/ConcreteOneLinkLowerBound.lean) | Same positive crossing-kernel expansion, fixed-degree polynomial extraction, local finite-energy estimate, and cancellation of volume-dependent remote factors. Lean selects a nonzero scalar endpoint mode and uses coarser coefficient/incidence estimates; the paper estimates the vector polynomial directly. Their numerical constants differ. |
| Pass the one-edge bound to the common limit | [FreeBoundaryLimitLowerBound.lean](../GluelumpPerimeterLaw/OneLink/FreeBoundaryLimitLowerBound.lean) | Same convergence of continuous local observables; the uniform finite-volume lower bound survives. |
| Propagate along straight lines | [ConjSpanPhysicalStraightExpectation.lean](../GluelumpPerimeterLaw/Propagation/ConjSpanPhysicalStraightExpectation.lean) | Both combine site and bond reflection positivity to obtain log-convexity and a lower bound `q^length`. Lean explicitly tracks even/odd gluings and gauge-fixed crossing families. |
| Bend a line into an L and close a square | [ConjSpanCornerExpectation.lean](../GluelumpPerimeterLaw/Propagation/ConjSpanCornerExpectation.lean), [ConjSpanCornerEndpoints.lean](../GluelumpPerimeterLaw/Propagation/ConjSpanCornerEndpoints.lean) | Same two diagonal Cauchy--Schwarz steps and dimension factor, but different endpoint orientation and square-length restrictions; see below. |
| Compare squares with arbitrary rectangles | [CofinalRectangleCertificate.lean](../GluelumpPerimeterLaw/Propagation/CofinalRectangleCertificate.lean), [CanonicalCofinalPerimeterLaw.lean](../GluelumpPerimeterLaw/Propagation/CanonicalCofinalPerimeterLaw.lean) | Both use rectangle log-convexity, the unit upper bound, monotonicity, and translation/axis symmetry. Lean first chooses a sufficiently large odd square; the paper uses the square with side `max(R,T)`. |

### The corner geometry differs

The paper uses `Phi^{32}` along direction `1`, with the long comb direction
`3` outside the rectangle's `1,2` plane. Its comb width within that plane is
only one lattice unit. The bending and closing inequalities are therefore
established for every positive integer side length `n`.

Lean's base comb has long direction `transverseAxis1`, which is also the
second axis of the rectangle used for the corner argument; see
[TransverseLoops.lean](../GluelumpPerimeterLaw/Endpoint/TransverseLoops.lean).
The comb extends `m` units within that plane. The formal bend used by the
headline requires odd physical length `ell = 2*l+1` with `m <= ell`.
This is recorded explicitly by `CofinalRectangleReflectionCertificate m r`.

Lean compensates by enlarging to a sufficiently large odd square and obtains
the weaker but positive perimeter base

```text
B = q^(2*(m+3)) / r,       r = dim(tau),       0 < q <= 1/2.
```

The paper instead uses `w(n,n) >= c^(4*n)/r` at every positive `n`, then
`n = max(R,T)`, giving its sharper displayed intermediate constants.
This is a genuine difference in the implemented proof geometry, not a gap
in the qualitative Lean conclusion.

Lean also allows tensor degree `m = 0`, whereas the paper chooses a positive
degree. This harmless difference handles a constant screening field; one
can pad with the invariant identity matrix to obtain a positive degree.

The paper's worked `SO(3)`, `SO(2N+1)` and adjoint `SU(3)` examples and the
odd-orthogonal Haar-moment calculation are expository additions. I did not
find corresponding worked-example lemmas in the production or regression
sources; the formal headline uses the general screening existence theorem.

## How close is Lean to the paper's coupling bound?

The supporting code contains substantially more quantitative information
than the headline exposes. From `conjSpanOneLinkLowerConstant`,
`allCouplingLowerConstant`, `collarFiniteEnergyFactor` and
`linkCombLocalKernelBound`, its uncapped one-link constant simplifies
mathematically to

```text
q0(beta_L) = C0 * beta_L^N * exp(-20*d*|E|*beta_L),
C0 = A^2 / (N! * H * (2*n)^N) > 0,
N = sum of the comb loop lengths,
E = the fixed comb collar,
A = conjSpanCombScalarMass,
H = conjSpanCombExtractionBound.
```

These are finite-volume-independent constants. The main proof uses
`q = min(q0,1/2)`, the base `B` above, and
`rate = -log(min(B,1/2))`. Fixing `m,T` independently of the coupling and
taking logarithms gives the paper's growth class
`O(1 + beta_L + |log beta_L|)`. Rescaling the coupling preserves that class.

Consequently the quantitative claim looks like an additional formal
assembly step, rather than a need for a different positivity argument.
The remaining work is to choose the screening data before quantifying over
`beta`, bound the logarithm uniformly, and export the paper's stronger
coupling-independent-`C` statement. The code's coarser constants need not
equal the particular constants displayed in the paper.

The exact definitions are in
[UniformPositivity.lean](../GluelumpPerimeterLaw/OneLink/UniformPositivity.lean),
[ConcreteOneLinkLowerBound.lean](../GluelumpPerimeterLaw/OneLink/ConcreteOneLinkLowerBound.lean),
[LocalIncidence.lean](../GluelumpPerimeterLaw/OneLink/LocalIncidence.lean),
and [ConcreteLocalKernelBound.lean](../GluelumpPerimeterLaw/OneLink/ConcreteLocalKernelBound.lean).

## Strong coupling and verification scope

Despite some supporting modules living under `StrongCoupling`, the general
headline assumes only positive coupling and the common local-limit
hypothesis. The separate theorem
`centeredInfiniteVolume_centerNeutralPerimeterLaw` adds a small-coupling
radius to construct that state. It is not the theorem to compare with the
paper's all-positive-coupling conditional result.

This review traced the source statements and their live proof dependencies.
It is not a fresh kernel-check certificate: `lake --no-build build
GluelumpPerimeterLaw` reports missing/out-of-date dependency artifacts, and
the Mathlib cache host still returns proxy `CONNECT 403`. No Lean proof
source or theorem statement was changed. The updated manuscript was rebuilt
with LaTeX/BibTeX, and the acknowledged writing/proof assistance was checked
in the resulting PDF.
