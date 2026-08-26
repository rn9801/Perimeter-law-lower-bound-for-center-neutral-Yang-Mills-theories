# Mathematical assumptions and proof boundary

Updated: 2026-08-25

This document records the exact assumptions of the proved gluelump
perimeter-law lower bound. It distinguishes the model-neutral propagation
theorem, the completed-free-boundary thermodynamic-limit theorem, and the
concrete strong-coupling corollary.

## 1. Ambient lattice and gauge group

The public theorem assumes:

- a cubic lattice of dimension `d` with `3 ≤ d`;
- a compact Hausdorff second-countable topological group `G`;
- compatible measurable and Borel structures on `G`;
- a normalized Haar probability on `G`; and
- positive Haar measure for every nonempty open set.

The last condition is used in the strict one-link lower bound. No
connectedness, Lie-group, or differentiable-manifold hypothesis is present in
the final theorem.

## 2. Representation hypotheses

There are two finite-dimensional continuous unitary representations:

- `sigma`, the action representation used by the Wilson plaquette potential;
- `rho`, the representation used by the rectangular Wilson loop.

The public theorem assumes that `sigma.ρ` is injective, that `rho` is
irreducible, and that `rho` is center neutral. Center neutrality means that
the center of `G` acts trivially in `rho`.

The operational screening map is not an additional assumption. The proved
theorem `centerNeutral_exists_conjSpanIntertwiner` constructs a tensor degree
`m` and a nonzero equivariant map

```text
(ConjSpan sigma)^⊗m → rho.dual
```

from faithfulness of `sigma` and center neutrality of `rho`. Irreducibility
is retained in the human-facing theorem and is used by the converse
screening characterization; the forward construction needed for the lower
bound does not require it.

## 3. Coupling and thermodynamic-limit hypothesis

The completed-free-boundary theorem assumes `beta > 0` and a probability
measure `mu` satisfying
`IsTranslationInvariantFreeBoundaryLimit sigma.wilsonPotential beta mu`.
This structure has two fields:

1. every local continuous observable converges to its `mu` expectation along
   the completed link-symmetric box exhaustion, for every choice of elongated
   coordinate direction; and
2. `mu` is invariant under every lattice translation.

The common limit for every elongation direction is the shape compatibility
that puts link, site, diagonal, and anti-diagonal reflection positivity in one
state. It is stronger than convergence along one arbitrarily chosen sequence
of boxes.

This limit condition is a hypothesis of the general infinite-volume theorem,
not a uniqueness claim for all Gibbs states. In the positive strong-coupling
interval it is discharged by the downstream compatibility theorem
`wilsonStrongCoupling_isTranslationInvariantFreeBoundaryLimit`, which is
proved from the thermodynamic-limit infrastructure on unchanged upstream
`main`.

## 4. Model-neutral propagation theorem

The theorem
`YangMills.Gluelump.Propagation.conjSpanPerimeterLaw_of_positiveOneLink`
does not mention a coupling, finite-volume action, cluster expansion, or
strong-coupling radius. It takes:

- a probability measure `mu`;
- a `ReflectionPositiveState mu` certificate containing translation
  invariance and the site, link, diagonal, and anti-diagonal reflection
  consequences used by the proof;
- the exact gauge-fixed crossing-link callbacks for the gluelump line and
  rectangle halves;
- coordinate-swap invariance;
- the direct conjugation-span endpoint map `T`; and
- a number `q` with `0 < q ≤ 1` below the one-bond screened expectation.

It returns one positive rate and, for every basepoint, every ordered pair of
distinct coordinate axes, and all positive rectangle side lengths, proves
both literal reality of the complex Wilson expectation and an exponential
lower bound in the perimeter.

The completed-free-boundary adapter proves all of these reflection and
crossing interfaces and constructs a uniform positive `q`. Thus none of
them remains an unproved assumption in the public theorem.

## 5. Strong-coupling specialization

The concrete downstream theorem
`YangMills.Gluelump.InfiniteVolume.centeredInfiniteVolume_centerNeutralPerimeterLaw`
adds the small-coupling condition supplied by the upstream construction

```text
‖(beta : ℂ)‖ < latticeStrongCouplingRadius d sigma.wilsonPotential.bound.
```

It applies the abstract result to the cluster-constructed centered
infinite-volume Wilson probability with identity exterior data. The rate is
chosen before the radius witness and before the rectangle data.

The strong-coupling radius is used only to construct and identify the
thermodynamic-limit state. The reflection-propagation theorem itself works at
every positive coupling whenever its state and one-link hypotheses hold.

## 6. Quantifier dependencies and conclusion

At fixed `d`, `sigma`, `rho`, and positive `beta`, the public theorem chooses
`rate > 0` before quantifying over:

- the limiting probability `mu`;
- the rectangle basepoint;
- the two distinct coordinate axes; and
- the positive side lengths `R` and `T`.

Consequently the rate is uniform in all of those data. The theorem does not
claim an optimal or explicit asymptotic rate. Its conclusion is

```text
E_mu[W_rho(rectangle)] ∈ ℝ,
exp (-rate * 2 * (R + T)) ≤ E_mu[W_rho(rectangle)].
```

Reality is a proved equality in `ℂ`; the lower bound is therefore stated on
the real expectation itself, not merely on an unexplained real part.

## 7. What is not claimed

The current theorem does not assert:

- an infinite-volume Gibbs-state uniqueness theorem outside the upstream
  strong-coupling regime;
- a finite-volume bound with hard Dirichlet boundary conditions;
- diagonal reflection positivity for unrestricted observables on the
  standard periodic torus;
- an optimal quantitative dependence of the rate on `beta`; or
- Osterwalder--Schrader reconstruction or a particle mass statement.

These omissions are deliberate and are not hidden proof obligations in the
declared theorem.

## 8. Placeholder and axiom audit

The shipped production and regression modules contain no proof placeholders,
custom assumptions declared with Lean's `axiom` command, or unsafe
declarations. Focused regression files use `#print axioms` on the headline
theorems and report only Lean's standard

- `propext`;
- `Classical.choice`; and
- `Quot.sound`.

The standalone source consists of 110 gluelump theorem modules, 28 additive
compatibility modules, and 10 regression modules. The package is configured
to depend only on the unchanged `main` branch of
`strong-coupling-lattice-yang-mills`; the compatibility modules live under
downstream-owned `GluelumpPerimeterLaw.Upstream.*` paths. The final clean-main
build and manifest refresh passed against upstream commit
`bc7383d023f0c58a16312764a32422248aa42ebe`; they required no upstream merge.

If a future upstream `main` incorporates one of the overlaid declarations,
the corresponding downstream extension must be removed and its imports
retargeted in the same update. This is a source-maintenance obligation, not a
new mathematical assumption of the theorem.
