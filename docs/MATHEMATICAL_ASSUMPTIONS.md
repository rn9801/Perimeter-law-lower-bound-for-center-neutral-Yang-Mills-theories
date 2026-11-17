# Mathematical assumptions and proof boundary

Updated: 2026-11-17

This document records the exact assumptions of the proved gluelump
perimeter-law lower bound. It distinguishes the model-neutral propagation
theorem, the ordinary free-boundary thermodynamic-limit theorem, and the
concrete strong-coupling corollary.

## 1. Ambient lattice and gauge group

The public theorem assumes:

- a cubic lattice of dimension `d` with `3 ≤ d`;
- a compact Hausdorff second-countable topological group `G`;
- compatible measurable and Borel structures on `G`;
- a normalized Haar probability on `G`.

Positive Haar measure for every nonempty open set is used in the strict
one-link lower bound, but it is not an additional assumption. Mathlib derives
it from compactness, probability normalization, and left invariance. No
connectedness, Lie-group, or differentiable-manifold hypothesis is present in
the final theorem.

## 2. Representation hypotheses

There are two finite-dimensional continuous unitary representations:

- `sigma`, the action representation used by the Wilson plaquette potential;
- `rho`, the representation used by the rectangular Wilson loop.

The public theorem assumes that `sigma.ρ` is injective and that `rho` is
center neutral. Center neutrality means that the center of `G` acts trivially
in `rho`; the theorem also applies when `rho` is reducible.

The operational screening map is not an additional assumption. The proved
theorem `centerNeutral_exists_conjSpanIntertwiner` constructs a tensor degree
`m` and a nonzero equivariant map

```text
(ConjSpan sigma)^⊗m → rho
```

from faithfulness of `sigma` and center neutrality of `rho`.  The construction
uses `faithful_selfDual_tensorPower_mapsTo_rep` directly with `rho` as its
target.  Consequently the Higgs-like endpoint takes values in `rho` and
transforms by the ordinary `rho(g)` action; the operational proof no longer
passes through `rho.dual` or a fixed-coordinate duality conversion.
Irreducibility is used only by the converse screening characterization
`centerNeutral_iff_exists_conjSpanIntertwiner`: it is not needed by the
forward construction or either headline perimeter-law theorem.

## 3. Coupling and thermodynamic-limit hypothesis

The ordinary free-boundary theorem assumes `beta > 0` and a probability
measure `mu` satisfying
`IsTranslationInvariantPaperFreeBoundaryLimit sigma beta mu`. This is the
ordinary local limit at normalized-potential coupling `n*beta`, where
`n=dim(sigma)`, so `beta` has the paper's convention.
This structure has two fields:

1. every local continuous observable converges to its `mu` expectation along
   the ordinary internal-edge box exhaustion, for every choice of elongated
   coordinate direction; and
2. `mu` is invariant under every lattice translation.

The common limit for every elongation direction is the shape compatibility
that puts link, site, diagonal, and anti-diagonal reflection positivity in one
state. It is stronger than convergence along one arbitrarily chosen sequence
of boxes.

The common local limit is unique by
`IsTranslationInvariantFreeBoundaryLimit.unique`; the local observable
expectations determine it. This is not a uniqueness theorem for all Gibbs
states at arbitrary coupling. In the positive strong-coupling
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

The ordinary free-boundary adapter proves all of these reflection and
crossing interfaces and constructs a uniform positive `q`. Thus none of
them remains an unproved assumption in the public theorem.

## 5. Strong-coupling specialization

The concrete downstream theorem
`YangMills.Gluelump.InfiniteVolume.centeredInfiniteVolume_centerNeutralPerimeterLaw`
adds the small-coupling condition supplied by the upstream construction

```text
‖(beta : ℂ)‖ < latticeStrongCouplingRadius d sigma.wilsonPotential.bound.
```

Here `beta` uses the upstream normalized-potential convention; the proof
applies the headline at paper coupling `beta/n`. It applies the result to the cluster-constructed centered
infinite-volume Wilson probability with identity exterior data. The rate is
chosen before the radius witness and before the rectangle data.

The strong-coupling radius is used only to construct and identify the
thermodynamic-limit state. The reflection-propagation theorem itself works at
every positive coupling whenever its state and one-link hypotheses hold.

## 6. Quantifier dependencies and conclusion

At fixed `d`, `sigma`, and `rho`, the public theorem chooses `C > 0` before
quantifying over the positive paper coupling `beta`, the limiting probability
`mu`, the rectangle basepoint, its distinct coordinate axes, and its positive
side lengths. Its conclusion is

```text
E_mu[W_rho(rectangle)] ∈ ℝ,
exp (-C * (1 + beta + |log beta|) * 2 * (R + T)) ≤ E_mu[W_rho(rectangle)].
```

The screening data are chosen before `beta`. The scalar seed and all-length
short-axis corner proof are documented in
[PAPER_LEAN_COMPARISON.md](../comparison/PAPER_LEAN_COMPARISON.md). The formal proof uses
conservative numerical constants; it asserts the paper's growth class, not
optimality of those constants.

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

The [recorded full build and audit](validation/2026-11-17/README.md) covers all
157 tracked production and regression modules. It found no `sorry`, `admit`,
`sorryAx`, `native_decide`, project axiom/constant declarations, or unsafe
code. All 2,673 compiled project declarations were checked for transitive
axiom dependencies, including definitions and opaque bodies. There were
zero project-defined axioms and zero unsafe declarations. The only axiom
dependencies were Lean's standard

- `propext`;
- `Classical.choice`; and
- `Quot.sound`.

Each audited headline theorem has exactly this three-axiom footprint.
Thus “no axioms introduced” means no additional project axioms; it does not
mean that classical choice, propositional extensionality, and quotient
soundness have been eliminated. Explicit theorem hypotheses such as
faithfulness, center neutrality, and existence of the common limit remain
hypotheses, not global axioms.

Every project module was freshly rebuilt and accepted by kernel replay.
The record retains the build logs, including the native-code-generation
diagnostics described there, and the successful official Comparator check
of the headline and its expanded paper contract.

The standalone source contains 30 additive compatibility modules and 10
regression modules, in addition to the gluelump theorem modules. The package is configured
to depend only on the unchanged `main` branch of
`strong-coupling-lattice-yang-mills`; the compatibility modules live under
downstream-owned `GluelumpPerimeterLaw.Upstream.*` paths. The final clean-main
build and manifest refresh passed against upstream commit
`bc7383d023f0c58a16312764a32422248aa42ebe`; they required no upstream merge.

If a future upstream `main` incorporates one of the overlaid declarations,
the corresponding downstream extension must be removed and its imports
retargeted in the same update. This is a source-maintenance obligation, not a
new mathematical assumption of the theorem.
