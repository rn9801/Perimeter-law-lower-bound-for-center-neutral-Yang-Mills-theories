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

- `YangMills.Gluelump.Propagation.conjSpanPerimeterLaw_of_positiveOneLink`
  derives the full lower bound from a positive direct one-link gluelump seed
  and model-neutral reflection-positive-state interfaces.
- `YangMills.Gluelump.InfiniteVolume.centerNeutralInfiniteVolumePerimeterLaw`
  applies the construction to every translation-invariant common local limit
  of the completed free-boundary reflection boxes.
- `YangMills.Gluelump.InfiniteVolume.centeredInfiniteVolume_centerNeutralPerimeterLaw`
  specializes the result to the cluster-constructed centered Wilson state in
  the positive strong-coupling interval.

The theorem is stated for every basepoint, every ordered pair of distinct
coordinate axes, and all positive side lengths.  It proves that the Wilson
loop expectation is real and gives an exponential lower bound in the loop
perimeter.  The rate is chosen before the limiting measure and rectangle
data.

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
