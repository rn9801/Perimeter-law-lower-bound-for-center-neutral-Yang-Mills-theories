# Gluelump perimeter-law lower bound

This Lean 4 project proves a center-neutral gluelump perimeter-law lower bound
for lattice Yang--Mills theory.  It is the standalone downstream companion to
[`strong-coupling-lattice-yang-mills`](https://github.com/rn9801/strong-coupling-lattice-yang-mills).

The package has exactly one direct Lake dependency: the `main` branch of that
repository.  Mathlib, the lattice/gauge foundations, reflection positivity,
and the strong-coupling thermodynamic-limit construction arrive transitively
through it.

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

See [the roadmap](docs/ROADMAP.md), [the mathematical assumptions](docs/MATHEMATICAL_ASSUMPTIONS.md),
and [the status ledger](STATUS.md).

## License and provenance

The project is released under Apache-2.0.  The initial standalone source was
extracted from the gluelump development in
`strong-coupling-lattice-yang-mills`; individual Lean files retain their
original copyright and contributor notices.  See [NOTICE](NOTICE).
