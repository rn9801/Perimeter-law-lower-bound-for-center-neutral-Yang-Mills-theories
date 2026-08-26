# Repository instructions

## Goal

Maintain the standalone Lean formalization of the center-neutral gluelump
perimeter-law lower bound.

## Required workflow

- Audit Mathlib and the upstream Strong-Coupling sources before adding APIs.
- Preserve Apache-2.0 provenance for extracted or adapted source.
- Build the narrow target, then `lake build GluelumpPerimeterLawTests`.
- Never add `sorry`, `admit`, custom axioms, or unsafe proof shortcuts.
- Update `STATUS.md` after every coherent milestone.

## Dependency rules

- The only direct Lake dependency is the `main` branch of
  `rn9801/strong-coupling-lattice-yang-mills`.
- Production module paths use `GluelumpPerimeterLaw.*`; declaration namespaces
  remain `YangMills.Gluelump.*`.
- Neutral endpoint and propagation modules must not import
  `YangMills.StrongCoupling` or `YangMills.Polymer`.
- Strong-coupling imports are confined to explicit downstream adapters and
  concrete corollaries.
- Do not duplicate upstream lattice, gauge, Wilson, or thermodynamic-limit
  infrastructure.
