# Lean formalization

This folder is the Lean project. Open it as the project directory when using
the Lean editor extension.

- [Main theorem statement](GluelumpPerimeterLaw/InfiniteVolumePerimeterLawStatement.lean)
- [Main theorem proof](GluelumpPerimeterLaw/InfiniteVolumePerimeterLaw.lean)
- [Quantitative proof assembly](GluelumpPerimeterLaw/InfiniteVolumeQuantitative.lean)
- [Supporting proofs](GluelumpPerimeterLaw/)
- [Regression checks](GluelumpPerimeterLawTests/)
- [Paper–Lean correspondence](../comparison/PAPER_LEAN_COMPARISON.md)

From the repository root:

```sh
cd lean
lake build GluelumpPerimeterLaw
lake build GluelumpPerimeterLawTests
```

The toolchain and dependency versions are recorded in `lean-toolchain` and
`lake-manifest.json`. The only direct dependency is the upstream
[Strong-Coupling project](https://github.com/rn9801/strong-coupling-lattice-yang-mills).
Lean module names and mathematical declarations are unchanged by the folder
organization. See [LICENSE](../LICENSE) and [NOTICE](../NOTICE) for provenance.
