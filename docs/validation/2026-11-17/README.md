# Complete Lean build and proof audit

Recorded on 2026-11-17, in the America/New_York time zone, against mathematical
source commit `35c788d1dd433c403d1f34073efcb26ce70bf15c`. This update adds
verification tooling and records; the mathematical Lean sources are unchanged.

**Every one of the 157 tracked Lean modules compiled, and all 157 passed
kernel replay. No project-defined axioms or proof placeholders were found.**

| Check | Result |
| --- | --- |
| Source inventory | All 157 tracked production and regression `.lean` files |
| Source guards | No `sorry`, `admit`, `sorryAx`, `native_decide`, axiom/constant declarations, or unsafe code |
| Fresh project build | 157 project traces invalidated; all 157 modules rebuilt successfully |
| Regression suite | `GluelumpPerimeterLawTests` passed |
| Compiled declaration audit | 2,673 declarations checked; zero project axiom declarations and zero unsafe declarations |
| Transitive axiom dependencies | Only `propext`, `Classical.choice`, and `Quot.sound` |
| Kernel replay | All 157 project modules accepted by Lean's `leanchecker` |
| Headline Comparator | Actual public theorem and independent statement-equivalence theorem accepted |
| Comparator negative control | Adding an extra assumption changed the statement and was rejected |

## What “no axioms introduced” means

The project introduces no global axiom declarations. Its proofs use Lean's
standard propositional extensionality, classical choice, and quotient
soundness principles: `propext`, `Classical.choice`, and `Quot.sound`.
The claim is **no extra axioms**, rather than an axiom-free foundation.

The audit imports every tracked Lean module, identifies project declarations
by their defining module (including the compatibility overlay), rejects
compiled axiom or unsafe declarations, and runs `Lean.collectAxioms` on every
one. This also checks definitions and opaque bodies, not just theorem names.
The [complete per-declaration results](axioms.json) include the headline,
quantitative assembly, model-neutral theorem, and strong-coupling corollary.
Each headline's footprint is exactly the three standard principles above.

The compact-group, representation, positive-coupling, and common-limit
assumptions remain explicit hypotheses in the theorem. They are not hidden
global axioms. In particular, this does not prove existence of the
infinite-volume state at every coupling.

## What compiled

Earlier public-root and regression builds covered their import closures.
This check additionally inventories and explicitly builds every tracked Lean
module, including the standalone `DualIrreducible` and `CenteredGibbsTower`
modules. It does not infer complete coverage from the default target alone.

Only project build traces were invalidated. The existing pinned dependency
caches were reused; this is a fresh rebuild of all project modules, not a
fresh source rebuild of every Mathlib dependency.

- Lean: `4.30.0`, release commit `d024af099ca4bf2c86f649261ebf59565dc8c622`.
- Lake: `5.0.0-src+d024af0`.
- Direct Strong-Coupling dependency: `bc7383d023f0c58a16312764a32422248aa42ebe`.
- Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

[build.json](build.json) records versions, dependency revisions, every source
and `.olean` hash, commands, durations, exit codes, and log hashes.

| Phase | Exit | Complete log |
| --- | --- | --- |
| Narrow headline build | 0 | [narrow-build.log](narrow-build.log) |
| Explicit build of all 157 modules | 0 | [all-modules-build.log](all-modules-build.log) |
| Regression build | 0 | [regression-build.log](regression-build.log) |
| Compiled axiom audit | 0 | [compiled-axiom-audit.log](compiled-axiom-audit.log) |
| Replay of all project modules | 0 | [kernel-replay.log](kernel-replay.log) |

The logs retain ordinary linter warnings and five Lean 4.30 native compiler
`PANIC` diagnostics associated with `conjSpanTraceToDual`. Lake returned zero
and produced the proof objects; all project declarations then passed kernel
replay, and the headline passed Comparator's fresh-kernel check. This record
does not claim a warning-free build or successful execution of that
auxiliary definition's generated native code.

Reproduce from the repository root with the recorded Lean toolchain in PATH:

```sh
python3 lean/scripts/verify.py --rebuild-project --output /tmp/gluelump-verification
```

CI now runs the full inventory/build/audit/replay procedure and uploads its
logs and JSON as the `lean-build-and-axiom-audit` artifact.

## Headline Comparator check

The check uses the official
[Lean Comparator v4.30.0](https://github.com/leanprover/comparator/tree/1cfc5d8ad183bf65efe7accd0efc175b6b8f25b6),
matching the project's toolchain, and its pinned `lean4export` revision
`a3e35a584f59b390667db7269cd37fca8575e4bf`.

The [separate contract](../../../lean/verification/comparator/Spec.lean.in)
spells out the paper's quantifier order, the ordinary free-boundary local
limit at coupling `dim(sigma) * beta`, translation invariance, and normalized
Wilson integrals. A kernel-checked **if and only if** theorem relates this
contract to the public headline statement. It is not merely a check that the
theorem's name exists.

Comparator then compares the exports for these actual declarations:

```text
YangMills.Gluelump.InfiniteVolume.centerNeutralInfiniteVolumePerimeterLaw
YangMills.Gluelump.Validation.headlineStatement_iff_contract
```

The solution imports the existing public headline; it does not replace it
with a wrapper. The trusted challenge uses the already proved quantitative
assembly, so both sides have complete proofs and introduce no new postulates
or proof holes. The fixtures are generated in a temporary Lake project;
the original dependency declarations and manifest are unchanged.

Comparator verifies matching statement dependencies, enforces the three-axiom
allowlist, and replays the exported solution in a fresh Lean environment.
The [successful log](headline-comparator.log) ends with:

```text
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

A [negative control](../../../lean/verification/comparator/Mismatch.lean.in)
adds the desired conclusion as an extra assumption. It is a valid but
different theorem. Comparator rejects it with
`Challenge and solution theorem statement do not match`; see the
[control log](comparator-negative-control.log). Its nonzero exit is the
expected successful outcome of that control.

[comparator.json](comparator.json) contains the exact configuration, tool
revisions, binary and input hashes, exit codes, and timings. The
[fixture-build log](comparator-fixture-build.log) records compilation of all
four comparison fixtures. See the
[reproduction instructions](../../../lean/verification/comparator/README.md).

These checks use Lean's kernel. Nanoda or another independently implemented
kernel was not run, and the fixtures do not provide an independent
mathematical proof. The interpretation of the paper is spelled out in the
[paper–Lean comparison](../../../comparison/PAPER_LEAN_COMPARISON.md).
