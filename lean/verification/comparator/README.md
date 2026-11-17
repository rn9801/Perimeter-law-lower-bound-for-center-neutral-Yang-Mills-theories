# Headline Comparator procedure

The [recorded run](../../../docs/validation/2026-11-17/README.md) checks the
real public headline and a separately written paper contract. All fixture
proofs are complete; none adds a proof placeholder or axiom declaration.
The `.lean.in` files are templates compiled in an isolated temporary project.
They do not alter the production theorem or add a Lake dependency to it.

- `Spec.lean.in`: the expanded paper contract and a proved equivalence with
  the headline proposition, in both directions.
- `Challenge.lean.in`: the expected public theorem, proved using the
  quantitative assembly instead of importing its public declaration.
- `Solution.lean.in`: imports the actual public theorem.
- `Mismatch.lean.in`: a negative control with an extra assumption, which
  Comparator must reject.
- `config.json`: the actual declaration names and the standard-axiom allowlist.

## Reproduce

First run the full project verification as described in
[lean/README.md](../../README.md). Use the project's Lean 4.30.0 toolchain.
Comparator and its exporter must be built at the recorded versions:

```sh
git clone https://github.com/leanprover/comparator.git /tmp/gluelump-comparator
git -C /tmp/gluelump-comparator checkout 1cfc5d8ad183bf65efe7accd0efc175b6b8f25b6
cd /tmp/gluelump-comparator
lake --no-cache build comparator lean4export
```

Build Landrun with Go 1.24 or later. The recorded run used Go 1.27.4 and the
following Landrun source revision:

```sh
git clone https://github.com/Zouuup/landrun.git /tmp/gluelump-landrun
git -C /tmp/gluelump-landrun checkout ec104f6edc1e14d7fec6d31146f1ec6f9c192c5a
cd /tmp/gluelump-landrun
go build -o /tmp/gluelump-landrun/landrun ./cmd/landrun
```

From this repository's root:

```sh
python3 lean/scripts/compare_headline.py \
  --comparator-root /tmp/gluelump-comparator \
  --landrun /tmp/gluelump-landrun/landrun \
  --landrun-source /tmp/gluelump-landrun \
  --output /tmp/gluelump-comparator-record
```

The driver requires Linux x86_64 and a working Landlock sandbox. It prebuilds
the trusted fixtures, uses the actual Landrun binary, and preserves every
filesystem restriction passed by upstream Comparator. A small CLI adapter
adds the argument separator required by current Landrun; it does not disable
sandboxing. A seccomp launcher denies creation of AF_UNIX sockets in the
Comparator process and its children, providing the address-family restriction
recommended by Comparator's current README without requiring a systemd user
bus. The recorded positive check and changed-statement rejection both used
these restrictions.

The driver records a successful overall result only if the genuine headline
passes and the changed-statement control is rejected. It uses the built-in
Lean kernel, not Nanoda. Comparator's trusted challenge uses existing proved
lemmas; this is a statement/dependency/axiom/kernel check, not a second
independent mathematical proof.
