# Comparator

Comparator checks [`FsFltz.geometricTarget`](../../FsFltz/Geometry/GeometricComparisonAssembly.lean)
against the independently frozen `FsFltz.GeometricTarget` and its defining
dependencies. The target is separate from the solution's normal imports.

The [challenge](challenge/) contains the target and all 21 other project modules
in its import closure, together with its toolchain and dependency manifest.
[Challenge provenance](challenge-provenance.json) records the fixed revisions and
file hashes. The theorem placeholder in [Challenge.lean](challenge/Challenge.lean)
is checker infrastructure; it is not imported by the proof library. No fixed
definition or foundational proof is a solution hole.

[prepare.py](prepare.py) checks those hashes and stages the solution and challenge
without compiled artifacts. Challenge imports are relocated to `Trusted.FsFltz.*`;
mathematical declarations and proof bodies remain unchanged. Comparator compares
the target's reached defining declarations, including supporting proof bodies.
Both configurations permit only `propext`, `Classical.choice`, and `Quot.sound`,
with `definition_names: []`.

## Run on Linux

Use an unprivileged Linux account with Landlock support and a working user
systemd service manager. Install Lean/Elan, Python 3, Git, a C compiler,
Go (at least 1.24), and Rust/Cargo. From the package root:

```sh
verification/comparator/bootstrap-tools.sh /absolute/path/to/new-tools
scripts/verify-comparator.sh /absolute/path/to/new-run /absolute/path/to/new-tools --nanoda
```

Both output directories must initially be empty. The bootstrap script downloads
and builds the exact versions in [tool-revisions.json](tool-revisions.json).
It selects Lean 4.34.1 for Comparator without changing its Lean source. Nanoda
uses its committed Cargo lockfile. The runner verifies these tool revisions.
Omit `--nanoda` to run Comparator and Lean kernel replay alone.

The [sandbox preflight](sandbox-preflight.py) checks an allowed write, denial of
a protected write, and denial of AF_UNIX socket creation. Failure stops the run.
Comparator builds and exports through real Landrun under systemd's
`RestrictAddressFamilies=~AF_UNIX` restriction, using Mathlib's published cache.
It compares the target and dependencies, checks permitted axioms, and replays
the proof through Lean's kernel and optionally Nanoda.

The run directory contains the staged source inventory, environment details,
sandbox receipts, and checker output. Preserve these with the command's exit
status. A macOS sandbox substitute does not provide this verification.

See the package's [verification record](../README.md) for results and scope.
Formal target comparison does not establish correspondence with natural-language
mathematics or formalize the external GPS categorical deduction.
