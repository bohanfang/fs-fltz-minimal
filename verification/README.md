# Verification

| Check | Result |
| --- | --- |
| Lean build | Passed |
| Project axiom audit | Passed; only `propext`, `Classical.choice`, and `Quot.sound` |
| Exact-target check | Passed; theorem type and 32 selected proof-body dependency paths |
| Comparator against the frozen target | Passed for the identical source/configuration payload |
| Lean kernel replay and Nanoda | Accepted that same proof payload |

The ordinary Lean checks ran on this package with unchanged sources and all
nine dependencies at their pinned revisions. The project was compiled afresh,
using Mathlib's published dependency cache.

The Comparator and additional-kernel results cover the identical mathematical
sources and checker configuration: all 896 staged source and configuration files,
including the independently preserved challenge, match the verified payload
byte for byte.

## Reproduce

From the package root:

```sh
lake exe cache get
scripts/verify.sh
```

The script runs the Lean build, project axiom audit, and exact-target check.
It records commands, exit statuses, source hashes, tool versions, and installed
dependency revisions in `.verification/`. Use `--output PATH` to select another
output directory. Lean is pinned by [lean-toolchain](../lean-toolchain); exact
dependency revisions are in [lake-manifest.json](../lake-manifest.json).

[Comparator reproduction](comparator/README.md) requires its supported Linux
sandbox. The independent target, fixed definitions, allowed axioms, and pinned
tool configuration are included in this package.

## Scope

These checks establish formal acceptance, permitted axioms, and preservation of
the formal target. The general GPS categorical deduction remains external.
