# FS–FLTZ geometric comparison

This Lean project is a by-product of an ongoing joint mathematical project with Mingyuan Hu, Yuze Sun, and Peng Zhou.

We present and verify in Lean a Liouville-geometric equivalence theorem that could imply an equivalence between the Fukaya–Seidel category (in the sense of Giroux–Pardon and Ganatra–Pardon–Shende) of a Givental–Hori–Vafa mirror of a smooth toric Fano variety and the partially wrapped Fukaya category of the cotangent bundle of a real torus, stopped at the FLTZ skeleton. These geometric and categorical equivalences are due to [Gammage–Shende](https://doi.org/10.4310/ACTA.2022.v229.n2.a2) and [Zhou](https://doi.org/10.1007/s00029-020-00555-9). We restrict our formalization to Liouville geometry because the higher categorical and Floer-theoretic aspects of symplectic geometry are still far from being formalized in Lean.

Lean development of the geometric superpotential–FLTZ comparison.

- [Target theorem](target-theorem.pdf): geometric definitions, the target, and
  its quantifier order.
- [FS–FLTZ target with categorical statement](fsf-target-with-categories.pdf):
  the complete specification and categorical consequence using the general GPS
  results.
- [Proof blueprint](proof-blueprint.pdf): the detailed mathematical blueprint.

The Lean statement is [`FsFltz.GeometricTarget`](FsFltz/Target.lean), proved by
[`FsFltz.geometricTarget`](FsFltz/Geometry/GeometricComparisonAssembly.lean).
It includes the full far-fiber markings, prescribed quantifiers, literal
endpoint full-core equality, and prescribed grading on the same finite
comparison chain. The GPS categorical deduction remains external to Lean.

With Elan/Lean, Git, and Python 3 installed, run from this folder:

```sh
lake exe cache get
scripts/verify.sh
```

The toolchain and all dependencies are pinned. The first command obtains
Mathlib's published dependency cache. See the [verification record](verification/README.md)
for results and [Comparator instructions](verification/comparator/README.md)
for the independent target comparison.

[Apache-2.0](LICENSE). Existing notices and third-party attribution are retained.
