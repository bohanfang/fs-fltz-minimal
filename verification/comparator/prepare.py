#!/usr/bin/env python3
"""Stage independent challenge and release sources; never import candidate target.

Only FsFltz import paths in baseline files are prefixed with Trusted. Mathematical
declarations and proofs are unchanged. The original baseline bytes remain under
challenge/. Comparator itself decides whether elaborated defining constants match.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess


def digest(data):
    return hashlib.sha256(data).hexdigest()


def relocate_imports(data):
    # All baseline imports are one module per line. Reject unfamiliar syntax
    # instead of silently skipping an import into the candidate environment.
    text = data.decode("utf-8")
    result = []
    for line in text.splitlines(keepends=True):
        if re.match(r"^(?:public )?import\s", line):
            match = re.fullmatch(r"(import )([A-Za-z0-9_.]+)(\s*)", line)
            if match is None:
                raise ValueError("Unsupported baseline import: " + repr(line))
            prefix, module, ending = match.groups()
            if module == "FsFltz" or module.startswith("FsFltz."):
                line = prefix + "Trusted." + module + ending
        result.append(line)
    return "".join(result).encode("utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("destination", type=Path, help="new, empty staging directory")
    args = parser.parse_args()
    infrastructure = Path(__file__).resolve().parent
    repository = infrastructure.parent.parent
    destination = args.destination.resolve()
    if destination.exists() and any(destination.iterdir()):
        parser.error("destination must be empty; existing builds are never reused")
    provenance = json.loads((infrastructure / "challenge-provenance.json").read_text())
    baseline = infrastructure / "challenge"
    for item in provenance["files"]:
        path = baseline / item["challenge"]
        if digest(path.read_bytes()) != item["sha256"]:
            raise ValueError("Trusted snapshot hash mismatch: " + str(path))
    for item in provenance["added_scaffolding"]:
        path = baseline / item["challenge"]
        if digest(path.read_bytes()) != item["sha256"]:
            raise ValueError("Trusted scaffolding hash mismatch: " + str(path))
    for name in ["lean-toolchain", "lake-manifest.json"]:
        if (repository / name).read_bytes() != (baseline / name).read_bytes():
            raise ValueError("Candidate changed a fixed dependency input: " + name)
    destination.mkdir(parents=True, exist_ok=True)
    for name in ["FsFltz", "FsFltz.lean", "lean-toolchain", "lake-manifest.json"]:
        source = repository / name
        if source.is_dir():
            shutil.copytree(source, destination / name)
        else:
            shutil.copyfile(source, destination / name)
    # Use the separately hashed, release-authored verification configuration;
    # it preserves the baseline dependency pin and adds the Challenge library.
    # Do not execute a candidate build hook while preparing the challenge.
    lakefile = (baseline / "lakefile.toml").read_text()
    lakefile += '\n[[lean_lib]]\nname = "Trusted"\n'
    (destination / "lakefile.toml").write_text(lakefile)
    transformed = []
    for source in sorted((baseline / "FsFltz").rglob("*.lean")):
        relative = source.relative_to(baseline)
        target = destination / "Trusted" / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        data = relocate_imports(source.read_bytes())
        target.write_bytes(data)
        transformed.append({"baseline": str(relative), "staged": str(target.relative_to(destination)),
                            "baseline_sha256": digest(source.read_bytes()), "staged_sha256": digest(data)})
    (destination / "Challenge.lean").write_bytes(relocate_imports((baseline / "Challenge.lean").read_bytes()))
    for name in ["config.json", "config-nanoda.json"]:
        shutil.copyfile(infrastructure / name, destination / name)
    inventory = [{"path": str(p.relative_to(destination)), "sha256": digest(p.read_bytes())}
                 for p in sorted(destination.rglob("*")) if p.is_file()]
    revision = subprocess.run(["git", "-C", str(repository), "rev-parse", "HEAD"],
                              text=True, capture_output=True)
    record = {"baseline_revision": provenance["source_revision"],
              "candidate_revision": revision.stdout.strip() if revision.returncode == 0 else None,
              "candidate_identity": "Exact staged source inventory below; excludes compiled artifacts.",
              "import_relocation": transformed, "files": inventory}
    (destination / "preparation.json").write_text(json.dumps(record, indent=2) + "\n")
    print("Prepared", destination)
    print("Trusted project modules:", len(transformed))
    print("Candidate Lean source files:", len(list((destination / "FsFltz").rglob("*.lean"))))


if __name__ == "__main__":
    main()
