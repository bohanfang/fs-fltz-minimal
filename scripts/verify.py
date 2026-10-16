#!/usr/bin/env python3
"""Run the ordinary release checks and retain exact source/command evidence."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent


def output(*command):
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    return result.stdout.strip() if result.returncode == 0 else None


def snapshot():
    files = [ROOT / p for p in ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "FsFltz.lean")]
    files += sorted((ROOT / "FsFltz").rglob("*.lean"))
    files += sorted((ROOT / "checks").rglob("*.lean"))
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}


def dependencies():
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    records = []
    for package in manifest["packages"]:
        path = ROOT / manifest["packagesDir"] / package["name"]
        actual = output("git", "-C", str(path), "rev-parse", "HEAD")
        dirty = output("git", "-C", str(path), "status", "--porcelain", "--untracked-files=no")
        records.append({"name": package["name"], "expected_revision": package["rev"],
                        "actual_revision": actual, "tracked_changes": dirty,
                        "matches": actual == package["rev"] and dirty == ""})
    return records


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / ".verification")
    args = parser.parse_args()
    dest = args.output.resolve()
    dest.mkdir(parents=True, exist_ok=True)
    before = snapshot()
    record = {
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "git_revision": output("git", "rev-parse", "HEAD"),
        "git_status_before": output("git", "status", "--porcelain"),
        "platform": platform.platform(),
        "lean_version": output("lake", "env", "lean", "--version"),
        "lake_version": output("lake", "--version"),
        "source_sha256": before,
        "commands": [],
    }
    commands = [
        ("build", ["lake", "build"]),
        ("axiom-audit", ["lake", "env", "lean", "checks/AxiomAudit.lean"]),
        ("target-check", ["lake", "env", "lean", "checks/TargetCheck.lean"]),
    ]
    failed = False
    for label, command in commands:
        print("+ " + " ".join(command), flush=True)
        start = time.monotonic()
        with (dest / (label + ".log")).open("w") as log:
            process = subprocess.Popen(command, cwd=ROOT, stdout=subprocess.PIPE,
                                       stderr=subprocess.STDOUT, text=True)
            for line in process.stdout:
                sys.stdout.write(line)
                log.write(line)
            code = process.wait()
        record["commands"].append({"command": command, "exit_code": code,
                                    "elapsed_seconds": round(time.monotonic() - start, 3),
                                    "log": label + ".log",
                                    "log_sha256": hashlib.sha256((dest / (label + ".log")).read_bytes()).hexdigest()})
        if code:
            failed = True
            break
    record["source_unchanged"] = before == snapshot()
    record["dependencies"] = dependencies()
    record["dependencies_match_manifest"] = all(d["matches"] for d in record["dependencies"])
    record["completed_utc"] = datetime.now(timezone.utc).isoformat()
    record["passed"] = not failed and record["source_unchanged"] and record["dependencies_match_manifest"]
    (dest / "result.json").write_text(json.dumps(record, indent=2) + "\n")
    return 0 if record["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
