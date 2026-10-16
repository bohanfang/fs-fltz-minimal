#!/usr/bin/env python3
"""Fail closed unless systemd and real Landrun enforce required restrictions.

Run this program inside the same systemd RestrictAddressFamilies setting used
for Comparator. A successful child must both write inside its permitted area
and be denied a write to an otherwise writable protected area.
"""

import errno
import hashlib
import json
import os
from pathlib import Path
import socket
import subprocess
import sys


def main():
    if len(sys.argv) != 3:
        raise SystemExit("usage: sandbox-preflight.py LANDRUN STAGE")
    if sys.platform != "linux" or os.geteuid() == 0:
        raise SystemExit("preflight requires unprivileged Linux")
    landrun = Path(sys.argv[1]).resolve()
    stage = Path(sys.argv[2]).resolve()
    protected = stage / "sandbox-preflight"
    writable = stage / ".lake" / "sandbox-preflight"
    protected.mkdir(parents=True, exist_ok=True)
    writable.mkdir(parents=True, exist_ok=True)
    # Positive control: ordinary filesystem permissions allow this account to
    # write the protected area before Landrun applies its restrictions.
    control = protected / "outside-control.txt"
    control.write_text("parent can write here\n")
    denied = protected / "must-not-be-created.txt"
    if denied.exists():
        raise SystemExit("protected test output already exists; use a fresh probe area")
    try:
        sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    except OSError as error:
        if error.errno != errno.EAFNOSUPPORT:
            raise
        unix_errno = error.errno
    else:
        sock.close()
        raise SystemExit("AF_UNIX creation succeeded: systemd restriction is ineffective")
    child = r'''
import errno, json, pathlib, sys
writable, denied = map(pathlib.Path, sys.argv[1:])
(writable / "allowed.txt").write_text("sandbox child can write in its permitted area\n")
try:
    denied.write_text("sandbox failure\n")
except OSError as error:
    if error.errno not in (errno.EACCES, errno.EPERM):
        raise
    print(json.dumps({"child_ran": True, "allowed_write": True,
                      "protected_write_denied": True, "denial_errno": error.errno}))
else:
    raise SystemExit("Landrun permitted a protected write: sandbox is ineffective")
'''
    command = [str(landrun), "--best-effort", "--ro", "/", "--rw", "/dev",
               "-ldd", "-add-exec", "--rwx", str(writable), "--",
               sys.executable, "-c", child, str(writable), str(denied)]
    result = subprocess.run(command, capture_output=True, text=True)
    if result.returncode != 0:
        sys.stderr.write(result.stdout + result.stderr)
        raise SystemExit("Landrun preflight child failed; verification must not proceed")
    child_result = json.loads(result.stdout)
    if denied.exists() or not (writable / "allowed.txt").is_file():
        raise SystemExit("Landrun preflight filesystem receipts disagree")
    receipt = {
        "uid": os.geteuid(), "systemd_af_unix_denied": True,
        "systemd_af_unix_errno": unix_errno,
        "parent_can_write_protected_area": control.read_text() == "parent can write here\n",
        "landrun_sha256": hashlib.sha256(landrun.read_bytes()).hexdigest(),
        "landrun": child_result,
        "result": "PASS",
    }
    (stage / "sandbox-preflight.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
