#!/usr/bin/env bash
# Supported release path: an unprivileged Linux user, real Landrun, systemd.
set -euo pipefail
if [[ $# -lt 2 || $# -gt 3 ]]; then
  echo "Usage: $0 EMPTY_WORK_DIRECTORY TOOL_DIRECTORY [--nanoda]" >&2
  exit 2
fi
if [[ $(uname -s) != Linux || $(id -u) == 0 ]]; then
  echo "Release Comparator verification requires an unprivileged Linux user." >&2
  exit 2
fi
command -v systemd-run >/dev/null
fsfltz_repo=$(cd "$(dirname "$0")/.." && pwd)
fsfltz_stage=$(python3 -c 'import os,sys; print(os.path.abspath(sys.argv[1]))' "$1")
fsfltz_tools=$(python3 -c 'import os,sys; print(os.path.abspath(sys.argv[1]))' "$2")
fsfltz_config=config.json
if [[ ${3:-} == --nanoda ]]; then
  fsfltz_config=config-nanoda.json
elif [[ $# == 3 ]]; then
  echo "Unknown option: $3" >&2
  exit 2
fi
export COMPARATOR_LANDRUN="$fsfltz_tools/landrun/landrun"
export COMPARATOR_LEAN4EXPORT="$fsfltz_tools/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export"
export COMPARATOR_NANODA="$fsfltz_tools/nanoda/target/release/nanoda_bin"
fsfltz_comparator="$fsfltz_tools/comparator/.lake/build/bin/comparator"
test -x "$COMPARATOR_LANDRUN"
test -x "$COMPARATOR_LEAN4EXPORT"
test -x "$fsfltz_comparator"
test "$(git -C "$fsfltz_tools/comparator" rev-parse HEAD)" = d03acab154d269c06e60e4de7e4cc85deebff94b
test "$(cat "$fsfltz_tools/comparator/lean-toolchain")" = leanprover/lean4:v4.34.1
test "$(git -C "$fsfltz_tools/comparator" diff --name-only HEAD)" = lean-toolchain
test "$(git -C "$fsfltz_tools/comparator/.lake/packages/lean4export" rev-parse HEAD)" = 076e8e57707e813375e8f9da8bf989799ace9680
git -C "$fsfltz_tools/comparator/.lake/packages/lean4export" diff --exit-code HEAD
test "$(git -C "$fsfltz_tools/landrun" rev-parse HEAD)" = 811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
git -C "$fsfltz_tools/landrun" diff --exit-code HEAD
if [[ $fsfltz_config == config-nanoda.json ]]; then
  test -x "$COMPARATOR_NANODA"
  test "$(git -C "$fsfltz_tools/nanoda" rev-parse HEAD)" = 3a2407216ee84a75f9e1aead6803d0578be06ae7
  git -C "$fsfltz_tools/nanoda" diff --exit-code HEAD
fi
python3 "$fsfltz_repo/verification/comparator/prepare.py" "$fsfltz_stage"
cd "$fsfltz_stage"
systemd-run --user --wait --pipe --collect \
  --property=RestrictAddressFamilies=~AF_UNIX \
  --working-directory="$fsfltz_stage" -E "PATH=$PATH" \
  -- python3 "$fsfltz_repo/verification/comparator/sandbox-preflight.py" \
  "$COMPARATOR_LANDRUN" "$fsfltz_stage" 2>&1 | tee sandbox-preflight.log
# Only trusted Mathlib dependency configuration is evaluated before sandboxing.
# No .lake content from the release checkout or original development is copied.
lake exe cache get
{
  date -u '+%Y-%m-%dT%H:%M:%SZ'
  uname -a
  lean --version
  "$COMPARATOR_LANDRUN" --version
  systemd-run --version
  git -C "$fsfltz_tools/comparator" diff -- lean-toolchain
  sha256sum "$fsfltz_comparator" "$COMPARATOR_LEAN4EXPORT" "$COMPARATOR_LANDRUN"
  if [[ $fsfltz_config == config-nanoda.json ]]; then
    sha256sum "$COMPARATOR_NANODA"
  fi
} > environment.txt
# The AF_UNIX restriction is required by the pinned upstream instructions.
# --wait and --pipe keep the full check's exit status and output available.
systemd-run --user --wait --pipe --collect \
  --property=RestrictAddressFamilies=~AF_UNIX \
  --working-directory="$fsfltz_stage" \
  -E "PATH=$PATH" -E "COMPARATOR_LANDRUN=$COMPARATOR_LANDRUN" \
  -E "COMPARATOR_LEAN4EXPORT=$COMPARATOR_LEAN4EXPORT" \
  -E "COMPARATOR_NANODA=$COMPARATOR_NANODA" \
  -- lake env "$fsfltz_comparator" "$fsfltz_config" 2>&1 | tee comparator.log
