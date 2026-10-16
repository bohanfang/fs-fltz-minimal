#!/usr/bin/env bash
set -euo pipefail
if [[ $# -ne 1 ]]; then
  echo "Usage: $0 NEW_TOOL_DIRECTORY (requires git, lake, go, cargo, C compiler)" >&2
  exit 2
fi
fsfltz_tools=$(python3 -c 'import os,sys; print(os.path.abspath(sys.argv[1]))' "$1")
mkdir -p "$fsfltz_tools"
if [[ -n $(ls -A "$fsfltz_tools") ]]; then
  echo "Tool directory must be empty." >&2
  exit 2
fi
git clone https://github.com/leanprover/comparator "$fsfltz_tools/comparator"
git -C "$fsfltz_tools/comparator" checkout --detach d03acab154d269c06e60e4de7e4cc85deebff94b
printf '%s\n' leanprover/lean4:v4.34.1 > "$fsfltz_tools/comparator/lean-toolchain"
(
  cd "$fsfltz_tools/comparator"
  lake build lean4export comparator
  test "$(git -C .lake/packages/lean4export rev-parse HEAD)" = 076e8e57707e813375e8f9da8bf989799ace9680
)
git clone https://github.com/Zouuup/landrun "$fsfltz_tools/landrun"
git -C "$fsfltz_tools/landrun" checkout --detach 811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
(
  cd "$fsfltz_tools/landrun"
  go build -mod=readonly -o landrun ./cmd/landrun
)
git clone https://github.com/ammkrn/nanoda_lib "$fsfltz_tools/nanoda"
git -C "$fsfltz_tools/nanoda" checkout --detach 3a2407216ee84a75f9e1aead6803d0578be06ae7
(
  cd "$fsfltz_tools/nanoda"
  cargo build --release --locked
)
{
  uname -a
  lake --version
  lean --version
  go version
  cargo --version
  rustc --version
} > "$fsfltz_tools/build-environment.txt"
echo "Built pinned tools in $fsfltz_tools"
