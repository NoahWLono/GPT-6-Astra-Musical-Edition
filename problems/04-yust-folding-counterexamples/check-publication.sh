#!/usr/bin/env bash
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
: "${MATHLIB_DIR:?Set MATHLIB_DIR to the pinned mathlib4 checkout; see REBUILD.md}"
if [[ -n "${LEAN_BIN:-}" ]]; then export PATH="$LEAN_BIN:$PATH"; fi
MATHLIB_DIR=$(cd "$MATHLIB_DIR" && pwd)
PIN=905b95818eb32af7874a58b427f50c1711a5e96c
[[ "$(git -C "$MATHLIB_DIR" rev-parse HEAD)" == "$PIN" ]] || { echo 'Wrong Mathlib revision' >&2; exit 1; }
cd "$MATHLIB_DIR"
[[ "$(lake env lean --version)" == *"version 4.32.2,"* ]] || { echo 'Lean 4.32.2 is required' >&2; exit 1; }
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT
# Compile the published source into a fresh temporary object; no project object is reused.
lake env lean -R "$HERE" -o "$OUT/Counterexamples.olean" "$HERE/formal/Counterexamples.lean"
