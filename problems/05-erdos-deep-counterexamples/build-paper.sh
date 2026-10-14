#!/usr/bin/env bash
set -euo pipefail
ROOT=$(cd "$(dirname "$0")" && pwd)
cd "$ROOT/paper"
# Requires a standard installed TeX Live setup with the source's packages.
for pass in 1 2; do
  pdflatex -interaction=nonstopmode -halt-on-error erdos_deep_counterexamples.tex >"build-$pass.log" 2>&1
done
