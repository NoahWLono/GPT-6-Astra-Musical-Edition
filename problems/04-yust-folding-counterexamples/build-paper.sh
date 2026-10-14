#!/usr/bin/env bash
set -euo pipefail
ROOT=$(cd "$(dirname "$0")" && pwd)
cd "$ROOT/paper"
# Requires a standard installed TeX Live setup with the source's packages.
for pass in 1 2; do
  pdflatex -interaction=nonstopmode -halt-on-error yust_folding_counterexamples.tex >"build-$pass.log" 2>&1
done
mkdir -p "$ROOT/output/pdf"
cp yust_folding_counterexamples.pdf "$ROOT/output/pdf/"
