#!/bin/sh
set -eu
cd "$(dirname "$0")/paper"
for pass in 1 2; do
    pdflatex -interaction=nonstopmode -halt-on-error one_pitch_shifts.tex
done
