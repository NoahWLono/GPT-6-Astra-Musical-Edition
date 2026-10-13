#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p qa/texmf-var qa/texmf-config
export TEXMF="{/usr/share/texmf,/usr/share/texlive/texmf-dist}"
export TEXMFVAR="$PWD/qa/texmf-var"
export TEXMFCONFIG="$PWD/qa/texmf-config"
export TEXFORMATS="$PWD/qa//:"
export TEXFONTMAPS="$PWD/qa//:/usr/share/texmf/fonts/map//:/usr/share/texlive/texmf-dist/fonts/map//:"
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
  (cd qa && pdftex -etex -ini -interaction=nonstopmode -halt-on-error -jobname=pdflatex -progname=pdflatex pdflatex.ini > format.log 2>&1)
fi
if [[ ! -f qa/pdftex.map ]]; then
  cat /usr/share/texmf/fonts/map/dvips/lm/lm.map /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/*.map > qa/pdftex.map
fi
for pass in 1 2; do
  pdflatex -interaction=nonstopmode -halt-on-error omnibus_bounds.tex > "qa/build-${pass}.log" 2>&1
done
pdfinfo omnibus_bounds.pdf > qa/pdfinfo.txt
pdftotext -layout omnibus_bounds.pdf qa/extracted.txt
pdftoppm -r 100 -png omnibus_bounds.pdf qa/page > qa/render.log 2>&1
