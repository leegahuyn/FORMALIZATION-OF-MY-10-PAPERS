#!/bin/bash
# usage: test_frag.sh path/to/frag.tex   -> compiles frag against common preamble in a temp dir
set -e
F=$(readlink -f "$1"); D=$(mktemp -d); P=$(dirname "$(readlink -f "$0")")/preamble.tex
{ cat "$P"; echo '\begin{document}'; echo "\\input{$F}"; echo '\end{document}'; } > $D/t.tex
cd $D; for i in 1 2; do xelatex -interaction=nonstopmode -halt-on-error t.tex > log.txt 2>&1 || { tail -40 log.txt; echo "COMPILE FAILED"; exit 1; }; done
grep -E "Missing character|undefined|Undefined" t.log | head -20 || true
echo "COMPILE OK: $(pdfinfo t.pdf 2>/dev/null | grep Pages)"; rm -rf $D
