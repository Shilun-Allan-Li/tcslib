#!/bin/bash
# Run tiles.py on the listed pairs (target file, target decl, source file, source decl), one per line of $2.
R=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/review/eq-cont1-fill
W=${2:-$R/wt-head}
while read -r a b c d; do
  [ -z "$a" ] && continue
  echo "### $b ($a) reproduces? $d ($c)"
  python3 -I $R/scripts/tiles.py "$W" "$a" "$b" "$c" "$d" 2>&1 | grep -v 'source body' | cut -c1-500
done < "$1"
