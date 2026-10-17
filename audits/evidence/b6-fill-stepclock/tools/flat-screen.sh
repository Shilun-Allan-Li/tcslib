#!/usr/bin/env bash
# Run the committed copy-text screen (audits/evidence/retrofit/copy-text-screen.py, unchanged)
# on byte-identical copies of a population whose names encode the full repository path
# (`/` becomes `__`). The screen labels each file by its basename, so two files with the
# same basename (for example Build/Seam.lean and, after MIG-0b, Build/Contract/Seam.lean)
# would share a label: their same-named declarations are treated as one and the pair is
# dropped, and the output cannot say which file a pair is in. Flattened names remove both
# effects; the counts are otherwise the screen's own.
#
# Usage: bash flat-screen.sh <repo-root> <population.txt> <empty-scratch-dir> > <out.txt>
# Population lines starting with `#` are comments. Exits nonzero if a copy is not
# byte-identical or if the screen fails.
set -u
root=$1; pop=$2; flat=$3
mkdir -p "$flat" || exit 1
if [ -n "$(ls -A "$flat")" ]; then echo "scratch dir not empty: $flat" >&2; exit 1; fi
names=()
while read -r f; do
  case "$f" in ''|'#'*) continue ;; esac
  g=${f//\//__}
  cp "$root/$f" "$flat/$g" || exit 1
  cmp -s "$root/$f" "$flat/$g" || { echo "not byte-identical: $f" >&2; exit 1; }
  names+=("$g")
done < "$pop"
python3 -I "$root/audits/evidence/retrofit/copy-text-screen.py" "$flat" "${names[@]}"
