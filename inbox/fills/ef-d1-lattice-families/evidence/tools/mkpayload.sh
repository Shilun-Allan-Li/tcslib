#!/usr/bin/env bash
# mkpayload.sh <outdir> <evidence-subset-dir...>: build the COMMON.md §7 payload for fill/ef-d1-lattice-families
set -eu
REPO=/home/user/work/ef-d1; BASE=5ed465f62e4ae0f93ded1a1ba49e807591b589eb
OUT="$1"; shift
[ -n "$OUT" ] && [ ! -e "$OUT" ] || { echo "outdir exists"; exit 2; }; mkdir -p "$OUT/patches" "$OUT/src" "$OUT/evidence"
cd "$REPO"
git format-patch -q -o "$OUT/patches" $BASE..fill/ef-d1-lattice-families
{ printf 'hash\tauthor_name\tauthor_email\tauthor_date\tcommitter_name\tcommitter_email\tcommitter_date\tsigning\n'
  git log --reverse --format='%H%x09%an%x09%ae%x09%aI%x09%cn%x09%ce%x09%cI%x09%G?' $BASE..fill/ef-d1-lattice-families; } > "$OUT/patches/COMMITS.tsv"
for f in $(git diff --name-only $BASE fill/ef-d1-lattice-families); do
  mkdir -p "$OUT/src/$(dirname $f)"; git show fill/ef-d1-lattice-families:$f > "$OUT/src/$f"; done
for d in "$@"; do cp -r "$d" "$OUT/evidence/"; done
cd "$OUT/evidence" && find . -type f ! -name SHA256SUMS | sed 's|^\./||' | sort | xargs sha256sum > SHA256SUMS
cd "$OUT" && find . -type f ! -name SHA256SUMS -o -path ./evidence/SHA256SUMS -type f | sed 's|^\./||' | sort | xargs sha256sum > SHA256SUMS
echo "payload at $OUT: $(find "$OUT" -type f | wc -l) files"
