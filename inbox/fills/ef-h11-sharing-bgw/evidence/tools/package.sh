#!/usr/bin/env bash
# package.sh <head> <outdir> <evidence-src-dir> <REPORT.md>
set -euo pipefail
BASE=5ed465f62e4ae0f93ded1a1ba49e807591b589eb
HEAD=$1; OUT=$2; EVSRC=$3; REP=$4
REPO=/home/user/work/ef-h11
rm -rf "$OUT"; mkdir -p "$OUT/patches" "$OUT/src" "$OUT/evidence"
cd "$REPO"
git format-patch -q -o "$OUT/patches" $BASE..$HEAD
printf 'hash\tauthor_name\tauthor_email\tauthor_date\tcommitter_name\tcommitter_email\tcommitter_date\tsigning\n' > "$OUT/patches/COMMITS.tsv"
for c in $(git rev-list --reverse $BASE..$HEAD); do
  sig=$(git cat-file -p $c | grep -c gpgsig || true)
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$c" "$(git log -1 --format=%an $c)" "$(git log -1 --format=%ae $c)" "$(git log -1 --format=%aI $c)" "$(git log -1 --format=%cn $c)" "$(git log -1 --format=%ce $c)" "$(git log -1 --format=%cI $c)" "$([ "$sig" = 0 ] && echo unsigned || echo signed)" >> "$OUT/patches/COMMITS.tsv"
done
for f in $(git diff --name-only $BASE $HEAD); do mkdir -p "$OUT/src/$(dirname $f)"; git show $HEAD:$f > "$OUT/src/$f"; done
cp -r "$EVSRC"/. "$OUT/evidence/"
(cd "$OUT/evidence" && find . -type f ! -name SHA256SUMS | sed 's|^\./||' | sort | xargs sha256sum > SHA256SUMS)
cp "$REP" "$OUT/REPORT.md"
(cd "$OUT" && find . -type f ! -name SHA256SUMS -o -path ./evidence/SHA256SUMS -type f | sed 's|^\./||' | sort | xargs sha256sum > SHA256SUMS)
echo packaged $(find "$OUT" -type f | wc -l) files
