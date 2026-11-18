#!/usr/bin/env bash
# assemble.sh <mode: ckpt1|final> <out-dir>: build the delivery payload inbox/fills/ef-r23-regev/ under <out-dir>
set -eu
MODE=$1; OUT=$2/inbox/fills/ef-r23-regev; R=/home/user/ef-r23/repo; B=5ed465f62e4ae0f93ded1a1ba49e807591b589eb
if [ "$MODE" = ckpt1 ]; then H=daaf5e65f753100afc75d8180625c83b8f60e895; REP=/home/user/ef-r23/deliver/REPORT-ckpt1.md
else H=324c5de20c4b5fe1e0ee95a07612d3fa2ffd4b1a; REP=/home/user/ef-r23/deliver/REPORT-final.md; fi
rm -rf "${OUT:?}"; mkdir -p "$OUT/patches" "$OUT/src"
cp "$REP" "$OUT/REPORT.md"
git -C $R format-patch -q $B..$H -o "$OUT/patches"
{ printf 'hash\tauthor_name\tauthor_email\tauthor_date\tcommitter_name\tcommitter_email\tcommitter_date\tsigning\n'
  git -C $R log --reverse --format='%H%x09%an%x09%ae%x09%aI%x09%cn%x09%ce%x09%cI%x09none' $B..$H; } > "$OUT/patches/COMMITS.tsv"
for f in $(git -C $R diff --name-only $B $H); do mkdir -p "$OUT/src/$(dirname $f)"; git -C $R show $H:$f > "$OUT/src/$f"; done
python3 -I -c '
import shutil,sys
shutil.copytree(sys.argv[1], sys.argv[2], ignore=shutil.ignore_patterns("dev","seals-flat","seals-coe-flat","SHA256SUMS"))' /home/user/ef-r23/evidence "$OUT/evidence"
(cd "$OUT/evidence" && find . -type f | sed 's|^\./||' | LC_ALL=C sort | xargs -d '\n' sha256sum > ../.ev.sums && mv ../.ev.sums SHA256SUMS)
(cd "$OUT" && find . -type f | sed 's|^\./||' | LC_ALL=C sort | xargs -d '\n' sha256sum > ../.top.sums && mv ../.top.sums SHA256SUMS)
echo "assembled $MODE head $H: $(find "$OUT" -type f | wc -l) files, $(du -sh "$OUT" | cut -f1)"
