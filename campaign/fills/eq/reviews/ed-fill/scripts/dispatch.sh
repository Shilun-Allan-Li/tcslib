#!/usr/bin/env bash
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad; R=$S/review/ed-fill; G=/Users/seyoonr/phd_experiments/tcslib
B=$(git -C $G rev-parse refs/deliv/eq-diagonalizer~11)
f=$(find $G/exchange -name 'eq-fill-diagonalizer.md' | head -1)
echo "== dispatch copy: $f"; shasum -a 256 "$f"
git -C $G show "${B}:campaign/fills/eq/briefs/eq-fill-diagonalizer.md" > $R/out/aux-brief-base.md
echo "== base copy's @ANCESTOR@ occurrences: $(grep -c '@ANCESTOR@' $R/out/aux-brief-base.md)"
sed "s/@ANCESTOR@/$B/g" $R/out/aux-brief-base.md | diff - "$f" > /dev/null && echo "dispatch = base copy with @ANCESTOR@ := base" || { echo "dispatch differs from the filled base copy:"; sed "s/@ANCESTOR@/$B/g" $R/out/aux-brief-base.md | diff - "$f" | head -20; }
echo "== record copy (wt-hk) vs base copy"; diff $R/out/aux-brief-base.md $S/wt-hk/campaign/fills/eq/briefs/eq-fill-diagonalizer.md > /dev/null && echo same || diff $R/out/aux-brief-base.md $S/wt-hk/campaign/fills/eq/briefs/eq-fill-diagonalizer.md | head -20
