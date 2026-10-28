#!/bin/bash
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
G=/Users/seyoonr/phd_experiments/tcslib; F=TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.lean
B=43fe918f2b7612b46d6b1bd6d4201651f7243430; H=e952bc50924ae7cea3364298087148fe1540a534
T=$(git -C $S/wt-hk rev-parse HEAD); M=$(git -C $G rev-parse c2887fb5)
echo "## the tip's Lean (records worktree, read $(date -u +%FT%TZ))"
echo "records tip $T: $(git -C $G log -1 --format=%s $T | cut -c1-120)"
echo "#174 merge $M"
echo ".lean files differing #174-merge..tip: $(git -C $G diff --name-only $M $T -- '*.lean' | wc -l)"
echo ".lean files differing base..#174-merge: $(git -C $G diff --name-only $B $M -- '*.lean' | tr '\n' ' ')"
echo "owned file at the tip: $(git -C $G rev-parse $T:$F) (base f965eac02e06549e8239c7476b31c0ced4f3d11b)"
echo "base an ancestor of the tip: $(git -C $G merge-base --is-ancestor $B $T && echo yes)"
echo "## the series at the tip (merge-tree of the tip and the head)"
git -C $G merge-tree --write-tree --name-only $T $H 2>&1 | head -5
echo "## snapshots"
echo "oleans-lnfapi4 NDHost.olean differs from oleans-lhh's: $(cmp -s $S/oleans-lnfapi4/TCSlib/Complexity/TuringMachine/Build/NDHost.olean $S/oleans-lhh/TCSlib/Complexity/TuringMachine/Build/NDHost.olean || echo yes)"
echo "oleans-lnfapi4 NTimeDiagonalizer.olean == oleans-lhh's: $(cmp -s $S/oleans-lnfapi4/TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.olean $S/oleans-lhh/TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.olean && echo yes || echo no)"
ls $S/oleans-lnfapi4 | head
