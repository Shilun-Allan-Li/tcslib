#!/usr/bin/env bash
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad; R=$S/review/ed-fill; G=/Users/seyoonr/phd_experiments/tcslib
B=$(git -C $G rev-parse refs/deliv/eq-diagonalizer~11)
for ref in complexity/arora-barak-ch3-4 origin/complexity/arora-barak-ch3-4; do
  T=$(git -C $G rev-parse $ref 2>/dev/null) || continue
  echo "== $ref = $T"
  echo "   base is ancestor: $(git -C $G merge-base --is-ancestor $B $T && echo yes || echo no)"
  echo "   .lean files changed base..$ref:"; git -C $G diff --name-only $B $T -- '*.lean' | sed 's/^/     /'
  echo "   owned file at $ref: $(git -C $G rev-parse $T:TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.lean)"
  echo "   merge-tree with the delivery head:"; git -C $G merge-tree --write-tree $T refs/deliv/eq-diagonalizer >/dev/null 2>&1 && echo "     clean" || echo "     CONFLICT"
done
