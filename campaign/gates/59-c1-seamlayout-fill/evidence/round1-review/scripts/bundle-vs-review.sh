#!/bin/bash
# usage: W REV LISTFILE REVIEWDIR...
W=$1; REV=$2; LIST=$3; shift 3
for d in "$@"; do
  echo "== review dir $d at $REV"
  git -C $W ls-tree -r --name-only $REV -- $d > /private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/review/gates-59-61/scripts/.bvr_tree.$$ 2>/dev/null
  total=$(wc -l < /private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/review/gates-59-61/scripts/.bvr_tree.$$ | tr -d ' ')
  inlist=$(grep -c "^$d/" $LIST)
  echo "files in tree: $total; in bundle list: $inlist"
  echo "-- in tree but not in bundle list:"
  comm -23 <(sort /private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/review/gates-59-61/scripts/.bvr_tree.$$) <(grep "^$d/" $LIST | sort)
  rm -f /private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/review/gates-59-61/scripts/.bvr_tree.$$
done
