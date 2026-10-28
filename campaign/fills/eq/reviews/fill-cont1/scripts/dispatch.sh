#!/bin/bash
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
R=$S/review/eq-cont1-fill; WT=$S/wt-hk; G=/Users/seyoonr/phd_experiments/tcslib
B=43fe918f2b7612b46d6b1bd6d4201651f7243430; O=$G/exchange/outbox/fills/eq-fill-query-cont1.md
P=campaign/fills/eq/briefs/eq-fill-query-cont1.md; A=campaign/standards/fill-environment-addendum.md
echo "## dispatched brief"; shasum -a 256 "$O"
echo "## repo copy at the base, at the tip"; git -C $G show "${B}:${P}" | shasum -a 256; shasum -a 256 "$WT/$P"
echo "@ANCESTOR@ count in the base copy: $(git -C $G show "${B}:${P}" | grep -o '@ANCESTOR@' | wc -l)"
echo -n "base copy with @ANCESTOR@ := base, vs dispatched: "; git -C $G show "${B}:${P}" | sed "s/@ANCESTOR@/$B/g" | cmp - "$O" && echo "byte-equal"
echo -n "tip copy == base copy: "; git -C $G show "${B}:${P}" | cmp - "$WT/$P" && echo yes
echo "## addendum at the base and the tip"; git -C $G show "${B}:${A}" | shasum -a 256; shasum -a 256 "$WT/$A"
echo "## worker's inputs-check.log"; cat $R/delivery/fill-eq-query-cont1/logs/inputs-check.log
