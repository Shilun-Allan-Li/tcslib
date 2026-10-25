#!/usr/bin/env bash
# Grep each A1 name (word-bounded) in the tip and the three open PR heads (read-only git grep).
cd /Users/seyoonr/phd_experiments/tcslib || exit 1
REVS="5cade0b848a3bb6d87a2149aacecf4a2af923889 origin/lean/u2-api origin/lean/startup-kit origin/complexity/arora-barak-ch7"
for n in timeConstructible_iff spaceConstructible_iff computesInSpace_iff logSpace_eq transduce_nil transduce_cons transduce_of_copy; do
  for r in $REVS; do
    c=$(git grep -nw -e "$n" "$r" -- '*.lean' | wc -l | tr -d ' ')
    echo "$n @ $r: $c"
    git grep -nw -e "$n" "$r" -- '*.lean' | head -5
  done
done
