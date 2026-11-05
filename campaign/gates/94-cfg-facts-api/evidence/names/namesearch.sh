#!/bin/bash
# namesearch.sh <name>...: every ref whose TCSlib Lean files mention each name as a word
G=/Users/seyoonr/phd_experiments/tcslib
refs=()
while read -r r; do refs+=("$r"); done < <(git -C $G for-each-ref --format='%(refname)' refs/remotes/origin refs/heads refs/deliv | grep -v HEAD)
echo "${#refs[@]} refs"
for n in "$@"; do
  hits=()
  for r in "${refs[@]}"; do
    while read -r h; do [ -n "$h" ] && hits+=("${h#*:}"); done < <(git -C $G grep -l -w "$n" "$r" -- 'TCSlib/*.lean' 2>/dev/null)
  done
  echo "== $n: ${#hits[@]} ref-file hits"
  printf '%s\n' "${hits[@]}" | grep . | sort | uniq -c
done
