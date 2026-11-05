#!/usr/bin/env bash
# All-ref search for gate 89 round 5's moved, removed and new names: declarations and uses of
# two_pow_bits_le (moved Codec → LogProg), wP_le in TQBFHard (removed) and wP_eq (new), on every
# origin ref, in TCSlib/**/*.lean.
# Usage: bash api_search.sh <repo worktree> <out file>
set -u
cd "$1" || exit 1
PAT='(^|[^_[:alnum:]])(two_pow_bits_le|wP_eq|TQBFHard\.wP_le)([^_[:alnum:]]|$)'
refs=()
while IFS= read -r line; do refs+=("$line"); done < <(git for-each-ref --format='%(refname:short)' refs/remotes/origin | grep -vx origin)
{
  echo "# All-ref search ($(date -u +%F)): $PAT, on every origin ref, in TCSlib/**/*.lean."
  echo "# refs: ${#refs[@]}"
  for r in "${refs[@]}"; do
    h=$(git rev-parse "$r")
    hits=$(git grep -n -E "$PAT" "$r" -- 'TCSlib/*.lean' 2>/dev/null | sed "s|^$r:||" | tr '\n' ';')
    echo "$r $h: ${hits:-(none)}"
  done
} > "$2"
