#!/usr/bin/env bash
# All-ref search for gate 89 round 4's moved name: every declaration or use of
# `logSpace_le_size_succ` on every origin ref (name, object id), in TCSlib/**/*.lean.
# Usage: bash api_search.sh <repo worktree> <out file>
set -u
cd "$1" || exit 1
PAT='logSpace_le_size_succ'
refs=()
while IFS= read -r line; do refs+=("$line"); done < <(git for-each-ref --format='%(refname:short)' refs/remotes/origin | grep -vx origin)
{
  echo "# All-ref search ($(date -u +%F)) for \`$PAT\` (declarations and uses) on every origin ref, in TCSlib/**/*.lean."
  echo "# refs: ${#refs[@]}"
  for r in "${refs[@]}"; do
    h=$(git rev-parse "$r")
    hits=$(git grep -n -E "$PAT" "$r" -- 'TCSlib/*.lean' 2>/dev/null | sed "s|^$r:||" | tr '\n' ';')
    echo "$r $h: ${hits:-(none)}"
  done
} > "$2"
