#!/usr/bin/env bash
# All-ref search for declarations of the ARM embedding API PR's new public names.
# Usage: bash api_copy_search.sh <repo worktree> <out file>
set -u
cd "$1" || exit 1
NAMES='callSegs_congr|arun_zero|astep_inc|astep_dec|astep_clr|astep_half|astep_jz|astep_jodd|astep_jeq|astep_call|astep_ret|astep_valP|astep_valQ|astep_jeqIn|astep_jeqFst|astep_jeqSnd|embed|RegExt|update|preS_of_ins|preS_embed|astep_embed|embed_guardLe|A_noVal'
PAT="^(@\[[^]]*\] *)?((private|protected|noncomputable) +)*(theorem|lemma|def|abbrev|structure) +(Complexity\.LogProg\.|LogProg\.|SavitchARM\.|Ins\.|AHalt\.|RegExt\.)*(${NAMES})( |\$|:)"
refs=()
while IFS= read -r line; do refs+=("$line"); done < <(git for-each-ref --format='%(refname:short)' refs/remotes/origin | grep -vx origin)
{
  echo "# All-ref search ($(date -u +%F)) for declarations of the API PR's new public names, on every origin ref (name, object id), in TCSlib/**/*.lean."
  echo "# Pattern: $PAT"
  echo "# refs: ${#refs[@]}"
  for r in "${refs[@]}"; do
    h=$(git rev-parse "$r")
    hits=$(git grep -n -E "$PAT" "$r" -- 'TCSlib/*.lean' 2>/dev/null | sed "s|^$r:||" | tr '\n' ';')
    echo "$r $h: ${hits:-(none)}"
  done
} > "$2"
