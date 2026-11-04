#!/usr/bin/env bash
# All-ref search for declarations of the codec edge-mode PR's new public names, on every origin
# ref (name, object id), in TCSlib/**/*.lean.
# Usage: bash api_copy_search.sh <repo worktree> <out file>
set -u
cd "$1" || exit 1
NAMES='CA_acc|CA_eFar|CA_eK|CA_eNext|CA_eRd1|CA_eRd2|CA_eStart_of_pos|CA_eStart_of_zero|CA_eTest|CA_rej|CA_vDone_edge|EdgeChk|Shape1\.eq|Shape1\.width|W_eq|cellOf_head|cpDst_Qe|cpDst_Te|cpDst_Ue|cpNext_Qe|cpNext_Te|cpNext_Ue|cpSrc_Qe|cpSrc_Te|cpSrc_Ue|edgeChk_def|edgeChk_iff|edgeLang|edgeLang_iff|edgeLang_mem|edge_loop|edge_round|edge_tail|getD_cfgWord_head|goto_eq|icCount_Eh|icCount_Ke|icCount_S1|icCount_S2|icNext_Eh|icNext_Ke|icNext_S1|icNext_S2|icReg_Eh|icReg_Ke|icReg_S1|icReg_S2|mem_edgeLang|mem_edgeLang_iff|orc_eq|scDst_Ee|scFactor_Ee|scNext_Ee|scSrc_Ee'
PAT="^(@\[[^]]*\] *)?((private|protected|noncomputable) +)*(theorem|lemma|def|abbrev|structure|inductive) +(Complexity\.Codec\.|Codec\.)?(${NAMES})( |$|:)"
refs=()
while IFS= read -r line; do refs+=("$line"); done < <(git for-each-ref --format='%(refname:short)' refs/remotes/origin | grep -vx origin)
{
  echo "# All-ref search ($(date -u +%F)) for declarations of the edge-mode PR's new public names, on every origin ref (name, object id), in TCSlib/**/*.lean."
  echo "# Pattern: $PAT"
  echo "# refs: ${#refs[@]}"
  for r in "${refs[@]}"; do
    h=$(git rev-parse "$r")
    hits=$(git grep -n -E "$PAT" "$r" -- 'TCSlib/*.lean' 2>/dev/null | sed "s|^$r:||" | tr '\n' ';')
    echo "$r $h: ${hits:-(none)}"
  done
} > "$2"
