#!/bin/bash
# Grep every local and remote ref's TCSlib tree for an nf_/Nf declaration name or an nf_ identifier after whitespace, a bracket, a comma or a dot (outside NDNormalForm) and the
# rule-11 names in the delivery's added lines.  usage: refgrep.sh <head.lean> <base.lean>
G=/Users/seyoonr/phd_experiments/tcslib
refs=$(git -C $G for-each-ref --format='%(refname)' refs/heads refs/remotes refs/deliv refs/pull 2>/dev/null)
n=0; hits=0
for r in $refs; do
  n=$((n+1))
  out=$(git -C $G grep -l -E '(theorem|def|abbrev|lemma|instance|structure|inductive|class)[[:space:]]+(nf_|Nf[A-Z])|[[:space:](\[,.]nf_[a-z]' "$r" -- 'TCSlib/*.lean' 2>/dev/null | grep -v 'NDNormalForm.lean')
  if [ -n "$out" ]; then hits=$((hits+1)); echo "HIT $r: $out"; fi
done
echo "refs searched: $n; refs with an nf_/Nf name outside NDNormalForm: $hits"
echo "## rule 11: added lines naming an R3 row or a named foreign private family"
diff <(cat "$2") <(cat "$1") | grep '^>' | grep -nE 'copyTM_run\b|transferTM_run\b|clearTM_run\b|compareTM_run\b|incrementTM_run_succ|incrementTM_run_overflow|xr_|gr_[a-z]|wr_[a-z]|choiceCore|recordStep_runFrom_one|zr_' || echo "none"
