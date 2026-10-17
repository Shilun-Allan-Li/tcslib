#!/bin/zsh
# Round-2 evidence runner for the ARM extensions fill gate (read-only analysis; no Lean, no git
# writes). Regenerates every round-2 table and log from:
#   - the read-only checkout $W (Lean tree identical at 39bfdca4 and at the tip e831b5b0),
#   - round 1's builder directory $G (screen copies at the received tree, labels, screen output,
#     disclosure table, import order, round-1 ledger script),
# and writes only under $R (work/, logs/, evidence/).
# usage: zsh run_r2.zsh <S>     (S = the session scratchpad)
set -euo pipefail
S=$1
W=$S/wt-armr2; G=$S/gate-arm; R=$S/gate-arm-r2
SC=$R/scripts; WK=$R/work; LG=$R/logs; EV=$R/evidence
mkdir -p $WK $LG $EV
py() { python3 -I "$@" }
TIP_CHECKOUT=$(git -C $W rev-parse HEAD)
TIP=$(git -C $W rev-parse e831b5b0^{commit})
RECV=$(git -C $W rev-parse 8c23f3bc^{commit})
BASE=$(git -C $W rev-parse 069cde82^{commit})
DC=$(git -C $W rev-parse dc891632^{commit})
RX=$(git -C $W rev-parse 733c22b7^{commit})
PR87M=$(git -C $W rev-parse 4d149798^{commit})
PR87P=$(git -C $W rev-parse 4d149798^1)
for h in $TIP_CHECKOUT $TIP $RECV $BASE $DC $RX $PR87M $PR87P; do git -C $W cat-file -e $h; done
# ---- 0. inputs ----
need=($G/work/screen-combined.out $G/evidence/screen-population-labels.txt $G/work/added.txt
      $G/work/screen-root $G/evidence/disclosed-copies.tsv $G/work/root-up.txt $G/work/screen-new.out
      $G/scripts/ledger.py $G/work/ledger-full.out $WK/kfam.tsv $WK/manual-spec.tsv
      $W/audits/evidence/retrofit/copy-text-screen.py)
for f in $need; do [[ -e $f ]] || { echo "missing input $f" >&2; exit 2 }; done
{
  echo "# arm-fill-r2-provenance: commits (resolved with git rev-parse, checked with cat-file -e)"
  echo "checkout HEAD           $TIP_CHECKOUT"
  echo "campaign tip            $TIP"
  echo "received commit         $RECV  (parents: $(git -C $W log -1 --format=%P $RECV))"
  echo "supplied baseline       $BASE"
  echo "round-1 pack tip        $DC"
  echo "replay/probe revision   $RX  (parents: $(git -C $W log -1 --format=%P $RX))"
  echo "PR #87 merge            $PR87M  (first parent $PR87P)"
  echo
  if git -C $W diff --quiet $TIP_CHECKOUT $TIP -- '*.lean'; then echo "Lean tree: identical at the checkout HEAD and the tip"; else echo "Lean tree: DIFFERS between checkout HEAD and tip"; exit 3; fi
  echo "non-Lean paths changed checkout HEAD..tip: $(git -C $W diff --name-only $TIP_CHECKOUT $TIP | tr '\n' ' ')"
  git -C $W diff --name-only $BASE $RECV -- '*.lean' > $WK/changed81.txt
  echo "received .lean paths (069cde82..8c23f3bc): $(wc -l < $WK/changed81.txt | tr -d ' ')"
  if git -C $W diff --quiet $RECV $TIP -- $(cat $WK/changed81.txt); then echo "the 81 received .lean files: byte-identical at the received commit and at the tip"; else echo "the 81 received files CHANGED"; exit 3; fi
  if git -C $W diff --quiet $RECV $RX -- $(cat $WK/changed81.txt); then echo "the 81 received .lean files: byte-identical at the replay revision 733c22b7"; else echo "81 differ at replay revision"; exit 3; fi
  echo; echo "round-1 input digests (SHA-256):"
  for f in $G/work/screen-combined.out $G/evidence/screen-population-labels.txt $G/work/added.txt $G/evidence/disclosed-copies.tsv $G/work/root-up.txt $G/work/screen-new.out $G/scripts/ledger.py; do echo "  $(shasum -a 256 $f | cut -d' ' -f1)  ${f#$S/}"; done
  echo "combined screen input: $(py $SC/combcheck.py $G/work/screen-full.out $G/work/screen-supp.out $G/work/screen-combined.out $G/evidence/screen-supplement-population.txt $G/evidence/screen-population.txt)"
  echo "this round's hand inputs:"
  for f in $WK/kfam.tsv $WK/manual-spec.tsv; do echo "  $(shasum -a 256 $f | cut -d' ' -f1)  ${f#$S/}"; done
} > $LG/arm-fill-r2-provenance.log
# ---- 1. population drift and line positions at the tip ----
{
  echo "# arm-fill-r2-drift: the round-1 screen population (214 labelled files) at the received tree vs the tip"
  py $SC/popdrift.py $G/evidence/screen-population-labels.txt $G/work/screen-root $W
  echo; echo "# library side of every library pair: span at the received tree vs the tip (ledger.py span rules)"
  py $SC/tipspans.py $WK/pairs.tsv $G/evidence/screen-population-labels.txt $G/work/screen-root $W 2>/dev/null || true
} > $LG/arm-fill-r2-drift.log.tmp
# ---- 2. the copy screen rerun on the 73 added files at the tip, flattened copies ----
rm -rf $WK/screen73; mkdir -p $WK/screen73; : > $WK/screen73-labels.tsv
while read p; do
  fl=${${p#TCSlib/Complexity/}//\//__}
  cp "$W/$p" "$WK/screen73/$fl"
  printf '%s\t%s\t%s\n' "$fl" "$p" "$(shasum -a 256 "$W/$p" | cut -d' ' -f1)" >> $WK/screen73-labels.tsv
done < $G/work/added.txt
start=$(date +%s)
( cd $WK/screen73 && py $W/audits/evidence/retrofit/copy-text-screen.py $WK/screen73 $(ls) > $WK/screen73.out 2> $WK/screen73.err ); src=$?
end=$(date +%s)
{
  echo "# arm-fill-r2-screen-added-only: audits/evidence/retrofit/copy-text-screen.py (unmodified, from the checkout) over byte copies of the 73 added files at the tip, named by flattened paths; rc=$src elapsed=$((end-start))s"
  if cmp -s $WK/screen73.out $G/work/screen-new.out; then echo "IDENTICAL to round 1's added-only screen output (received tree)"; else echo "DIFFERS from round 1's added-only output"; fi
  if diff -q <(cut -f2,3 $WK/screen73-labels.tsv | sort) <(awk -F'\t' 'NR==FNR{a[$1];next} ($2 in a){print $2"\t"$3}' $G/work/added.txt $G/evidence/screen-population-labels.txt | sort) >/dev/null; then echo "the 73 copies' SHA-256 equal round 1's labels"; else echo "SHA-256 MISMATCH with round-1 labels"; fi
  cat $WK/screen73.out
} > $LG/arm-fill-r2-screen-added-only.log
# ---- 3. pairs, same-file included; the same-name blind spot ----
{
  echo "# arm-fill-r2-pairs: every unordered screen pair with an added side, same-file pairs included (scripts/pairs.py over round 1's combined screen output)"
  py $SC/pairs.py $G/work/screen-combined.out $G/evidence/screen-population-labels.txt $G/work/added.txt $G/work/screen-root $WK/pairs.tsv
  echo; echo "# the screen skips a pair when (file label, short name) coincide: same-name declarations inside one added file"
  py $SC/dupnames.py $G/evidence/screen-population-labels.txt $G/work/added.txt $G/work/screen-root
} > $LG/arm-fill-r2-pairs.log
# drift's span check needs pairs.tsv; redo it now that pairs.tsv exists
{
  echo "# arm-fill-r2-drift: the round-1 screen population (214 labelled files) at the received tree vs the tip"
  py $SC/popdrift.py $G/evidence/screen-population-labels.txt $G/work/screen-root $W
  echo; echo "# library side of every library pair: span at the received tree vs the tip (ledger.py span rules)"
  py $SC/tipspans.py $WK/pairs.tsv $G/evidence/screen-population-labels.txt $G/work/screen-root $W
} > $LG/arm-fill-r2-drift.log; rm -f $LG/arm-fill-r2-drift.log.tmp
# ---- 4. classification and groups ----
{
  echo "# arm-fill-r2-classify: class and group of every pair (scripts/classify.py; rules and named overrides in the script)"
  py $SC/classify.py $WK/pairs.tsv $G/evidence/disclosed-copies.tsv $WK/classify.tsv $WK/kfam.tsv
} > $LG/arm-fill-r2-classify.log
# ---- 5. manual (below-floor) entries ----
py $SC/manualtile.py $G/evidence/screen-population-labels.txt $G/work/screen-root $WK/manual-spec.tsv $W > $WK/manual.tsv
# ---- 6. ledgers: round 1 reproduced, then the round-2 accountings ----
( cd $WK && py $G/scripts/ledger.py $G/work/screen-combined.out $G/evidence/screen-population-labels.txt $G/work/added.txt $G/work/screen-root $G/evidence/disclosed-copies.tsv $G/work/root-up.txt > $WK/ledger-r1-repro.out )
py $SC/ledger2.py $G/work/screen-combined.out $G/evidence/screen-population-labels.txt $G/work/added.txt $G/work/screen-root $WK/pairs.tsv $WK/classify.tsv $G/work/root-up.txt $WK/manual.tsv $WK
{
  echo "# arm-fill-r2-ledger: round 1's ledger.py rerun on round 1's inputs, then scripts/ledger2.py (accountings A1-A4+)"
  if cmp -s $WK/ledger-r1-repro.out $G/work/ledger-full.out; then echo "round 1's ledger reproduces byte for byte"; else echo "round 1's ledger does NOT reproduce"; fi
  echo "manual (below-floor) entries:"; cat $WK/manual.tsv
  echo; cat $WK/ledger2.out
} > $LG/arm-fill-r2-ledger.log
# ---- 7. families ----
py $SC/families.py $WK/pairs.tsv $WK/classify.tsv $WK/kfam.tsv $WK/families.out > /dev/null
{ echo "# arm-fill-r2-families: round 1's 45 internal components, the same-file components, the logical families (scripts/families.py)"; cat $WK/families.out } > $LG/arm-fill-r2-families.log
# ---- 8. registry inputs: declaration lines and direct importers at the tip ----
py $G/evidence/tools/imports.py $W $WK/graph-tip.json > /dev/null
{
  echo "# arm-fill-r2-registry: declaration header lines (scripts/finddecl.py, comment-stripped) and direct importers of each component (scripts/consumers.py) at the tip"
  py $SC/finddecl.py $W compile_correct_from compile_correct arm_space arm_decides arm_decides_poly arm_decides_space arm_decides_SPACE arm_decides_pspace arm_decides_pspace_of_logspace arm_decides_pspace_val LOGSPACE_subset_PSPACE SPACE_succ_pow_subset_PSPACE GuardLe arm_reach move_run dmove_run vword_whole₂ vword_whole₃ NIns NARM nastep narun NHalts NAns ncompileTM ncompileFinNDTM narm_space narm_decides_space narm_decides narm_decides_poly narm_decides_npspace narm_decides_npspace_of_logspace NTerm NAcc NSem NSem.decides NSPACE.mono_const MIns MARM mstep MReach MHalt mcompileTM mcompileFinTM runFrom_count_eq marm_dtime InWin cfgWord cfgCode cfgWord_congr coreSum_eq_of_cfgWord_eq codeK cfgCode_lt decodeCfg decodeCfg_cfgCode validLang initLang acceptLang stepLang validLang_mem acceptLang_mem initLang_mem stepLang_mem StepRel mem_of_codePath mem_iff_codeChain inputBitLang inputLenLang vword_whole₁ boundedDecode_loop mem_LOGSPACE_preimage compile_decides RCode rset mem_iff_of_card_eq inWin_runWith_of_decides card_rset_succ_of_le NSPACE_subset_exp_dtime_of_le NSPACE_subset_exp_dtime NL_subset_P polyTimeReducible_of_mem_NL Reach NSPACE_poly_subset_PSPACE NPSPACE_subset_PSPACE decs orcN igA GS compl_mem_NSPACE compl_mem_NL WalkLe walkLe_short reach_iff_walkLe rawEdge pathRawLang pathA pathRawLang_mem_NL PATH_eq_pathRawLang Edge red pathRawLang_NLHard truth_mem_PSPACE synStep synOK levelQuants levelMatrix Mid mid_iff_steps predB toCNF_extension_iff PSPACE_polyTimeReducible_TQBF truth_exSuffix_of_pointwise Cfg.InWindow CfgStep coreSum GraphReach | /usr/bin/grep -v 'Kruskal\|StepBlock\|ARMSim\|LogspaceUniform\|Programs/Light\|UnaryLogspace'
  echo; py $SC/consumers.py $WK/graph-tip.json
} > $LG/arm-fill-r2-registry.log
# ---- 9. the C1 delta to the received tree (finding 14) ----
git -C $W diff $PR87P $PR87M > $WK/pr87.diff
git -C $W diff $DC $RX > $WK/c1-delta.diff
git -C $W diff --name-status $PR87P $PR87M > $WK/pr87-diff-names.txt
{
  echo "# arm-fill-r2-c1delta: PR #87 (C1's host contracts) against the received tree"
  echo "PR #87 diff ($PR87P..$PR87M): $(wc -l < $WK/pr87-diff-names.txt | tr -d ' ') paths; SHA-256 $(shasum -a 256 $WK/pr87.diff | cut -d' ' -f1)"
  echo "dc891632..733c22b7 diff: SHA-256 $(shasum -a 256 $WK/c1-delta.diff | cut -d' ' -f1)"
  if cmp -s $WK/pr87.diff $WK/c1-delta.diff; then echo "the two diffs are byte-identical: the replay revision is the received tree plus exactly PR #87's diff"; else echo "the two diffs DIFFER"; exit 3; fi
  if git -C $W diff --quiet $PR87P $DC -- '*.lean'; then echo "PR #87's first parent has the received tree's Lean files (dc891632's)"; else echo "first parent Lean differs"; fi
  echo; printf 'path\tstatus\tblob@dc891632\tblob@733c22b7\tSHA-256@733c22b7\tbytes\tblob@tip\tsame at tip\n'
  while read st p; do
    if git -C $W cat-file -e "$DC:$p" 2>/dev/null; then b0=$(git -C $W rev-parse "$DC:$p"); else b0=-; fi
    b1=$(git -C $W rev-parse "$RX:$p")
    if git -C $W cat-file -e "$TIP:$p" 2>/dev/null; then bt=$(git -C $W rev-parse "$TIP:$p"); else bt=-; fi
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$p" "$st" "$b0" "$b1" "$(git -C $W cat-file blob $b1 | shasum -a 256 | cut -d' ' -f1)" "$(git -C $W cat-file -s $b1)" "$bt" "$([[ $b1 == $bt ]] && echo yes || echo no)"
  done < $WK/pr87-diff-names.txt
  echo; echo "# which of the ten are in the upstream import closure of the 81 received modules (round 1's closure list, received tree)"
  while read st p; do m=${${p%.lean}//\//.}; printf '%s: %s\n' "$p" "$(/usr/bin/grep -cx "$m" $G/work/up-all81.txt || true)"; done < $WK/pr87-diff-names.txt
  echo; echo "# sorry tokens (comment-stripped code) in the two upstream files, before and after"
  for c in $DC $RX; do for f in TCSlib/Complexity/TuringMachine/Nondeterministic.lean TCSlib/Complexity/TuringMachine/NondeterministicSpace.lean; do
    git -C $W show "$c:$f" > $WK/tmp_src.lean
    echo "${c[1,8]} ${f:t}: $(py -c "import sys,re; sys.path.insert(0,'$SC'); from leancore import strip_keep_lines; print(len(re.findall(r'\bsorry\b', strip_keep_lines(open('$WK/tmp_src.lean',encoding='utf-8').read()))))") sorry token(s)"
  done; done; rm -f $WK/tmp_src.lean
  echo; echo "# text hits (comments included), at the received tree, of the two lemmas C1 proved"
  git -C $W grep -n -w -e runWith_eq_fixChoice_runFrom -e spaceUsedWith_eq_fixChoice_spaceUsed $DC -- 'TCSlib/*.lean' | sed "s/^$DC://"
  echo "# the same files comment-stripped: code references other than the two declaration headers"
  args=(); mkdir -p $WK/c1refs
  for f in $(git -C $W grep -l -w -e runWith_eq_fixChoice_runFrom -e spaceUsedWith_eq_fixChoice_spaceUsed $DC -- 'TCSlib/*.lean' | sed "s/^$DC://"); do
    git -C $W show "$DC:$f" > $WK/c1refs/${f:t}; args+=("$f=$WK/c1refs/${f:t}"); done
  py $SC/coderefs_at.py runWith_eq_fixChoice_runFrom,spaceUsedWith_eq_fixChoice_spaceUsed $args
  rm -rf $WK/c1refs
} > $LG/arm-fill-r2-c1delta.log
# ---- 10. record checks for the payback decisions (D1, D6, s1b) ----
{
  echo "# arm-fill-r2-records: counts behind the dedup decisions (backlog ARM-1 at e831b5b0)"
  echo "## D1: code occurrences of InWin (comment-stripped), by file"
  py $SC/refs.py $W '\bInWin\b' none 0 0 | awk -F: '/^TCSlib/{print $1}' | sort | uniq -c
  py $SC/refs.py $W '\bInWin\b' none 0 0 | tail -1
  echo "## D1: code uses of ConfigGraph's bridge inWindow_iff_cfgInWindow"
  py $SC/refs.py $W '\binWindow_iff_cfgInWindow\b' none 0 0
  echo "## D6: declarations in ClassPSPACE/TQBF.lean lines 2474-3185 (the b4m* appendix)"
  py $SC/b4m.py $W/TCSlib/Complexity/ClassPSPACE/TQBF.lean 2474 3185
  echo "## D6: b4m references outside TQBF.lean (code)"
  py $SC/refs.py $W '\bb4m\w*' TCSlib/Complexity/ClassPSPACE/TQBF.lean 1 99999 | tail -1
  echo "## s1b_*: code references outside ConfigGraph.lean (s1b_binderkinds in ShapeFixtures is an unrelated name)"
  py $SC/refs.py $W '\bs1b_\w*' TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean 1 99999
} > $LG/arm-fill-r2-records.log
# ---- 10b. two merged PRs said to be comment-only (#89, #91) ----
{
  echo "# arm-fill-r2-commentonly: Lean changes of #89 (f4b23f05) and #91 (1a70235c) against their first parents, comment-stripped"
  for c in f4b23f05 1a70235c; do
    H=$(git -C $W rev-parse $c^{commit}); P=$(git -C $W rev-parse $H^1); rm -rf $WK/co; mkdir -p $WK/co; args=()
    for f in $(git -C $W diff --name-only $P $H -- '*.lean'); do
      b=$WK/co/${f//\//_}; git -C $W show "$P:$f" > $b.before 2>/dev/null || : > $b.before; git -C $W show "$H:$f" > $b.after; args+=($b.before $b.after)
    done
    echo "$H: $(py $SC/codeonly_commit.py $args)"
  done; rm -rf $WK/co
} > $LG/arm-fill-r2-commentonly.log
# ---- 11. evidence copies ----
mkdir -p $EV/inputs
for f in $G/work/screen-combined.out $G/work/added.txt $G/work/root-up.txt $G/work/up-all81.txt; do cp $f $EV/inputs/; done
{ echo "# r2/inputs: copies of round 1's builder work files (not landed in round 1), used by run_r2.zsh"; for f in $EV/inputs/*(.); do [[ ${f:t} == MANIFEST.txt ]] || echo "$(shasum -a 256 $f | cut -d' ' -f1)  ${f:t}"; done } > $EV/inputs/MANIFEST.txt
cp $WK/pr87.diff $EV/pr87.diff
for f in pairs.tsv classify.tsv kfam.tsv manual-spec.tsv manual.tsv ledger2-decls.tsv families.out pr87-diff-names.txt; do cp $WK/$f $EV/$f; done
mv $EV/families.out $EV/families.txt
py $SC/tables.py $WK $EV/ledger-r2-tables.md
# ---- 12. every git hash in the deliverables resolves (abbreviations included) ----
{
  echo "# arm-fill-r2-hashcheck: every 7-40 hex token of the pack, NOTES and the evidence notes that names a git object"
  for f in $R/arm-extensions-fill-r2-pack.md $R/NOTES.md $EV/corrections.md $EV/registry-rows.md; do
    [[ -e $f ]] || continue
    for t in $(/usr/bin/grep -oE '\b[0-9a-f]{7,40}\b' $f | sort -u); do
      if [[ ${#t} -eq 64 ]]; then continue; fi
      if full=$(git -C $W rev-parse --verify --quiet "$t^{object}" 2>/dev/null); then
        [[ $full == $t* ]] && echo "ok  ${f:t} $t -> $full ($(git -C $W cat-file -t $full))" || { echo "BAD ${f:t} $t"; exit 4 }
      else echo "not a git object (left as is): ${f:t} $t"; fi
    done
  done
} > $LG/arm-fill-r2-hashcheck.log
echo "run_r2: done"
