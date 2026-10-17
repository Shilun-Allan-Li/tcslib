#!/bin/zsh
# Round-3 evidence runner for the ARM extensions fill gate (read-only analysis; no Lean, no git
# writes). Inputs: the read-only repository (git), the payback landing folder (read only), the three
# v3 screens already run by scripts/screen.zsh (base, landed, tip). Writes under $R3 only.
# usage: zsh run_r3.zsh <S> <repo>
set -euo pipefail
S=$1; REPO=$2
R3=$S/gate-arm-r3; LP=$S/land-payback; G=$S/gate-arm
SC=$R3/scripts; WK=$R3/work; LG=$R3/logs; EV=$R3/evidence
py() { python3 -I -B "$@" }
TIP=$(git -C $REPO rev-parse origin/complexity/arora-barak-ch3-4)
BASE=$(git -C $REPO rev-parse ff4cab18^{commit})
C9=$(git -C $REPO rev-parse c9cc485b^{commit})
RECV=$(git -C $REPO rev-parse 8c23f3bc^{commit})
R2T=$(git -C $REPO rev-parse e831b5b0^{commit})
EB=$(git -C $REPO rev-parse eb750e63^{commit})
PR101=$(git -C $REPO rev-parse 9c0ae906^{commit}); PR101P=$(git -C $REPO rev-parse $PR101^1)
for h in $TIP $BASE $C9 $RECV $R2T $EB $PR101 $PR101P; do git -C $REPO cat-file -e $h; done
LPB=$(cat $LP/work/base-commit.txt)
[[ $LPB == $BASE || $LPB == $EB ]] || { echo "landing base $LPB is neither ff4cab18 nor eb750e63" >&2; exit 2 }
for t in base landed tip; do [[ $(cat $WK/screen-$t.out.status) == rc=0* ]] || { echo "screen $t not complete" >&2; exit 2 }; done
# ---- import graphs (the module import relation of each tree; TCSlib imports only) ----
for t in base landed tip; do py $SC/imports.py $WK/$t $WK/graph-$t.json > /dev/null; done
# ---- provenance ----
{
  echo "# arm-fill-r3-provenance (hashes from git rev-parse; checked with cat-file -e)"
  echo "campaign tip                $TIP"
  echo "payback base                $BASE  (land-payback/work/base-commit.txt agrees)"
  echo "Lean content of the base    $C9"
  echo "received commit             $RECV"
  echo "round-2 tree                $R2T"
  echo "landing folder's base now   $LPB  (work/base-commit.txt; the landing was re-run after MIG-1 S, #98)"
  echo "PR #101 (the payback) merge $PR101  (first parent $PR101P)"
  P27=(${(f)"$(cut -f1 $WK/patch-stats.txt)"})
  git -C $REPO diff --quiet $BASE $EB -- $P27 && echo "the 27 payback files: identical at ff4cab18 and eb750e63" || { echo "27 files differ ff4cab18..eb750e63"; exit 3 }
  git -C $REPO diff --quiet $BASE $PR101P -- $P27 && echo "the 27 payback files: identical at ff4cab18 and at #101's first parent" || { echo "27 files differ at #101's parent"; exit 3 }
  diff <(git -C $REPO diff --name-only $PR101P $PR101 | sort) <(print -l $P27 | sort) > /dev/null && echo "PR #101 changes exactly the 27 files" || { echo "PR #101's file set differs"; exit 3 }
  k=0; for f in $P27; do git -C $REPO show "${PR101}:$f" | cmp -s - $WK/landed/$f || { echo "#101 differs from the landed tree: $f"; exit 3 }; git -C $REPO show "${TIP}:$f" | cmp -s - $WK/landed/$f || { echo "tip differs from the landed tree: $f"; exit 3 }; k=$((k+1)); done
  echo "the 27 files at #101's merge and at the tip equal the measured landed tree byte for byte: $k files"
  echo "Lean files where the tip differs from the measured landed tree (PRs #98-#100, none a payback file):"
  for f in $(git -C $REPO ls-tree -r --name-only $TIP TCSlib | /usr/bin/grep '\.lean$'); do git -C $REPO show "${TIP}:$f" | cmp -s - $WK/landed/$f 2>/dev/null || echo "  $f$( /usr/bin/grep -qx $f $WK/pop3.txt && echo ' (in the screen population)')"; done
  echo "Lean files in the landed tree absent at the tip: $(n=0; for f in $(cd $WK/landed && find TCSlib -name '*.lean'); do git -C $REPO cat-file -e "${TIP}:$f" 2>/dev/null || { n=$((n+1)); echo "  $f" >&2 }; done; echo $n)"
  echo "tip export ($WK/tip) equals git archive of the tip: $(n=0; b=0; for f in $(git -C $REPO ls-tree -r --name-only $TIP TCSlib | /usr/bin/grep '\.lean$'); do n=$((n+1)); git -C $REPO show "${TIP}:$f" | cmp -s - $WK/tip/$f || b=$((b+1)); done; echo "$n files, $b differ")"
  git -C $REPO diff --quiet $BASE $C9 -- '*.lean' && echo "Lean files: base == c9cc485b" || { echo "base Lean differs from c9cc485b"; exit 3 }
  git -C $REPO merge-base --is-ancestor $BASE $TIP && echo "base is an ancestor of the tip"
  echo "# after the bundle's tip: #102's merge, in the object store but not in the local branch ref"
  N102=$(git -C $REPO rev-parse d32e12c0^{commit}); git -C $REPO cat-file -e $N102
  git -C $REPO merge-base --is-ancestor $TIP $N102 && echo "$N102 descends from the tip"
  for f in $(git -C $REPO diff --name-only $TIP $N102); do echo "  $f: in the population $(/usr/bin/grep -cx $f $WK/pop3.txt), bundled $(cat $G/work/added.txt $WK/bundle-library.txt | /usr/bin/grep -cx $f)"; done
  echo "v3 screen script: $(shasum -a 256 $SC/copy-text-screen-v3.py | cut -d' ' -f1) (the tip's audits/evidence/retrofit/copy-text-screen-v3.py: $(git -C $REPO show "${TIP}:audits/evidence/retrofit/copy-text-screen-v3.py" | shasum -a 256 | cut -d' ' -f1))"
  echo
  echo "# the base export ($WK/base) against git archive of the base, and the landed tree against base + the 27 patches"
  n=0; bad=0
  for f in $(git -C $REPO ls-tree -r --name-only $BASE TCSlib | /usr/bin/grep '\.lean$'); do
    n=$((n+1)); git -C $REPO show "${BASE}:$f" | cmp -s - $WK/base/$f || { bad=$((bad+1)); echo "base export differs: $f" }
  done; echo "base export: $n Lean files, $bad differ"
  rm -rf $WK/replay; mkdir -p $WK/replay; cp -R $WK/base/. $WK/replay/
  ( cd $WK/replay && for p in $LP/patches/*.patch; do patch -p1 -s < $p; done )
  d=$(diff -rq $WK/replay $WK/landed | wc -l | tr -d ' '); echo "base + 27 patches vs the landed tree: $d differences"
  m=0; for f in $(cd $LP/tree && find . -name '*.lean' | sed 's#^\./##'); do m=$((m+1)); cmp -s $LP/tree/$f $WK/landed/$f || { echo "landing tree differs: $f"; exit 3 }; done
  echo "the landing folder's tree/ (27 files) equals the landed tree byte for byte: $m files"
  rm -rf $WK/replay
  echo "files changed by the payback: $(diff -rq $WK/base $WK/landed | wc -l | tr -d ' ')"
  echo "PR #101's diffstat: $(git -C $REPO diff --shortstat $PR101P $PR101)"
  echo "# the 27 files by kind (comment-stripped identity), with the patch line counts"
  py $SC/paybackkinds.py $WK/base $WK/landed $WK/patch-stats.txt
  echo; echo "# land-payback/SHA256SUMS, rechecked"
  ( cd $LP && shasum -a 256 -c SHA256SUMS --quiet && echo "all $(wc -l < SHA256SUMS | tr -d ' ') entries OK" )
  echo; echo "# population: round 1's 214 files + 2 modules now in the added files' closure at the base + 2 added by the payback"
  echo "population files: $(wc -l < $WK/pop3.txt | tr -d ' '); SHA-256 of the list $(shasum -a 256 $WK/pop3.txt | cut -d' ' -f1)"
  py $SC/popcheck.py $WK/graph-base.json $WK/graph-landed.json $G/evidence/screen-population-labels.txt $G/work/added.txt $WK/pop3.txt
} > $LG/arm-fill-r3-provenance.log
# ---- the three screens ----
for t in base landed tip; do
  py $SC/screenfilter.py $WK/screen-$t.out $WK/pop3.txt $G/work/added.txt > $WK/screen-$t.added.txt
  { echo "# arm-fill-r3-screen-$t: copy-text-screen-v3.py (unmodified) over the 218-file population at the $t tree, repository paths, niced; $(cat $WK/screen-$t.out.status); stderr bytes $(wc -c < $WK/screen-$t.out.err | tr -d ' ')"
    echo "# full output: $(wc -l < $WK/screen-$t.out | tr -d ' ') lines, SHA-256 $(shasum -a 256 $WK/screen-$t.out | cut -d' ' -f1); its first line:"
    head -1 $WK/screen-$t.out
    echo "# below: exactly the hit lines with an added-file side ($(/usr/bin/grep -c reproduces $WK/screen-$t.added.txt | tr -d ' ') lines), in the output's order; pairs3.py reads them unchanged"
    cat $WK/screen-$t.added.txt } > $LG/arm-fill-r3-screen-$t.log
done
# ---- pairs, classes, ledgers ----
{
  echo "# arm-fill-r3-pairs: base, then landed, then tip (ids: round 2's, then N3-* new at the base, L3-* new at the landed tree, T3-* new at the tip)"
  py $SC/pairs3.py $WK/screen-base.out $WK/pop3.txt $G/work/added.txt $WK/base $WK/r2/pairs.tsv $WK/pairs3-base.tsv
  echo "# the base's pairs against round 2's (same ids, hits, bodies; moved lines)"
  py $SC/r2compare.py $WK/pairs3-base.tsv $WK/r2/pairs.tsv
  py $SC/pairs3.py $WK/screen-landed.out $WK/pop3.txt $G/work/added.txt $WK/landed $WK/r2/pairs.tsv $WK/pairs3-landed.tsv $WK/pairs3-base.tsv L3
  py $SC/pairs3.py $WK/screen-tip.out $WK/pop3.txt $G/work/added.txt $WK/tip $WK/r2/pairs.tsv $WK/pairs3-tip.tsv $WK/pairs3-landed.tsv T3
} > $LG/arm-fill-r3-pairs.log
{
  echo "# arm-fill-r3-classify: base, then landed, then tip (the landed overrides apply at both)"
  py $SC/classify3.py $WK/pairs3-base.tsv $WK/r2/classify.tsv $WK/r2/kfam.tsv $WK/n3lib.tsv $WK/classify3-base.tsv
  py $SC/classify3.py $WK/pairs3-landed.tsv $WK/r2/classify.tsv $WK/r2/kfam.tsv $WK/n3lib.tsv $WK/classify3-landed.tsv $WK/landed-overrides.tsv
  py $SC/classify3.py $WK/pairs3-tip.tsv $WK/r2/classify.tsv $WK/r2/kfam.tsv $WK/n3lib.tsv $WK/classify3-tip.tsv $WK/landed-overrides.tsv
} > $LG/arm-fill-r3-classify.log
for t in base landed; do py $SC/manualtile3.py $WK/$t $t $WK/manual3-spec.tsv > $WK/manual3-$t.tsv; done
py $SC/manualtile3.py $WK/tip landed $WK/manual3-spec.tsv > $WK/manual3-tip.tsv
{
  echo "# arm-fill-r3-ledger: ledger3.py at the base, then at the landed tree, then at the tip"
  py $SC/ledger3.py $WK/pairs3-base.tsv $WK/classify3-base.tsv $WK/base $G/work/added.txt $WK/manual3-base.tsv $WK/ledger3-base > /dev/null
  cat $WK/ledger3-base.out; echo
  py $SC/ledger3.py $WK/pairs3-landed.tsv $WK/classify3-landed.tsv $WK/landed $G/work/added.txt $WK/manual3-landed.tsv $WK/ledger3-landed > /dev/null
  cat $WK/ledger3-landed.out; echo
  py $SC/ledger3.py $WK/pairs3-tip.tsv $WK/classify3-tip.tsv $WK/tip $G/work/added.txt $WK/manual3-tip.tsv $WK/ledger3-tip > /dev/null
  cat $WK/ledger3-tip.out
  echo; echo "# round 3's K+ at the base against round 2's acknowledged A4+ (r2/ledger2-decls.tsv)"
  py $SC/r2decls.py $WK/r2/ledger2-decls.tsv $WK/ledger3-base-decls.tsv
  echo; echo "# the tip against the measured landed tree: the pair sets, classes and K+ declaration tables"
  py $SC/tipcompare.py $WK/pairs3-landed.tsv $WK/classify3-landed.tsv $WK/ledger3-landed-decls.tsv $WK/pairs3-tip.tsv $WK/classify3-tip.tsv $WK/ledger3-tip-decls.tsv
} > $LG/arm-fill-r3-ledger.log
{
  echo "# arm-fill-r3-transitions: every pair base -> landed, and the payback ledger map's rows"
  py $SC/transitions.py $WK/pairs3-base.tsv $WK/classify3-base.tsv $WK/pairs3-landed.tsv $WK/classify3-landed.tsv $LP/ledger-map.md $WK/transitions.tsv $WK/dispositions.tsv
  cat $WK/dispositions.tsv
} > $LG/arm-fill-r3-transitions.log
# ---- excerpts of the 25 counterparts round 2 could not show ----
py $SC/excerpts.py $WK/pairs3-base.tsv $WK/classify3-base.tsv $WK/base $WK/excerpts-n-pairs.md --tip $WK/pairs3-tip.tsv L013 L014 L096 L036 L037 L063 L088 L089 L105 L094 L095 L097 L098 L106 L108 L112 L099 L100 L107 L109 L113 L101 L102 L103 L104 L033 > $LG/arm-fill-r3-excerpts.log
# ---- R2-8: finding 11's leftovers, base against landed ----
py $SC/leftovers.py $WK/base $WK/landed > $LG/arm-fill-r3-leftovers.log
# ---- R2-2 and R2-6: the records at the tip ----
zsh $SC/records3.zsh $REPO $TIP > $LG/arm-fill-r3-records.log
# ---- R2-5's lower homes, on the landed tree's import graph ----
py $SC/homes.py $WK/landed $WK/graph-landed.json > $LG/arm-fill-r3-homes.log
py $SC/homes.py $WK/tip $WK/graph-tip.json | sed 's/^/tip: /' >> $LG/arm-fill-r3-homes.log
# ---- tables ----
py $SC/tables3.py $WK $WK/ledger-r3-tables.md > /dev/null
# ---- evidence copies ----
for f in pairs3-base.tsv pairs3-landed.tsv classify3-base.tsv classify3-landed.tsv n3lib.tsv manual3-spec.tsv manual3-base.tsv manual3-landed.tsv landed-overrides.tsv ledger3-base-decls.tsv ledger3-landed-decls.tsv pairs3-tip.tsv classify3-tip.tsv ledger3-tip-decls.tsv manual3-tip.tsv transitions.tsv dispositions.tsv excerpts-n-pairs.md ledger-r3-tables.md pop3.txt patch-stats.txt; do cp $WK/$f $EV/$f; done
# ---- logs: the scratch root printed as <S> ----
for f in $LG/*.log; do py -c 'import sys; p, r = sys.argv[1:3]; t = open(p, encoding="utf-8").read(); open(p, "w", encoding="utf-8").write(t.replace(r + "/", "<S>/"))' $f $S; done
echo "run_r3: done"
