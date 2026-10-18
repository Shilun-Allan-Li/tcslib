#!/bin/zsh
# Stage the round-3 bundle's files at their repository (landing) paths, then list them in bundle
# order (stage/BUNDLE-ORDER.txt, also written as r3/BUNDLE-FILES.txt with sizes).
# Repository files come from the campaign tip by `git show` (read only); this round's files from
# the builder's folder; the payback landing material from land-payback/ (read only).
# usage: zsh stage.zsh <S> <repo>
set -euo pipefail
S=$1; REPO=$2
R3=$S/gate-arm-r3; LP=$S/land-payback; G=$S/gate-arm
ST=$R3/stage; WK=$R3/work
TIP=$(git -C $REPO rev-parse origin/complexity/arora-barak-ch3-4)
rm -rf $ST; mkdir -p $ST
order=()
fromtip() { for p in "$@"; do mkdir -p $ST/${p:h}; git -C $REPO show "${TIP}:$p" > $ST/$p; order+=($p); done }
mine() { mkdir -p $ST/${2:h}; cp $1 $ST/$2; order+=($2) }
R3P=audits/evidence/arm-fill/r3
# A. the pack, the round-2 and round-1 records, the standards, the campaign records (whole)
mine $R3/arm-extensions-fill-r3-pack.md audits/arm-extensions-fill-r3-pack.md
fromtip audits/arm-extensions-fill-r2-findings.md audits/arm-extensions-fill-r2-resolutions.md \
  audits/arm-extensions-fill-r2-pack.md audits/arm-extensions-fill-findings.md \
  audits/TEMPLATE.md policy.md workflow.md arm-extensions-response.md backlog.md \
  machine-library-design.md AroraBarakChapters3-4Plan.md
# B. round-3 evidence
mine $R3/NOTES.md $R3P/NOTES.md
for f in ledger-r3-tables.md excerpts-n-pairs.md dispositions.tsv transitions.tsv pairs3-base.tsv pairs3-landed.tsv pairs3-tip.tsv \
         classify3-base.tsv classify3-landed.tsv classify3-tip.tsv n3lib.tsv landed-overrides.tsv \
         manual3-spec.tsv manual3-base.tsv manual3-landed.tsv manual3-tip.tsv \
         ledger3-base-decls.tsv ledger3-landed-decls.tsv ledger3-tip-decls.tsv pop3.txt patch-stats.txt; do mine $R3/evidence/$f $R3P/$f; done
for f in $R3/scripts/*(.); do mine $f $R3P/scripts/${f:t}; done
# C. logs
for f in $R3/logs/*.log(.); do mine $f audits/logs/${f:t}; done
# D. the payback (the refactor's diff and its landing evidence), read from land-payback/
mine $LP/LANDING-NOTES.md $R3P/payback/LANDING-NOTES.md
mine $LP/ledger-map.md $R3P/payback/ledger-map.md
mine $LP/replay-order.txt $R3P/payback/replay-order.txt
mine $LP/SHA256SUMS $R3P/payback/SHA256SUMS
for f in $LP/patches/*.patch(.); do mine $f $R3P/payback/patches/${f:t}; done
for f in verify.log freeze.log elaboration.log controls.log names.log cuts.log graph.log hygiene.log ledger.log probes.log land-edits.txt; do mine $LP/logs/$f $R3P/payback/logs/$f; done
mine $LP/work/api-delta.json $R3P/payback/work/api-delta.json
for f in $LP/scripts/*(.); do mine $f $R3P/payback/scripts/${f:t}; done
# (land-payback/tree/ is not bundled: its 27 files equal the bundled tip files byte for byte, provenance log)
# E. round-2 evidence that round 3's scripts read; the v3 screen and its notes
fromtip audits/evidence/arm-fill/r2/pairs.tsv audits/evidence/arm-fill/r2/classify.tsv audits/evidence/arm-fill/r2/kfam.tsv \
  audits/evidence/arm-fill/r2/manual.tsv audits/evidence/arm-fill/r2/ledger2-decls.tsv audits/evidence/arm-fill/r2/ledger-r2-tables.md \
  audits/evidence/arm-fill/r2/registry-rows.md audits/evidence/arm-fill/r2/corrections.md \
  audits/evidence/arm-fill/screen-population-labels.txt \
  audits/evidence/arm-fill/r2/inputs/added.txt \
  audits/evidence/retrofit/copy-text-screen-v3.py audits/evidence/screenfix/v3/NOTES.md audits/evidence/screenfix/NOTES.md
# F. Lean sources at the tip: the 73 added files, then the 27 library files the ledger rows cite (the 27 payback files
#    among them equal the measured landed tree; no bundled file differs between the tip and the landed tree)
fromtip $(cat $G/work/added.txt)
fromtip $(cat $WK/bundle-library.txt)
print -l $order > $ST/BUNDLE-ORDER.txt
{ print "# BUNDLE-FILES — ARM-extensions fill gate, round 3 (repository paths in bundle order, TAB, bytes)"
  print "# Repository files at the tip $TIP (every bundled Lean file equals the measured landed tree); this round's and the payback's files at their landing paths."
  tot=0; for p in $order; do s=$(wc -c < $ST/$p | tr -d ' '); tot=$((tot+s)); print "$p	$s"; done
  print "# total: ${#order} files, $tot bytes" } > $ST/BUNDLE-FILES.txt
mkdir -p $ST/$R3P; cp $ST/BUNDLE-FILES.txt $R3/evidence/BUNDLE-FILES.txt
echo "staged ${#order} files"
