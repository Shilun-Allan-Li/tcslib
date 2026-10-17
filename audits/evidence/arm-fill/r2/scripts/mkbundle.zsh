#!/bin/zsh
# Writes evidence/BUNDLE-FILES.txt: repository paths in bundle order, with sizes (repository files
# at the tip e831b5b0 via git cat-file -s; this round's files from the builder's folder, under
# their landing paths). usage: zsh mkbundle.zsh <S>
set -euo pipefail
S=$1; W=$S/wt-armr2; R=$S/gate-arm-r2; G=$S/gate-arm
TIP=$(git -C $W rev-parse e831b5b0^{commit})
out=$R/evidence/BUNDLE-FILES.txt; tmp=$out.tmp; : > $tmp
total=0; nfiles=0
sec() { print -r -- "" >> $tmp; print -r -- "## $1" >> $tmp }
repo() { for p in "$@"; do s=$(git -C $W cat-file -s "$TIP:$p"); print -r -- "$p	$s" >> $tmp; total=$((total+s)); nfiles=$((nfiles+1)); done }
mine() { s=$(wc -c < "$1" | tr -d ' '); print -r -- "$2	$s" >> $tmp; total=$((total+s)); nfiles=$((nfiles+1)) }
sec "A. This pack, round 1's findings and pack, the standards, the response, the records (whole)"
mine $R/arm-extensions-fill-r2-pack.md audits/arm-extensions-fill-r2-pack.md
repo audits/arm-extensions-fill-findings.md audits/arm-extensions-fill-pack.md audits/TEMPLATE.md policy.md workflow.md arm-extensions-response.md backlog.md machine-library-design.md AroraBarakChapters3-4Plan.md
sec "B. Round-2 evidence (audits/evidence/arm-fill/r2/)"
mine $R/NOTES.md audits/evidence/arm-fill/r2/NOTES.md
for f in ledger-r2-tables.md registry-rows.md corrections.md pairs.tsv classify.tsv kfam.tsv manual-spec.tsv manual.tsv ledger2-decls.tsv families.txt pr87-diff-names.txt pr87.diff; do mine $R/evidence/$f audits/evidence/arm-fill/r2/$f; done
for f in $R/evidence/inputs/*(.); do mine $f audits/evidence/arm-fill/r2/inputs/${f:t}; done
for f in $R/scripts/*(.); do mine $f audits/evidence/arm-fill/r2/scripts/${f:t}; done
sec "C. Logs: round 2, and round 1's ledger log"
for f in $R/logs/*.log(.); do mine $f audits/logs/${f:t}; done
repo audits/logs/arm-fill-ledger.log
sec "D. Round 1's evidence that round 2's scripts read"
repo audits/evidence/arm-fill/screen-population-labels.txt audits/evidence/arm-fill/disclosed-copies.tsv audits/evidence/arm-fill/design-14-extract.md audits/evidence/arm-fill/scripts/ledger.py audits/evidence/arm-fill/scripts/leanlib.py audits/evidence/arm-fill/tools/imports.py audits/evidence/retrofit/copy-text-screen.py audits/evidence/arm-fill/AxARM.lean.txt
sec "E. The 73 added Lean files (identical at 8c23f3bc and at the tip)"
repo $(cat $G/work/added.txt)
sec "F. Library files the ledger rows and the registry cite (at the tip)"
repo TCSlib/Complexity/SpaceComplexity/Machines/{ARMProof,ARMKit,Compile,ARMRun,Call,Parse,Parse2,ParseCmp,DblLang}.lean \
  TCSlib/Complexity/SpaceComplexity/{ConfigCount,ConfigGraph}.lean \
  TCSlib/Complexity/SpaceComplexity/Logspace/{InputAccess,QueryReshape,Mult,PreimageHost,Path}.lean \
  TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean \
  TCSlib/Complexity/CircuitComplexity/{DAGCircuitSat,TreeDAG,DAGTransform,DAGFanin,PSubsetPPolyConfigCircuit}.lean \
  TCSlib/Complexity/Formulas/QBF.lean TCSlib/Complexity/ClassPSPACE/TQBF.lean TCSlib/Programs/Util/List.lean \
  TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean TCSlib/Complexity/CookLevin/Hardness.lean
{ print -r -- "# BUNDLE-FILES — ARM-extensions fill gate, round 2 (audits/arm-extensions-fill-r2-bundle.md)"
  print -r -- "# Repository paths in bundle order, TAB, size in bytes. Repository files at the tip $TIP"
  print -r -- "# (its Lean tree equals 39bfdca4's and, for the 81 received files, 8c23f3bc's). This round's files under their landing paths."
  print -r -- "# Total: $nfiles files, $total bytes."
  print -r -- "# Not included (named for completeness): round 1's screen logs (arm-fill-screen.log, arm-fill-screen-supplement.log; r2/inputs/screen-combined.out, which round 1's ledger read, is the full-population output verbatim followed by the supplement's 215 pairs that involve its four extra files (provenance log)), Build/Catalog, Build/Embed and the other library files that only incidental pairs touch (lines in r2/pairs.tsv), PRs #92 and #93 (open; the maintainer adds their diffs when ready)."
  cat $tmp } > $out
rm -f $tmp
print -r -- "bundle list: $nfiles files, $total bytes"
