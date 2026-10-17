#!/bin/zsh
# Builds gate-arm/BUNDLE-FILES.txt (repository paths) and estimates the bundle size from the
# sizes of the sources (checkout files at the tip; gate-arm files for the pack's own outputs).
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
W=$S/wt-t2; G=$S/gate-arm; O=$G/BUNDLE-FILES.txt; T=$G/work/bundle-sizes.tsv
: > $T
sz() { wc -c < "$1" | tr -d ' '; }
add() { # section, repo path, source file
  echo "$1	$2	$(sz $3)" >> $T
}
# A. pack, standards, records
add A audits/arm-extensions-fill-pack.md $G/arm-extensions-fill-pack.md
for f in audits/TEMPLATE.md policy.md workflow.md arm-extensions-response.md arm-extensions-proposal.md AroraBarakChapters3-4Plan.md backlog.md; do add A $f $W/$f; done
# B. received Lean files, after state (= 8c23f3bc = tip)
for f in $(cat $G/work/added.txt $G/work/modified.txt); do add B $f $W/$f; done
# C. before state of the 8 modified files
for f in $(cat $G/work/modified.txt); do add C audits/evidence/arm-fill/before/$f.txt $G/evidence/before/$f.txt; done
# D. evidence, logs, scripts, tools
for f in $(cd $G/evidence && find . -type f ! -path './before/*' | sed 's|^\./||' | sort); do
  add D audits/evidence/arm-fill/$f $G/evidence/$f; done
for f in $(cd $G/logs && ls arm-fill-*.log); do add D audits/logs/$f $G/logs/$f; done
add D audits/evidence/arm-fill/BUNDLE-FILES.txt $O   # this list (size of its previous version)
add D audits/evidence/retrofit/copy-text-screen.py $W/audits/evidence/retrofit/copy-text-screen.py
add D scripts/campaign_style_lint.py $W/scripts/campaign_style_lint.py
# E. library files the interfaces rest on
for f in $(cat $G/work/support.txt); do add E $f $W/$f; done
add E TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean $W/TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean   # source of a substantive undisclosed pair
# G. other library files in a reported pair (incidental overlaps only, <= 148 shared chars)
for f in $(cat $G/work/pair-incidental.txt); do add G $f $W/$f; done
# F. the rest of the screen populations (for a rerun of the screen); drop first if over budget
for f in $(cat $G/work/pop-rest.txt); do add F $f $W/$f; done
{
echo "# BUNDLE-FILES — ARM-extensions fill gate (audits/arm-extensions-fill-bundle.md)"
echo "# Repository paths, in bundle order. Lean sources are taken at the received commit 8c23f3bc"
echo "# (byte-identical at the tip dc891632). Sizes in bytes (sources as of $(date -u +%F))."
for sec in A B C D E G F; do
  case $sec in
    A) h="A. The pack, the standards, the response and proposal, the plan and the backlog (whole)";;
    B) h="B. The 73 added and the 8 modified Lean files (after state)";;
    C) h="C. The 8 modified files' before state (git show 069cde82:<path>)";;
    D) h="D. Evidence, logs, the pack author's scripts and the maintainer tools used";;
    E) h="E. Library files the interfaces rest on, and the source of the one substantive undisclosed pair outside them";;
    G) h="G. Other library files that appear in a reported pair; their pairs are incidental (drop SECOND, largest first)";;
    F) h="F. The rest of the two screen populations, only for a full rerun of the screen (DROP FIRST)";;
  esac
  n=$(awk -F'\t' -v s=$sec '$1==s' $T | wc -l | tr -d ' ')
  b=$(awk -F'\t' -v s=$sec '$1==s {t+=$3} END {print t+0}' $T)
  echo
  echo "## $h — $n files, $b bytes"
  awk -F'\t' -v s=$sec '$1==s {print $2"\t"$3}' $T
done
tot=$(awk -F'\t' '{t+=$3} END {print t}' $T); n=$(wc -l < $T | tr -d ' ')
noF=$(awk -F'\t' '$1!="F" {t+=$3} END {print t}' $T); nF=$(awk -F'\t' '$1!="F"' $T | wc -l | tr -d ' ')
noFG=$(awk -F'\t' '$1!="F" && $1!="G" {t+=$3} END {print t}' $T); nFG=$(awk -F'\t' '$1!="F" && $1!="G"' $T | wc -l | tr -d ' ')
echo
echo "## Estimate: $n files, $tot bytes of content (~$((tot/1000000)).$(( (tot%1000000)/100000 )) MB) plus ~80 bytes of section header per file."
echo "## Without section F: $nF files, $noF bytes (~$((noF/1000000)).$(( (noF%1000000)/100000 )) MB)."
echo "## Without sections F and G: $nFG files, $noFG bytes (~$((noFG/1000000)).$(( (noFG%1000000)/100000 )) MB)."
smallG=$(awk -F'\t' '$1=="G" && $3<60000 {t+=$3; n++} END {print n" files, "t" bytes"}' $T)
echo "## Recommendation (over the ~6 MB budget): ship A-E plus section G's files under 60 KB ($smallG); drop F first, then G's large files"
echo "## (Build/Catalog, CookLevin/Hardness, Build/Loop, ClassNP/SAT, TuringMachine/Universal, Robustness/SingleTape, Logspace/Mult), whose pairs are all incidental and are listed with line ranges in audits/logs/arm-fill-ledger.log."
} > $O
