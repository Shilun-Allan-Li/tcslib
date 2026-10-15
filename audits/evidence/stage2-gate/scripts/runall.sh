#!/usr/bin/env bash
# Re-run every check of the stage-2 statement gate pack and write the elaboration log.
# Read-only: `lean` on each file against the olean snapshot (no -o), python3 -I for the scripts.
S="$1"; WT="$S/wt-g2"; OL="$S/oleans-f7"; O="$S/gate-stage2"; LOG="$O/elaboration.log"
el() { bash "$S/tools/leanelab.sh" "$WT" "$OL" "$1" 2>&1; }
san() { sed "s|$O/|<OUT>/|g; s|$S/|<S>/|g"; }
python3 -I "$O/work/mkprobes.py" "$O" >&2
summ() { # file output exit
  local e w s o
  e=$(grep -c ': error' <<<"$2"); w=$(grep -c ': warning' <<<"$2")
  s=$(grep -c "declaration uses 'sorry'" <<<"$2"); o=$(grep -c ': warning' <<<"$2" | awk -v s="$s" '{print $1 - s}')
  echo "  exit $3 | errors $e | warnings $w | of which \`declaration uses 'sorry'\` $s | other warnings $o"
}
{
echo "# Stage-2 statement gate: elaboration log"
echo
echo "Tool: \`bash <S>/tools/leanelab.sh <S>/wt-g2 <S>/oleans-f7 <file>\` (direct \`lean\`, no \`-o\`,"
echo "no olean written). Worktree: the read-only campaign-tip checkout \`wt-g2\`; olean snapshot"
echo "\`oleans-f7\` (all of TCSlib, \`TCSlib/Programs\` included, and Mathlib). Toolchain:"
echo "\`$(cat "$WT/lean-toolchain")\`. <OUT> is the pack's output directory; <S> the scratchpad."
echo "Run: $(date -u '+%Y-%m-%d %H:%M UTC')."
echo "In the repository the files map as: <OUT>/{Stage2,NDSlice,LanguageExtensions}.lean ->"
echo "audits/evidence/stage2-gate/<Name>.lean.txt; <OUT>/probes/<P>.lean ->"
echo "audits/evidence/stage2-gate/probes/<P>.lean.txt; <OUT>/work/<script> (cutcheck.py, stmtdiff.py,"
echo "names.py, cited.py, widths.py, mkprobes.py, runall.sh and the two probe tails) ->"
echo "audits/evidence/stage2-gate/scripts/<script>; <OUT>/work/lint.py is"
echo "scripts/campaign_style_lint.py with its ROOT line pointed at a copy of the three files."
echo
echo "## 1. The three proposed files"
for f in Stage2 NDSlice LanguageExtensions; do
  out=$(el "$O/$f.lean"); ex=$?
  echo; echo "### $f.lean ($(wc -l < "$O/$f.lean" | tr -d ' ') lines)"; summ "$f" "$out" "$ex"
  echo '```'; san <<<"$out"; echo '```'
done
echo
echo "## 2. Cut checks: each landing module of Stage2.lean in exactly its own import closure"
echo
echo "\`python3 -I <OUT>/work/cutcheck.py <OUT>/Stage2.lean <S>/wt-g2 <OUT>/work/cut\` writes, for"
echo "each part, a file holding the imports of the part's import closure and the bodies of the parts"
echo "in that closure, in file order (the method of \`scripts/vendor_afm26/closurecheck.py\`). Each is"
echo "elaborated on its own."
echo '```'
rm -rf "$O/work/cut"; (cd "$O/work" && python3 -I "$O/work/cutcheck.py" "$O/Stage2.lean" "$WT" "$O/work/cut") | san
echo '```'
for f in "$O"/work/cut/*.check.lean; do
  out=$(el "$f"); ex=$?
  echo "* \`$(basename "$f")\`:"; summ x "$out" "$ex"
done
echo
echo "## 3. Semantic sanity probes (evidence only; not landing material)"
for f in Stage2Sanity LanguageExtensionsSanity; do
  out=$(el "$O/probes/$f.lean"); ex=$?
  n=$(grep -c '^example' "$O/probes/$f.lean")
  echo; echo "### probes/$f.lean: the unit plus $n \`example\`s, each by \`rfl\`, \`decide\`, a term or a short tactic proof"
  summ x "$out" "$ex"
  echo '```'; san <<<"$out" | grep -v "declaration uses 'sorry'" ; echo "(the sorry warnings are those of the unit)"; echo '```'
done
echo
echo "Negative controls (deliberately false copies, deleted afterwards; each must fail):"
for n in neg1 neg2 neg3; do
  out=$(el "$O/work/$n.lean"); ex=$?
  echo "* \`$n\`: exit $ex, errors $(grep -c ': error' <<<"$out"): $(grep ': error' <<<"$out" | san | head -1 | cut -c1-120)"
done
echo "  (neg1: \`emit\` of a nonzero cell claimed to emit \`[false]\`; neg2: \`half\` of -3 claimed"
echo "  to be -1; neg3: \`inBitVal [false, true] 1\` claimed to be 0.)"
echo
echo "## 4. Style lint (\`scripts/campaign_style_lint.py\`, its ROOT pointed at a copy of the units)"
echo '```'
rm -rf "$O/work/lintroot"; mkdir -p "$O/work/lintroot/units"; cp "$O"/Stage2.lean "$O"/NDSlice.lean "$O"/LanguageExtensions.lean "$O/work/lintroot/units/"
(cd "$O/work" && python3 -I "$O/work/lint.py" units) | san
echo '```'
echo "The one WARN is Stage2.lean, an elaboration unit that lands as six modules (part sizes in the pack)."
echo
echo "## 5. Line widths (characters, not bytes)"
echo '```'
python3 -I "$O/work/widths.py" "$O/Stage2.lean" "$O/NDSlice.lean" "$O/LanguageExtensions.lean" | san
echo '```'
echo
echo "## 6. Name screen: the units' declarations against every declaration of TCSlib"
echo '```'
python3 -I "$O/work/names.py" "$O/Stage2.lean" "$O/NDSlice.lean" "$O/LanguageExtensions.lean" "$WT" | san
echo '```'
echo "Positive control: a file declaring \`WordRAM.startMem\` (the draft's name) and \`Light.Compiler.sim\`:"
echo '```'
python3 -I "$O/work/names.py" "$O/work/screen_ctrl.lean" "$WT" | san
echo '```'
echo
echo "## 7. Cited names: every backticked identifier of each unit's comments, as \`#check @…\`"
for spec in "Stage2:WordRAM Light Light.Compiler Turing Complexity" "NDSlice:Turing Turing.NDTM Turing.MultiTapeTM" "LanguageExtensions:Light Light.Compiler"; do
  f=${spec%%:*}; ops=${spec#*:}
  python3 -I "$O/work/cited.py" "$O/$f.lean" > "$O/work/cited_$f.txt"
  { cat "$O/$f.lean"; echo; echo "open $ops"; while read -r t; do echo "#check @$t"; done < "$O/work/cited_$f.txt"; } > "$O/work/cite_$f.lean"
  out=$(el "$O/work/cite_$f.lean")
  echo; echo "### $f: $(wc -l < "$O/work/cited_$f.txt" | tr -d ' ') tokens; those that do not resolve:"
  echo '```'; grep ': error' <<<"$out" | sed -E 's/.*error[^:]*: //' | sort | uniq | tr '\n' ' ' | fold -s -w 98; echo; echo '```'
done
echo
echo "## 8. Statement correspondence with the drafts (comment-stripped, whitespace-collapsed)"
echo
echo "\`python3 -I <OUT>/work/stmtdiff.py <draft> <proposed> [renames]\`: every declaration of the draft"
echo "against its counterpart (same name after the listed renames; names that one file qualifies and"
echo "the other opens are normalized; proofs, all \`sorry\`, removed). Docstrings are not compared."
echo
echo "### audits/evidence/stage2/Stage2Draft.lean.txt against Stage2.lean (rename startMem=initMem)"
echo '```'
(cd "$O/work" && python3 -I stmtdiff.py "$WT/audits/evidence/stage2/Stage2Draft.lean.txt" "$O/Stage2.lean" startMem=initMem) | san
echo '```'
echo
echo "### audits/evidence/stage2/ExtensionsDraft.lean.txt against LanguageExtensions.lean (rename XFits=Compiler.XFits)"
echo '```'
(cd "$O/work" && python3 -I stmtdiff.py "$WT/audits/evidence/stage2/ExtensionsDraft.lean.txt" "$O/LanguageExtensions.lean" XFits=Compiler.XFits) | san
echo '```'
echo
echo "NDSlice.lean has no draft counterpart: both of its theorems are new (NOTES.md §3.9 names the"
echo "lemma; design §15d records the need)."
} > "$LOG"
echo "wrote $LOG"
