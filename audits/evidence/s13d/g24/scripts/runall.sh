#!/usr/bin/env bash
# Re-run every check of the §13d G2–G4 statement gate (rebuild at the tip) and write the logs.
# Read-only: `lean` only through tools/leanelab.sh (no -o, no olean written), python3 -I only,
# read-only git (`rev-parse`, `diff --name-only`; the base tree is a `git archive` export).
# Usage: bash runall.sh <S>
#   base tree  <OUT>/base  = `git archive f2d48ad5` (Lean content = 1b6b972c), its .lake a symlink to
#              the packages of <S>/wt-g24 (same lake-manifest); snapshot <S>/oleans-lb6.
S="$1"; O="$S/gate-g24"; WT="$O/base"; GW="$S/wt-g24"; REV=f2d48ad5; OL="$S/oleans-lb6"
SC="$O/scripts"; B=TCSlib/Complexity/TuringMachine/Build; L="$O/landed/$B"
el() { bash "$S/tools/leanelab.sh" "$WT" "$OL" "$1" 2>&1; }
san() { sed "s|$O/|<OUT>/|g; s|$S/|<S>/|g"; }
summ() { # output exit
  local e w s
  e=$(grep -c ': error' <<<"$1"); w=$(grep -c ': warning' <<<"$1")
  s=$(grep -c "declaration uses 'sorry'" <<<"$1")
  echo "  exit $2 | errors $e | warnings $w | of which \`declaration uses 'sorry'\` $s | other warnings $((w - s))"
}
sorried() { grep "declaration uses 'sorry'" <<<"$1" | sed -E 's/.*:([0-9]+):[0-9]+: warning.*/\1/' |
  while read -r n; do sed -n "${n}p" "$2" | sed -E 's/^(theorem|def|lemma) ([^ ]+).*/\2/'; done | tr '\n' ' '; }
wnorm() { grep ': warning' <<<"$1" | sed -E 's/^[^:]*:[0-9]+:[0-9]+: //' | sort; }

bash "$SC/mkunit.sh" "$O"
python3 -I "$SC/mkprobes.py" "$O" >/dev/null
rm -rf "$O/landed"
python3 -I "$SC/mklanded.py" "$O/G24Statements.lean" "$WT" "$O/landed" > "$O/work/mklanded.out"
python3 -I "$SC/mklanded_zone.py" "$WT" "$O/parts/Z.body" "$L/Zone.lean" "$O/parts/zone_imports.txt" \
  "$O/parts/zone_landed_doc.txt" > "$O/work/mklanded_zone.out"
python3 -I "$SC/mklanded_catalog.py" "$WT" "$O/parts" "$O/landed" > "$O/work/mklanded_catalog.out"
python3 -I "$SC/mkfacade.py" "$WT" "$O/landed/TCSlib/Complexity/TuringMachine.lean" > /dev/null
python3 -I "$SC/mkchain.py" "$O" "$O/work/LandedChain.lean" > "$O/work/mkchain.out"
python3 -I "$SC/mkcatchain.py" "$L/Catalog.lean" "$L/Contract/Catalog.lean" "$O/work/CatChain.lean" > /dev/null
python3 -I "$SC/mkcatchain.py" "$WT/$B/Catalog.lean" "$WT/$B/Contract/Catalog.lean" "$O/work/CatChainBase.lean" > /dev/null

HDR="Tool: \`bash <S>/tools/leanelab.sh <OUT>/base <S>/oleans-lb6 <file>\` (direct \`lean\`, no \`-o\`, no olean
written). Base: <OUT>/base, a read-only \`git archive\` export of $(git -C "$GW" rev-parse --short $REV) (the local
\`origin/complexity/arora-barak-ch3-4\`; its Lean files equal 1b6b972c's: PRs #92 and #93 merged); its \`.lake\` is
a symlink to <S>/wt-g24's packages (same \`lake-manifest.json\`). Snapshot: \`oleans-lb6\`. Toolchain:
\`$(cat "$WT/lean-toolchain")\`. <OUT> is the gate's output directory; <S> the scratchpad. Run: $(date -u '+%Y-%m-%d %H:%M UTC')."

# ---------- cut checks, landed forms, the restructure
{
echo "# §13d G2–G4 statement gate: cut checks and landed forms"; echo; echo "$HDR"; echo
echo "\`python3 -I <OUT>/scripts/cutcheck.py <OUT>/G24Statements.lean <OUT>/base <OUT>/cut\` (the C1 and"
echo "stage-2 gates' script, verbatim) writes, for each part, a file holding the imports of the part's import"
echo "closure and the bodies of the parts in that closure, in file order. Each is elaborated on its own."
echo '```'
rm -rf "$O/cut"; (cd "$O" && python3 -I "$SC/cutcheck.py" "$O/G24Statements.lean" "$WT" "$O/cut") | san
echo '```'
for f in "$O"/cut/*.check.lean; do out=$(el "$f"); ex=$?
  echo "* \`$(basename "$f")\` ($(wc -l < "$f" | tr -d ' ') lines):"; summ "$out" "$ex"
  echo "  sorried: $(sorried "$out" "$f")"
  grep ': error' <<<"$out" | san | sed 's/^/    /'
done
echo
echo "## Landed forms (\`<OUT>/landed/\`)"
echo
echo "\`mklanded.py\` (C1 gate, verbatim) writes the new modules; \`mklanded_zone.py\` the retirements, the"
echo "promotion and the narrowed imports of \`Build/Zone.lean\` (retire.log); \`mklanded_catalog.py\` the"
echo "restructured \`Build/Catalog.lean\` and \`Build/Contract/Catalog.lean\` (freeze below); \`mkfacade.py\` the"
echo "facade. Every edit is an asserted, content-anchored replacement or insertion."
echo '```'; san < "$O/work/mklanded.out"; san < "$O/work/mklanded_zone.out"; san < "$O/work/mklanded_catalog.out"
san < "$O/work/mkchain.out"; echo '```'
out=$(el "$L/Zone.lean"); ex=$?
echo "* \`landed/.../Build/Zone.lean\` (standalone, narrowed imports: $(grep '^import' "$L/Zone.lean" | tr '\n' ' ')):"
summ "$out" "$ex"; echo "  sorried: $(sorried "$out" "$L/Zone.lean")"
out=$(el "$O/work/LandedChain.lean"); ex=$?
echo "* \`work/LandedChain.lean\`: the landed \`Zone.lean\` (narrowed imports) plus the imports of \`ZoneTape\` and"
echo "  \`ZoneRebalance\`, then those two landed modules' bodies, in one file:"
summ "$out" "$ex"; echo "  sorried: $(sorried "$out" "$O/work/LandedChain.lean")"
grep ': error' <<<"$out" | san | sed 's/^/    /'
t0=$(date +%s); outC=$(el "$L/Catalog.lean"); exC=$?; t1=$(date +%s)
echo "* \`landed/.../Build/Catalog.lean\` (standalone, $(wc -l < "$L/Catalog.lean" | tr -d ' ') lines, $((t1 - t0)) s):"
summ "$outC" "$exC"; echo "  sorried: $(sorried "$outC" "$L/Catalog.lean")"
grep ': error' <<<"$outC" | san | sed 's/^/    /'
cp "$WT/$B/Catalog.lean" "$O/work/Catalog_base.lean"
outB=$(el "$O/work/Catalog_base.lean"); exB=$?
echo "* baseline: the base's \`Build/Catalog.lean\` (a byte copy), standalone:"; summ "$outB" "$exB"
echo "  warnings of the landed file minus the baseline's (messages, line numbers dropped):"
diff <(wnorm "$outB") <(wnorm "$outC") | grep '^[<>]' | sed 's/^/    /'
outK=$(el "$O/work/CatChain.lean"); exK=$?
echo "* \`work/CatChain.lean\`: the landed \`Build/Catalog.lean\` with the import of \`Build/Contract/Basic\`, then the"
echo "  landed \`Build/Contract/Catalog.lean\`'s body (re-pointed \`clearTM_contract\`, its frames and trajectory,"
echo "  the shared constructor and the G2 contracts), in one file:"
summ "$outK" "$exK"; echo "  sorried: $(sorried "$outK" "$O/work/CatChain.lean")"
grep ': error' <<<"$outK" | san | sed 's/^/    /'
echo "  warnings minus the base Catalog's: $(diff <(wnorm "$outB") <(wnorm "$outK") | grep -c '^[<>]') lines (the 2 sorries expected)"
cp "$WT/$B/Zone.lean" "$O/work/Zone_base.lean"
out=$(el "$O/work/Zone_base.lean"); ex=$?
echo "* baseline: the base's \`Build/Zone.lean\` (a byte copy), standalone:"; summ "$out" "$ex"
} > "$O/cutcheck.log"

# ---------- the freeze of the restructured Catalog files
{
echo "# §13d G2–G4 statement gate: freeze of the restructured \`Build/Catalog.lean\` and \`Build/Contract/Catalog.lean\`"
echo; echo "$HDR"; echo
echo "\`<OUT>/scripts/freeze.py <base file> <landed file>\`: every declaration's statement (up to the top-level"
echo "\`:=\`/\`where\`, comments stripped) and whole comment-stripped text, base against landed. The user's rule:"
echo "every existing public statement unchanged apart from definitional restatements."
for f in Catalog Contract/Catalog; do
  echo; echo "## \`Build/$f.lean\`"; echo '```'
  python3 -I "$SC/freeze.py" "$WT/$B/$f.lean" "$L/$f.lean" | san; echo '```'
done
echo
echo "## The five body changes in \`Build/Catalog.lean\` and the three in \`Build/Contract/Catalog.lean\`"
echo
echo "Each changed declaration, base → landed (comment-stripped, blank lines dropped; \`freeze.py --show\`):"
for f in Catalog Contract/Catalog; do
  echo; echo "### \`Build/$f.lean\`"; echo '```diff'
  python3 -I "$SC/freeze.py" "$WT/$B/$f.lean" "$L/$f.lean" --show | grep -v 'old declarations' | san
  echo '```'
done
echo
echo "## Downstream uses of the restated definitions (whole-word, every \`.lean\` file of the base tree)"
echo
echo "A downstream proof could depend on the old table only by unfolding \`copyTM\`/\`transferTM\` by name"
echo "(\`simp\`, \`unfold\`, \`rw\`, \`delta\`, an equation lemma); \`change\` and applications are definitional."
echo '```'
(cd "$WT" && grep -rnw --include='*.lean' -E 'copyTM|transferTM|clearTM_contract' TCSlib |
  grep -v "^$B/Catalog.lean:\|^$B/Contract/Catalog.lean:") > "$O/work/downstream_uses.txt"
echo "$(wc -l < "$O/work/downstream_uses.txt" | tr -d ' ') lines in $(cut -d: -f1 "$O/work/downstream_uses.txt" | sort -u | wc -l | tr -d ' ') files;"
echo "of which name the definitions inside simp/unfold/rw/delta or an equation lemma:"
hits=$(grep -E 'simp|unfold|rw \[|delta|\.eq_[0-9]' "$O/work/downstream_uses.txt")
if [ -n "$hits" ]; then san <<<"$hits"; else echo "  (none)"; fi
echo "kinds of the other lines:"
sed -E 's/^[^:]*:[0-9]+://' "$O/work/downstream_uses.txt" | sed -E 's/^ +//' | cut -d' ' -f1 | sort | uniq -c | sort -rn | head -12
echo '```'
} > "$O/freeze.log"

# ---------- axioms
{
echo "# §13d G2–G4 statement gate: axiom prints"; echo; echo "$HDR"; echo
echo "\`<OUT>/work/AxProbe.lean\` is a copy of the unit followed by \`#print axioms\` for every public"
echo "declaration (\`<OUT>/scripts/mkaxprobe.py\`); \`AxFit.lean\` the fit probe with its own declarations;"
echo "\`AxChain.lean\` the landed zone chain; \`AxCatBase.lean\`/\`AxCatAfter.lean\` the base and landed Catalog chains"
echo "with every public declaration of both Catalog files (\`<OUT>/scripts/mkaxcat.py\`). Evidence only."
python3 -I "$SC/mkaxprobe.py" "$O/G24Statements.lean" "$O/work/AxProbe.lean"
out=$(el "$O/work/AxProbe.lean"); ex=$?
summ "$out" "$ex"
echo '```'; grep -v "declaration uses 'sorry'" <<<"$out" | san; echo '```'
{ cat "$O/probes/G24FitProbe.lean"; echo; echo "-- Axiom probe (evidence only)."
  for n in stopContract zoneTrackStepData trackStep_fit two_pow_eq_succ_sum amortized_le run_cost_le; do
    echo "#print axioms Turing.G24Fit.$n"; done; } > "$O/work/AxFit.lean"
out=$(el "$O/work/AxFit.lean"); ex=$?
echo; echo "Fit probe:"; summ "$out" "$ex"
echo '```'; grep -v "declaration uses 'sorry'" <<<"$out" | san; echo '```'
{ cat "$O/work/LandedChain.lean"; echo; echo "-- Axiom probe (evidence only)."
  for n in zoneCascadeRight_frame zoneRebalance_frame zoneRebalancePost_frames zoneCascadeRight_home \
           zoneTrackTape_rebalance_right exists_zoneRebalanceTM; do echo "#print axioms Turing.$n"; done
} > "$O/work/AxChain.lean"
out=$(el "$O/work/AxChain.lean"); ex=$?
echo; echo "The landed zone chain (\`work/LandedChain.lean\`), where the promoted frame lemma has its existing proof:"
summ "$out" "$ex"
echo '```'; grep -v "declaration uses 'sorry'" <<<"$out" | san; echo '```'
echo
echo "## The restructured Catalog files, before and after"
python3 -I "$SC/mkaxcat.py" "$O/work/CatChainBase.lean" "$O/work/AxCatBase.lean" "$WT/$B/Catalog.lean" "$WT/$B/Contract/Catalog.lean"
python3 -I "$SC/mkaxcat.py" "$O/work/CatChain.lean" "$O/work/AxCatAfter.lean" "$L/Catalog.lean" "$L/Contract/Catalog.lean"
el "$O/work/AxCatBase.lean" > "$O/work/AxCatBase.out"; e1=$?
el "$O/work/AxCatAfter.lean" > "$O/work/AxCatAfter.out"; e2=$?
echo "before: exit $e1, errors $(grep -c ': error' "$O/work/AxCatBase.out"); after: exit $e2, errors $(grep -c ': error' "$O/work/AxCatAfter.out")"
echo '```'; python3 -I "$SC/axcompare.py" "$O/work/AxCatBase.out" "$O/work/AxCatAfter.out"; echo '```'
echo "Full prints: \`work/AxCatBase.out\`, \`work/AxCatAfter.out\` (attached as \`axioms-catalog-{before,after}.txt\`)."
} > "$O/axioms.log"
grep "axioms" "$O/work/AxCatBase.out" | san > "$O/axioms-catalog-before.txt"
grep "axioms" "$O/work/AxCatAfter.out" | san > "$O/axioms-catalog-after.txt"

# ---------- names
{
echo "# §13d G2–G4 statement gate: name screen"; echo; echo "$HDR"; echo
echo "Against every declaration of the base tree (PRs #92 and #93 merged), and the pending statement units"
echo "of the base: MIG-1, the C1 assembly, the H1 harvest, the B5a canonizer overlay, RD-2 and stage 2."
echo '```'
python3 -I "$SC/names_c1.py" "$O/G24Statements.lean" "$WT" \
  "$WT/audits/evidence/mig1/gate/MIG1Statements.lean.txt" "$WT/audits/evidence/c1/assembly/C1Assembly.lean.txt" \
  "$WT/audits/evidence/h1harv/H1Harvest.lean.txt" "$WT/audits/evidence/b5a-canon-cont3/CanonCont3Overlay.lean.txt" \
  "$WT/audits/evidence/rd2-gate/FormulaKitGate.lean.txt" "$WT/audits/evidence/stage2-gate/Stage2.lean.txt" \
  "$WT/audits/evidence/stage2-gate/LanguageExtensions.lean.txt" 2>&1 | san
echo '```'
printf 'namespace Turing\ndef zoneSide := 0\ntheorem zoneBase_succ : True := trivial\nend Turing\n' > "$O/work/screen_ctrl.lean"
echo "Positive control (\`<OUT>/work/screen_ctrl.lean\` declares two existing full names):"
python3 -I "$SC/names_c1.py" "$O/work/screen_ctrl.lean" "$WT" > "$O/work/screen_ctrl.out"
echo '```'; san < "$O/work/screen_ctrl.out"; echo '```'
} > "$O/names.log"

# ---------- retirements
{
echo "# §13d G2–G4 statement gate: retirements"; echo; echo "$HDR"; echo
echo "## 1. Consumers of the retired declarations"
echo
echo "For each name: Lean files of the base's \`TCSlib\` tree (and \`TCSlib.lean\`) other than"
echo "\`Build/Zone.lean\` that mention it as a whole word, and the count of non-Lean files of the campaign"
echo "checkout (<S>/wt-g24, records) that mention it."
echo '```'
for n in zoneCellBits zoneCellOf zoneCellOf_bits zoneTape zoneTape_empty zoneTape_blank_outside \
         zoneTape_homeWrite zoneStageWord zoneStageWord_length zoneStageWord_getElem zoneStageSlot \
         zoneStage_rightWindow zoneStage_leftWindow zoneStage_window_bounds exists_zoneShiftInTM \
         exists_zoneShiftOutTM; do
  lean=$(cd "$WT" && grep -rlw --include='*.lean' "$n" TCSlib TCSlib.lean | grep -v 'Build/Zone.lean$' | tr '\n' ' ')
  rec=$(cd "$GW" && grep -rlw --exclude-dir=.lake --exclude-dir=.git --exclude='*.lean' "$n" . | wc -l | tr -d ' ')
  printf '%-26s Lean consumers outside Zone: %s | non-Lean files mentioning it: %s\n' "$n" "${lean:-none}" "$rec"
done
echo '```'
echo
echo "Kept pure declarations whose only consumers retire (no consumer remains in the layer; open question 6):"
echo '```'
for n in zoneSlot zoneIndex zoneIndex_eq_iff; do
  c=$(grep -cw "$n" "$L/Zone.lean"); printf '%-18s occurrences in the landed Zone.lean (definition included): %s\n' "$n" "$c"
done
echo '```'
echo
echo "## 2. The landed \`Build/Zone.lean\`: what changed (\`<OUT>/scripts/mklanded_zone.py\`)"
echo
echo "Comment-stripped statement comparison of the base's file (old) against the landed file (new),"
echo "\`<OUT>/scripts/sigdiff.py\`:"
echo '```'; python3 -I "$SC/sigdiff.py" "$WT/$B/Zone.lean" "$L/Zone.lean" | san; echo '```'
echo
echo "Unified diff, old → new, with the appended Part Z elided after its first line:"
echo '```diff'
diff -u "$WT/$B/Zone.lean" "$L/Zone.lean" | sed 's|^--- .*|--- base/Build/Zone.lean|; s|^+++ .*|+++ landed/Build/Zone.lean|' |
  awk '/^\+\/-! ## The §13d additions/ {print; print "+[… Part Z, verbatim from the unit, minus its sorried copy of zoneCascadeRight_frame …]"; skip=1; next}
       skip && /^\+end Turing$/ {skip=0} !skip'
echo '```'
echo
echo "## 3. The two retired rows against their replacements"
echo
echo '```'
python3 -I - "$WT/$B/Zone.lean" "$O/G24Statements.lean" <<'PY'
import re, sys
for path, names in [(sys.argv[1], ["exists_zoneShiftInTM", "exists_zoneShiftOutTM"]),
                    (sys.argv[2], ["exists_zoneRebalanceTM", "exists_zoneExtendTM"])]:
    src = open(path, encoding="utf-8").read()
    for n in names:
        i = src.index(f"theorem {n}")
        j = src.index(":= by", i)
        stmt = " ".join(src[i:j].split())
        print(f"{n}:\n  {stmt[:900]}{' …' if len(stmt) > 900 else ''}\n")
PY
echo '```'
echo
echo "## 4. The facade (\`mkfacade.py\`), rebased on PR #92's additions"
echo '```diff'
diff -u "$WT/TCSlib/Complexity/TuringMachine.lean" "$O/landed/TCSlib/Complexity/TuringMachine.lean" |
  sed 's|^--- .*|--- base/TuringMachine.lean|; s|^+++ .*|+++ landed/TuringMachine.lean|'
echo '```'
} > "$O/retire.log"

# ---------- main log
{
echo "# §13d G2–G4 statement gate: elaboration log"; echo; echo "$HDR"; echo
echo "In the repository the files map as: <OUT>/G24Statements.lean -> audits/evidence/s13d/g24/"
echo "G24Statements.lean.txt; <OUT>/probes/<P>.lean -> audits/evidence/s13d/g24/probes/<P>.lean.txt;"
echo "<OUT>/landed/<path> -> audits/evidence/s13d/g24/landed/<path>.txt; <OUT>/scripts/<x> and the part"
echo "files <OUT>/parts/<x> -> audits/evidence/s13d/g24/scripts/<x>, parts/<x>; <OUT>/G24-design.md ->"
echo "audits/evidence/s13d/g24/G24-design.md; <OUT>/{cutcheck,freeze,axioms,names,retire}.log and this file ->"
echo "audits/logs/s13d-g24-statements-{cutcheck,freeze,axioms,names,retire,elaboration}.log. <OUT>/scripts/lint.py"
echo "is scripts/campaign_style_lint.py with ROOT from its second argument; style_lint_copy.py is"
echo "scripts/style_lint.py with ROOT the working directory. The first build's records are under"
echo "<OUT>/work/superseded-r0/ (built at 759471be with oleans-lm0b)."
echo
echo "## 1. The unit"
out=$(el "$O/G24Statements.lean"); ex=$?
echo; echo "### G24Statements.lean ($(wc -l < "$O/G24Statements.lean" | tr -d ' ') lines; SHA-256 $(shasum -a 256 "$O/G24Statements.lean" | cut -d' ' -f1))"
summ "$out" "$ex"; echo "  sorried: $(sorried "$out" "$O/G24Statements.lean")"
echo '```'; san <<<"$out"; echo '```'
echo
echo "## 2. Cut checks, landed forms, freeze, axioms, names, retirements"
echo
echo "Separate logs (same run): \`cutcheck.log\`, \`freeze.log\`, \`axioms.log\`, \`names.log\`, \`retire.log\`. Summary:"
echo '```'
grep -E '^\* |exit [0-9]' "$O/cutcheck.log" | san
grep -E 'old declarations' "$O/freeze.log"
grep -E 'unchanged|gain sorryAx' "$O/axioms.log"
grep -E '^[0-9]\.|declarations in the unit' "$O/names.log" | cut -c1-150
echo "positive control: $(grep -c '   CLASH' "$O/work/screen_ctrl.out") clashes caught (of 2 planted)"
echo "unit, fit and zone-chain axiom prints: $(sed -n '1,/## The restructured/p' "$O/axioms.log" | grep -c "depends on axioms\|does not depend") lines; with sorryAx: $(sed -n '1,/## The restructured/p' "$O/axioms.log" | grep -c 'sorryAx')"
echo '```'
echo
echo "## 3. Sanity probes (evidence only; not landing material)"
out=$(el "$O/probes/G24Sanity.lean"); ex=$?
n=$(grep -c '^example' "$O/probes/G24Sanity.lean")
echo; echo "### probes/G24Sanity.lean: the unit, one extra Mathlib import, and $n \`example\`s"; summ "$out" "$ex"
echo '```'; grep -v "declaration uses 'sorry'" <<<"$out" | san; echo "(the sorry warnings are those of the unit)"; echo '```'
echo
echo "Negative controls (deliberately false copies of probe facts; each must fail):"
neg() { { cat "$O/G24Statements.lean"; echo; echo "open Turing"; cat; } > "$O/work/$1.lean"; }
neg neg1 <<'EOF'
def zA : ZoneContents 1 where
  home := some true
  left := fun _ => [some false]
  right := fun _ => [some true]
  left_le := by decide
  right_le := by decide
example : (zoneRebalance true zA).right ⟨0, by decide⟩ = [some true] := by decide
EOF
neg neg2 <<'EOF'
example : zoneStart 1 = 4 := by decide
EOF
neg neg3 <<'EOF'
example : zonedTape (fun t : Fin 1 => (ZoneContents.empty 0).extend) 3 =
    some (.inr fun _ => some none) := by decide
EOF
neg neg4 <<'EOF'
example : zoneRebalanceIndex true (0 : Fin 1) (zoneExtendData ⟨0, fun _ => ZoneContents.empty 0⟩) = 1 := by
  decide
EOF
for n in neg1 neg2 neg3 neg4; do out=$(el "$O/work/$n.lean"); ex=$?
  echo "* \`$n\`: exit $ex, errors $(grep -c ': error' <<<"$out"): $(grep ': error' <<<"$out" | san | head -1 | sed -E 's/.*error[^:]*: //' | cut -c1-90)"
done
echo "  (neg1: the right zone keeps its cell after a right move; neg2: zone 1 starts at 4; neg3: the"
echo "  extension's outer cell holds a virtual blank; neg4: the retried scan is 1.)"
echo
echo "## 4. The fit probe (evidence only)"
out=$(el "$O/probes/G24FitProbe.lean"); ex=$?
echo; echo "### probes/G24FitProbe.lean: the unit, two extra imports, and the fit"; summ "$out" "$ex"
echo '```'; grep -v "declaration uses 'sorry'" <<<"$out" | san; echo "(the sorry warnings are those of the unit; the fit's own declarations have none: axioms.log)"; echo '```'
echo
echo "## 5. Style lint (copies of the five landed modules and the facade in <OUT>/work/lintroot)"
rm -rf "$O/work/lintroot"; mkdir -p "$O/work/lintroot"; cp -R "$O/landed/TCSlib" "$O/work/lintroot/"
find "$O/work/lintroot" -name '*.deleted.txt' -delete
cp "$WT/$B/Contract.lean" "$O/work/lintroot/$B/"   # the intermediate facade, so the facade rule sees it
echo; echo "\`scripts/campaign_style_lint.py\` (as <OUT>/scripts/lint.py; the base's \`Build/Contract.lean\` facade is copied"
echo "in as well, so that the facade rule sees the intermediate facade of \`Build/Contract/Catalog.lean\`):"
echo '```'; (cd "$O/work/lintroot" && python3 -I "$SC/lint.py" TCSlib "$O/work/lintroot") | san; echo '```'
rm -rf "$O/work/lintbase"; mkdir -p "$O/work/lintbase/$B/Contract"
cp "$WT/$B/Zone.lean" "$O/work/lintbase/$B/"; cp "$WT/$B/Contract/Catalog.lean" "$O/work/lintbase/$B/Contract/"
echo; echo "Baseline, \`scripts/style_lint.py\` on copies of the base's \`Build/Zone.lean\` and \`Build/Contract/Catalog.lean\`:"
echo '```'
(cd "$O/work/lintbase" && python3 -I "$SC/style_lint_copy.py" $B/Zone.lean $B/Contract/Catalog.lean 2>&1) | san
echo '```'
echo; echo "\`scripts/style_lint.py\` (as <OUT>/scripts/style_lint_copy.py), on the four zone and contract files:"
echo '```'
(cd "$O/work/lintroot" && python3 -I "$SC/style_lint_copy.py" $B/Zone.lean $B/ZoneTape.lean \
  $B/ZoneRebalance.lean $B/Contract/Catalog.lean 2>&1) | san
echo '```'
echo
echo "## 6. Line widths (characters, not bytes)"
echo '```'
python3 -I "$SC/widths.py" "$O/G24Statements.lean" "$O/probes/G24Sanity.lean" "$O/probes/G24FitProbe.lean" \
  "$L/Zone.lean" "$L/ZoneTape.lean" "$L/ZoneRebalance.lean" "$L/Contract/Catalog.lean" \
  "$O/landed/TCSlib/Complexity/TuringMachine.lean" | san
echo "(landed Build/Catalog.lean: $(python3 -I "$SC/widths.py" "$L/Catalog.lean" | tail -1); the base's: $(python3 -I "$SC/widths.py" "$WT/$B/Catalog.lean" | tail -1))"
echo '```'
echo
echo "## 7. Cited names: every backticked identifier of the unit's comments, as \`#check @…\`"
python3 -I "$SC/cited.py" "$O/G24Statements.lean" > "$O/work/cited_unit.txt"
{ cat "$O/G24Statements.lean"; echo
  echo "open Turing Turing.FinTM Turing.MultiTapeTM Turing.Contract"
  while read -r t; do echo "#check @$t"; done < "$O/work/cited_unit.txt"; } > "$O/work/cite_unit.lean"
out=$(el "$O/work/cite_unit.lean")
echo; echo "$(wc -l < "$O/work/cited_unit.txt" | tr -d ' ') tokens; those that do not resolve:"
echo '```'; grep ': error' <<<"$out" | sed -E 's/.*error[^:]*: //' | sort | uniq | tr '\n' ' ' | fold -s -w 98; echo; echo '```'
echo
echo "## 8. Statement correspondence"
echo
echo "The unit's sorried \`Turing.zoneCascadeRight_frame\` against the base's private lemma of that name"
echo "(comment-stripped statements, \`private\` removed):"
echo '```'
python3 -I - "$SC" "$WT/$B/Zone.lean" "$O/G24Statements.lean" <<'PY'
import sys
sys.path.insert(0, sys.argv[1])
from sigdiff import decls
a, b = decls(sys.argv[2]), decls(sys.argv[3])
n = "Turing.zoneCascadeRight_frame"
sa = a[n][0].replace("private ", "", 1)
sb = b[n][0]
print(f"{n}: unit statement {'IDENTICAL to' if sa == sb else 'DIFFERS from'} the private lemma's")
if sa != sb:
    print("  old: " + sa); print("  new: " + sb)
PY
echo '```'
echo
echo "## 9. Downstream and the sequencing with MIG-1 stage S"
echo '```'
python3 -I "$S/tools/imports.py" "$WT" "$O/work/importgraph.json" >/dev/null
python3 -I - "$O/work/importgraph.json" <<'PY'
import json, sys
g = json.load(open(sys.argv[1]))
def closure(m, seen=None):
    seen = set() if seen is None else seen
    if m in seen: return seen
    seen.add(m)
    for d in g.get(m, []):
        if d in g: closure(d, seen)
    return seen
B = "TCSlib/Complexity/TuringMachine/Build/"
for t in ["Zone", "Catalog", "Contract/Catalog"]:
    direct = sorted(m for m, ds in g.items() if B + t in ds)
    down = [m for m in g if m != B + t and B + t in closure(m)]
    print(f"{t}: {len(direct)} direct importers; downstream closure {len(down)} modules"
          + (f"; direct: {direct}" if len(direct) <= 3 else ""))
F = "TCSlib/Complexity/TuringMachine"
for d in ["Build/Catalog", "Build/Embed", "Build/Seam", "Simulation"]:
    print(f"  the facade imports {d} directly: {F + '/' + d in g.get(F, [])}")
PY
echo "(downstream uses of copyTM, transferTM and clearTM_contract: freeze.log, last section)"
echo '```'
echo
echo "## 10. Nothing in the checkout was changed"
echo
echo "All outputs are under <OUT> (the base tree included). No lake or elan command was run, and no fetch;"
echo "git ran read-only (\`rev-parse\`, \`diff --name-only\`, \`archive\`); \`lean\` ran only through"
echo "\`tools/leanelab.sh\`, which writes no olean; Python ran only as \`python3 -I\`. \`git status --short\` of the"
echo "campaign checkout after the run:"
echo '```'; git -C "$GW" status --short | head; echo "(end)"; echo '```'
} > "$O/elaboration.log"
echo "wrote logs in $O"
