#!/usr/bin/env bash
# Re-run every check of the C1 host-contracts statement gate and write the logs.
# Read-only: `lean` only through tools/leanelab.sh (no -o, no olean written), python3 -I only.
# Usage: bash runall.sh <S>   (S = the scratchpad; checkout wt-g5c1, snapshot oleans-f8)
S="$1"; WT="$S/wt-g5c1"; OL="$S/oleans-f8"; O="$S/gate-c1hosts"; SC="$O/scripts"
el() { bash "$S/tools/leanelab.sh" "$WT" "$OL" "$1" 2>&1; }
san() { sed "s|$O/|<OUT>/|g; s|$S/|<S>/|g"; }
summ() { # output exit
  local e w s
  e=$(grep -c ': error' <<<"$1"); w=$(grep -c ': warning' <<<"$1")
  s=$(grep -c "declaration uses 'sorry'" <<<"$1")
  echo "  exit $2 | errors $e | warnings $w | of which \`declaration uses 'sorry'\` $s | other warnings $((w - s))"
}
python3 -I "$SC/mkprobes.py" "$O" >&2
python3 -I "$SC/mkpatch.py" "$O/work/patch/a/TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean" \
  "$O/work/patch/b/TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean" >&2
(cd "$O/work/patch" && diff -u a/TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean \
  b/TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean > "$O/NTimeHierarchy-docstrings.patch")
HDR="Tool: \`bash <S>/tools/leanelab.sh <S>/wt-g5c1 <S>/oleans-f8 <file>\` (direct \`lean\`, no \`-o\`,
no olean written). Checkout: \`wt-g5c1\`, campaign commit 1781a230 (PR #84, fills-8), read-only.
Snapshot: \`oleans-f8\` (all of TCSlib at that commit). Toolchain: \`$(cat "$WT/lean-toolchain")\`.
<OUT> is the gate's output directory; <S> the scratchpad. Run: $(date -u '+%Y-%m-%d %H:%M UTC')."

# ---------- cut checks
{
echo "# C1 host contracts statement gate: cut checks"; echo; echo "$HDR"; echo
echo "\`python3 -I <OUT>/scripts/cutcheck.py <OUT>/C1Hosts.lean <S>/wt-g5c1 <OUT>/cut\` (the stage-2"
echo "gate's script, verbatim) writes, for each part, a file holding the imports of the part's import"
echo "closure and the bodies of the parts in that closure, in file order. Each is elaborated on its own."
echo '```'
rm -rf "$O/cut"; (cd "$O" && python3 -I "$SC/cutcheck.py" "$O/C1Hosts.lean" "$WT" "$O/cut") | san
echo '```'
for f in "$O"/cut/*.check.lean; do out=$(el "$f"); ex=$?
  echo "* \`$(basename "$f")\` ($(wc -l < "$f" | tr -d ' ') lines):"; summ "$out" "$ex"
  grep ': error' <<<"$out" | san | sed 's/^/    /'
done
echo
echo "## Landing modules as they would land (\`<OUT>/scripts/mklanded.py\` -> \`<OUT>/landed/\`)"
echo
echo "Each new module is the copyright block, its part's imports, the options and the part; the"
echo "addition to \`Nondeterministic.lean\` is the checkout's file with the extra import and the part"
echo "appended. A file is elaborated standalone only when every module it imports exists in the"
echo "snapshot; the other two import new modules and are covered by the cut checks above."
echo '```'
rm -rf "$O/landed"; python3 -I "$SC/mklanded.py" "$O/C1Hosts.lean" "$WT" "$O/landed" | san
echo '```'
for f in TCSlib/Complexity/TuringMachine/Nondeterministic.lean TCSlib/Complexity/TuringMachine/ChoiceReplay.lean \
         TCSlib/Complexity/TuringMachine/Build/InputWindow.lean TCSlib/Complexity/ClassNP/ExhaustiveReplay.lean; do
  out=$(el "$O/landed/$f"); ex=$?; echo "* \`landed/$f\` (standalone):"; summ "$out" "$ex"
done
echo "* \`landed/TCSlib/Complexity/TuringMachine/Build/NDHost.lean\`: not standalone (uses Part A)."
echo "* \`landed/TCSlib/Complexity/TuringMachine/NDCodeSimulator.lean\`: not standalone (imports ChoiceReplay)."
} > "$O/cutcheck.log"

# ---------- axioms
{
echo "# C1 host contracts statement gate: axiom prints"; echo; echo "$HDR"; echo
echo "\`<OUT>/work/AxProbe.lean\` is a copy of the unit followed by \`#print axioms\` for every public"
echo "declaration (\`<OUT>/scripts/mkaxprobe.py\`). The probe is evidence only."
python3 -I "$SC/mkaxprobe.py" "$O/C1Hosts.lean" "$O/work/AxProbe.lean" >/dev/null
out=$(el "$O/work/AxProbe.lean"); ex=$?
summ "$out" "$ex"
echo '```'; grep -v "declaration uses 'sorry'" <<<"$out" | san; echo '```'
} > "$O/axioms.log"

# ---------- freeze
{
echo "# C1 host contracts statement gate: freeze check of the NTimeHierarchy docstring patch"; echo; echo "$HDR"; echo
echo "a = the checkout's \`TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean\` (byte copy), b = a with"
echo "the patch applied by \`<OUT>/scripts/mkpatch.py\` (each replacement asserted to match exactly once)."
echo "SHA-256: a $(shasum -a 256 "$O/work/patch/a/TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean" | cut -d' ' -f1)"
echo "         checkout $(shasum -a 256 "$WT/TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean" | cut -d' ' -f1)"
echo "         b $(shasum -a 256 "$O/work/patch/b/TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean" | cut -d' ' -f1)"
echo "         patch $(shasum -a 256 "$O/NTimeHierarchy-docstrings.patch" | cut -d' ' -f1)"
echo '```'
(cd "$O/work/patch" && python3 -I "$SC/freeze.py" a/TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean \
  b/TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean); echo "freeze.py exit $?"
echo '```'
for f in a b; do out=$(el "$O/work/patch/$f/TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean"); ex=$?
  echo "* elaboration of $f:"; summ "$out" "$ex"; done
echo "* line widths of b (characters):"
python3 -I "$SC/widths.py" "$O/work/patch/b/TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean" | san | sed 's/^/    /'
echo "* line widths of a (characters):"
python3 -I "$SC/widths.py" "$O/work/patch/a/TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean" | san | sed 's/^/    /'
echo
echo "Names cited in b's comments, \`#check\`ed in the unit plus \`NTimeHierarchy\` and \`ClockLoop\`;"
echo "those that do not resolve:"
python3 -I "$SC/cited.py" "$O/work/patch/b/TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean" > "$O/work/cited_patch.txt"
python3 -I - "$O" <<'PY'
import sys
O = sys.argv[1]
unit = open(O + "/C1Hosts.lean", encoding="utf-8").read()
a = "import TCSlib.Complexity.ClassNP.NTIME\n"
assert unit.count(a) == 1
unit = unit.replace(a, a + "import TCSlib.Complexity.Diagonalization.NTimeHierarchy\n"
                    "import TCSlib.Complexity.TimeHierarchy.ClockLoop\n")
toks = [l.strip() for l in open(O + "/work/cited_patch.txt", encoding="utf-8") if l.strip()]
with open(O + "/work/cite_patch.lean", "w", encoding="utf-8") as f:
    f.write(unit + "\nopen Turing Complexity\n" + "".join(f"#check @{t}\n" for t in toks))
PY
out=$(el "$O/work/cite_patch.lean")
echo '```'; grep ': error' <<<"$out" | sed -E 's/.*error[^:]*: //' | sort | uniq | tr '\n' ' ' | fold -s -w 98; echo; echo '```'
} > "$O/freeze.log"

# ---------- names
{
echo "# C1 host contracts statement gate: name screen"; echo; echo "$HDR"; echo
echo '```'
python3 -I "$SC/names_c1.py" "$O/C1Hosts.lean" "$WT" "$WT/audits/evidence/b6hosts/B6HostsDraft.lean.txt" \
  "$WT/audits/evidence/stage2-gate/NDSlice.lean.txt" "$WT/audits/evidence/stage2-gate/Stage2.lean.txt" \
  "$WT/audits/evidence/stage2-gate/LanguageExtensions.lean.txt" "$WT/audits/evidence/h2/StepBlockDraft.lean.txt" \
  "$WT/audits/evidence/mig0/Contract-proposed-r2.lean.txt" "$WT/audits/evidence/c1/C1HostsDraft.lean.txt" | san
echo '```'
printf 'namespace Turing\nnamespace MultiTapeTM\ndef relabelState := 0\nend MultiTapeTM\ntheorem exists_timed_universal_NDTM : True := trivial\nend Turing\n' > "$O/work/screen_ctrl.lean"
echo "Positive control (\`<OUT>/work/screen_ctrl.lean\` declares two existing full names):"
echo '```'; python3 -I "$SC/names_c1.py" "$O/work/screen_ctrl.lean" "$WT" | san; echo '```'
} > "$O/names.log"

# ---------- main log
{
echo "# C1 host contracts statement gate: elaboration log"; echo; echo "$HDR"; echo
echo "In the repository the files map as: <OUT>/C1Hosts.lean -> audits/evidence/c1/gate/C1Hosts.lean.txt;"
echo "<OUT>/NTimeHierarchy-docstrings.patch -> audits/evidence/c1/gate/NTimeHierarchy-docstrings.patch;"
echo "<OUT>/probes/C1HostsSanity.lean -> audits/evidence/c1/gate/probes/C1HostsSanity.lean.txt;"
echo "<OUT>/scripts/<x>.py and runall.sh -> audits/evidence/c1/gate/scripts/<x>; probe_tail.lean ->"
echo "audits/evidence/c1/gate/scripts/probe_tail.lean.txt; <OUT>/{cutcheck,axioms,freeze,names}.log ->"
echo "audits/logs/c1-hosts-statements-{cutcheck,axioms,freeze,names}.log; this file ->"
echo "audits/logs/c1-hosts-statements-elaboration.log. <OUT>/scripts/lint.py is"
echo "scripts/campaign_style_lint.py with ROOT taken from its second argument."
echo
echo "## 1. The unit"
out=$(el "$O/C1Hosts.lean"); ex=$?
echo; echo "### C1Hosts.lean ($(wc -l < "$O/C1Hosts.lean" | tr -d ' ') lines; SHA-256 $(shasum -a 256 "$O/C1Hosts.lean" | cut -d' ' -f1))"
summ "$out" "$ex"; echo '```'; san <<<"$out"; echo '```'
echo
echo "## 2. Cut checks, axiom prints, freeze, names"
echo
echo "Separate logs (same run): \`cutcheck.log\`, \`axioms.log\`, \`freeze.log\`, \`names.log\`. Summary:"
echo '```'
grep -E '^\* |exit [0-9]' "$O/cutcheck.log" | san
grep -E 'FREEZE|CODE DIFFERS|freeze.py exit' "$O/freeze.log"
sed -n '/^```/,/^```/p' "$O/names.log" | grep -E '^[0-9]\.|^[0-9]+ declarations' | cut -c1-150
echo "positive control: $(grep -c '   CLASH' "$O/names.log") clashes caught (of 2 planted)"
echo '```'
echo
echo "## 3. Semantic sanity probes (evidence only; not landing material)"
out=$(el "$O/probes/C1HostsSanity.lean"); ex=$?
n=$(grep -c '^example' "$O/probes/C1HostsSanity.lean")
echo; echo "### probes/C1HostsSanity.lean: the unit, one extra Mathlib import, and $n \`example\`s"; summ "$out" "$ex"
echo '```'; grep -v "declaration uses 'sorry'" <<<"$out" | san; echo "(the sorry warnings are those of the unit)"; echo '```'
echo
echo "Negative controls (deliberately false copies of probe examples; each must fail):"
for n in neg1 neg2 neg3; do out=$(el "$O/work/$n.lean"); ex=$?
  echo "* \`$n\`: exit $ex, errors $(grep -c ': error' <<<"$out"): $(grep ': error' <<<"$out" | san | head -1 | cut -c1-110)"
done
echo "  (neg1: 80 replay records per state; neg2: the replay head at 3 after a halting choice step;"
echo "  neg3: a word of length m reaches the writer's \`done\`; neg3 fails once per case split.)"
echo
echo "## 4. Style lint (\`scripts/campaign_style_lint.py\` over the six landing modules and patched b)"
rm -rf "$O/work/lintroot"; mkdir -p "$O/work/lintroot/TCSlib/Complexity/Diagonalization"
cp -R "$O/landed/TCSlib" "$O/work/lintroot/"
cp "$O/work/patch/b/TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean" "$O/work/lintroot/TCSlib/Complexity/Diagonalization/"
echo '```'; (cd "$O/work/lintroot" && python3 -I "$SC/lint.py" TCSlib "$O/work/lintroot") | san; echo '```'
echo
echo "## 5. Line widths (characters, not bytes)"
echo '```'
python3 -I "$SC/widths.py" "$O/C1Hosts.lean" "$O/probes/C1HostsSanity.lean" $(find "$O/landed" -name '*.lean') | san
echo '```'
echo
echo "## 6. Cited names: every backticked identifier of the unit's comments, as \`#check @…\`"
python3 -I "$SC/cited.py" "$O/C1Hosts.lean" > "$O/work/cited_unit.txt"
{ cat "$O/C1Hosts.lean"; echo; echo "open Turing Turing.NDTM Turing.FinNDTM Turing.FinTM Turing.MultiTapeTM";
  while read -r t; do echo "#check @$t"; done < "$O/work/cited_unit.txt"; } > "$O/work/cite_unit.lean"
out=$(el "$O/work/cite_unit.lean")
echo; echo "$(wc -l < "$O/work/cited_unit.txt" | tr -d ' ') tokens; those that do not resolve:"
echo '```'; grep ': error' <<<"$out" | sed -E 's/.*error[^:]*: //' | sort | uniq | tr '\n' ' ' | fold -s -w 98; echo; echo '```'
echo
echo "## 7. Statement correspondence (\`<OUT>/scripts/sigdiff.py\`: statements up to the top-level \`:=\`)"
echo
echo "### audits/evidence/c1/C1HostsDraft.lean.txt against C1Hosts.lean"
echo '```'; python3 -I "$SC/sigdiff.py" "$WT/audits/evidence/c1/C1HostsDraft.lean.txt" "$O/C1Hosts.lean" | san; echo '```'
echo
echo "### audits/evidence/stage2-gate/NDSlice.lean.txt against C1Hosts.lean (the gated slice lemma)"
echo '```'; python3 -I "$SC/sigdiff.py" "$WT/audits/evidence/stage2-gate/NDSlice.lean.txt" "$O/C1Hosts.lean" | san | cut -c1-300; echo '```'
echo
echo "### audits/evidence/b6hosts/B6HostsDraft.lean.txt: C1's draft step clock as the B6 corollary"
echo '```'
python3 -I - "$SC" "$WT/audits/evidence/c1/C1HostsDraft.lean.txt" "$WT/audits/evidence/b6hosts/B6HostsDraft.lean.txt" <<'PY'
import sys
sys.path.insert(0, sys.argv[1])
from sigdiff import decls
a, b = decls(sys.argv[2]), decls(sys.argv[3])
for n in ["Turing.exists_stepClockTM", "Turing.clockCfg"]:
    same = a[n][0] == b[n][0]
    print(f"{n}: C1 draft statement {'IDENTICAL to' if same else 'differs from'} the B6 draft's")
    if not same:
        print("   C1: " + a[n][0]); print("   B6: " + b[n][0])
PY
echo '```'
echo
echo "## 8. Downstream import check (Part A adds \`import ...StateRenaming\` to \`Nondeterministic.lean\`)"
python3 -I "$S/tools/imports.py" "$WT" "$O/work/importgraph.json" >/dev/null
echo '```'
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
ND = "TCSlib/Complexity/TuringMachine/Nondeterministic"
SR = "TCSlib/Complexity/TuringMachine/StateRenaming"
down = [m for m in g if ND in closure(m)]
lack = sorted(m for m in down if SR not in closure(m))
print(f"{len(g)} modules; {len(down)} have Nondeterministic in their closure; "
      f"{len(lack)} of these gain StateRenaming at landing:")
for m in lack: print("  ", m)
PY
echo '```'
for m in ClassNP/NTIME TuringMachine/NondeterministicSpace; do b=$(basename $m)
  { sed -n '1,/^import/p' "$WT/TCSlib/Complexity/$m.lean" | grep -v '^import'
    echo "import TCSlib.Complexity.TuringMachine.StateRenaming"; sed -n '/^import/,$p' "$WT/TCSlib/Complexity/$m.lean"; } > "$O/work/downstream/$b.lean"
  cp "$WT/TCSlib/Complexity/$m.lean" "$O/work/downstream/${b}_orig.lean"
  o1=$(el "$O/work/downstream/${b}_orig.lean"); e1=$?; o2=$(el "$O/work/downstream/$b.lean"); e2=$?
  echo "* \`$m\`: as is:"; summ "$o1" "$e1"; echo "  with the extra import:"; summ "$o2" "$e2"
done
echo
echo "## 9. Nothing in the checkout was changed"
echo
echo "All outputs are under <OUT>. No git, lake or elan command was run; \`lean\` ran only through"
echo "\`tools/leanelab.sh\`, which writes no olean; Python ran only as \`python3 -I\`."
} > "$O/elaboration.log"
echo "wrote logs in $O"
