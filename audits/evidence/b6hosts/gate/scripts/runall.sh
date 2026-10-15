#!/usr/bin/env bash
# Re-run every check of the B6 hosts statement gate and write the logs (read-only on the worktree).
# `lean` only through tools/leanelab.sh (no -o, no olean written); python3 -I for the scripts;
# `diff` and `patch` on scratch copies. No git, no lake.
# Usage: bash runall.sh <S>
S="$1"; WT="$S/wt-g5b6"; OL="$S/oleans-f8"; O="$S/gate-b6hosts"; SC="$O/scripts"; WK="$O/work"
LOGE="$O/elaboration.log"; LOGC="$O/cutcheck.log"; LOGF="$O/freeze.log"; LOGA="$O/axioms.log"
LOGN="$O/names.log"
el() { bash "$S/tools/leanelab.sh" "$WT" "$OL" "$1" 2>&1; }
san() { sed "s|$O/|<OUT>/|g; s|$S/|<S>/|g"; }
summ() { # output exit
  local e w s
  e=$(grep -c ': error' <<<"$1"); w=$(grep -c ': warning' <<<"$1")
  s=$(grep -c "declaration uses 'sorry'" <<<"$1")
  echo "exit $2 | errors $e | warnings $w | of which \`declaration uses 'sorry'\` $s | other warnings $((w - s))"
}
HEADC=$(cat /Users/seyoonr/phd_experiments/tcslib/.git/worktrees/wt-g5b6/HEAD)
prov() {
  echo "Tool: \`bash <S>/tools/leanelab.sh <S>/wt-g5b6 <S>/oleans-f8 <file>\` (a direct \`lean\` call"
  echo "inside the worktree, no \`-o\`, no olean written). Worktree: the read-only checkout \`wt-g5b6\`"
  echo "at campaign commit \`$HEADC\` (the worktree's HEAD file); olean snapshot \`oleans-f8\`"
  echo "(all of TCSlib at that commit, and Mathlib). Toolchain \`$(cat "$WT/lean-toolchain")\`."
  echo "<OUT> is this pack's scratch directory, <S> the scratchpad. Run: $(date -u '+%Y-%m-%d %H:%M UTC')."
}
rm -rf "$WK/landing" "$WK/patched" "$WK/cut" "$WK/patchreplay"
mkdir -p "$O/patches" "$O/probes" "$WK"

# ---------------------------------------------------------------- landing, patches, probes
LAND=$(cd "$SC" && python3 -I gate.py land "$O/B6Hosts.lean" "$WT" "$SC/edits.py" "$WK")
EXIST="TuringMachine/StateRenaming TuringMachine/Encoding SpaceComplexity/ConfigCount
TuringMachine/Build/CfgRecord SpaceComplexity/ConfigGraph SpaceComplexity/Hierarchy"
rm -f "$O"/patches/*.patch
for f in $EXIST; do
  b=$(basename "$f")
  (cd "$WT" && diff -u "TCSlib/Complexity/$f.lean" "$WK/patched/TCSlib/Complexity/$f.lean" |
    sed "1s|^--- .*|--- a/TCSlib/Complexity/$f.lean|; 2s|^+++ .*|+++ b/TCSlib/Complexity/$f.lean|") \
    > "$O/patches/$b.patch"
done
for f in TuringMachine SpaceComplexity; do
  (cd "$WT" && diff -u "TCSlib/Complexity/$f.lean" "$WK/patched/TCSlib/Complexity/$f.lean" |
    sed "1s|^--- .*|--- a/TCSlib/Complexity/$f.lean|; 2s|^+++ .*|+++ b/TCSlib/Complexity/$f.lean|") \
    > "$O/patches/facade-$f.patch"
done
rm -rf "$O/landing"; cp -R "$WK/landing" "$O/landing"
CUT=$(cd "$SC" && python3 -I gate.py cut "$O/B6Hosts.lean" "$WT" "$SC/edits.py" "$WK")
PROBES=$(cd "$SC" && python3 -I probes.py "$O" "$WT")

# ---------------------------------------------------------------- cut checks
{
echo "# B6 hosts statement gate: cut checks"
echo; prov; echo
echo "## 1. Landing: the parts placed, the asserted edits applied"
echo
echo "\`python3 -I <OUT>/scripts/gate.py land <OUT>/B6Hosts.lean <S>/wt-g5b6 <OUT>/scripts/edits.py"
echo "<OUT>/work\` writes the five new modules (copyright, the part's imports, the standard options,"
echo "the part verbatim) and the eight patched existing files (each part placed as its header says,"
echo "then the edits of \`edits.py\`, each asserted to match exactly once)."
echo '```'; san <<<"$LAND"; echo '```'
echo
echo "## 2. Patch replay"
echo
echo "Each patch is applied with \`patch -p1\` to a scratch copy of the worktree file, and the result"
echo "is compared byte for byte with the patched file."
echo '```'
mkdir -p "$WK/patchreplay"
for p in "$O"/patches/*.patch; do
  t=$(sed -n '1s|^--- a/||p' "$p")
  mkdir -p "$WK/patchreplay/$(dirname "$t")"; cp "$WT/$t" "$WK/patchreplay/$t"
  (cd "$WK/patchreplay" && patch -s -p1 < "$p")
  if cmp -s "$WK/patchreplay/$t" "$WK/patched/$t"; then r=identical; else r=DIFFERENT; fi
  echo "$(basename "$p"): $t, $(grep -c '^+[^+]' "$p") added / $(grep -c '^-[^-]' "$p") removed lines; replay $r"
done
echo '```'
echo
echo "## 3. Each landing module in exactly its own import closure"
echo
echo "\`python3 -I <OUT>/scripts/gate.py cut …\` writes one check file per part and one per patched"
echo "existing file: the imports of the target and of the parts in its import closure, the standard"
echo "options, the bodies of those parts in file order, then the target's own body. The closure is"
echo "computed over the worktree's import graph, so an appended part is included wherever its module"
echo "is imported, directly or not. Part K (a replacement) is never included in another target."
echo '```'; san <<<"$CUT"; echo '```'
echo
for f in "$WK"/cut/*.check.lean; do
  out=$(el "$f"); ex=$?
  echo "* \`$(basename "$f")\` ($(wc -l < "$f" | tr -d ' ') lines): $(summ "$out" "$ex")"
  grep ': error' <<<"$out" | san | head -5
done
echo
echo "## 4. Layering (user decision B4): \`SpaceComplexity\` modules in each new module's import closure"
echo '```'
python3 -I - "$WT" "$O/B6Hosts.lean" <<'PYEOF'
import os, sys
wt, unit = sys.argv[1], sys.argv[2]
g = {}
for dp, _, fs in os.walk(os.path.join(wt, "TCSlib")):
    for f in fs:
        if f.endswith(".lean"):
            p = os.path.join(dp, f); m = os.path.relpath(p, wt)[:-5].replace(os.sep, ".")
            g[m] = [l.split()[1] for l in open(p, encoding="utf-8") if l.startswith("import TCSlib")]
parts, cur = {}, None
for l in open(unit, encoding="utf-8"):
    if l.startswith("-- @landing "): cur = l.split()[2]; parts[cur] = []
    elif l.startswith("-- @imports ") and cur: parts[cur] += l.split()[2:]
def clo(ms):
    seen, todo = set(), list(ms)
    while todo:
        m = todo.pop()
        if m in seen: continue
        seen.add(m); todo += parts.get(m, []) if m not in g else g[m]
    return seen
for m in parts:
    if m in g: continue
    c = clo(parts[m]); sc = sorted(x for x in c if ".SpaceComplexity." in x or x.endswith(".SpaceComplexity"))
    print(f"{m}: closure {len(c)} modules; SpaceComplexity modules: {len(sc)}{' ' + str(sc[:3]) + ' …' if sc else ''}")
PYEOF
echo '```'
} > "$LOGC"

# ---------------------------------------------------------------- freeze
{
echo "# B6 hosts statement gate: freeze check of the eight existing files touched"
echo; prov; echo
echo "\`python3 -I <OUT>/scripts/freeze.py <worktree file> <patched file> <allowed statement changes>"
echo "<allowed body changes>\`: every declaration's statement (comment-stripped, up to the top-level"
echo "\`:=\`), body and docstring compared; a statement or body change outside the allowances fails."
echo "The allowances are exactly the user's decisions B1 (\`space_universal\`) and B3 (the S1b"
echo "re-pointing), and the one proof re-derivation (\`exists_codeTM\`, to build the relabelling once)."
allow_s() { case "$1" in
  SpaceComplexity/Hierarchy) echo "Complexity.space_universal" ;;
  SpaceComplexity/ConfigGraph) echo "Turing.FinNDTM.s1b_record_accepts" ;;
  *) echo "" ;; esac; }
allow_b() { case "$1" in
  SpaceComplexity/ConfigGraph) echo "Turing.FinNDTM.count_windowed_vertices,Turing.FinNDTM.s1b_record,Turing.FinNDTM.s1b_record_eq_iff,Turing.FinNDTM.s1b_record_accepts" ;;
  TuringMachine/Encoding) echo "Turing.exists_codeTM" ;;
  *) echo "" ;; esac; }
for f in $EXIST; do
  echo; echo "## $f.lean"
  echo "allowances: statements [$(allow_s "$f")], bodies [$(allow_b "$f")]"
  echo '```'
  (cd "$SC" && python3 -I freeze.py "$WT/TCSlib/Complexity/$f.lean" \
    "$WK/patched/TCSlib/Complexity/$f.lean" "$(allow_s "$f")" "$(allow_b "$f")") | san
  echo '```'
done
echo; echo "## Positive control: \`Hierarchy.lean\` without its allowance (must fail)"
echo '```'
(cd "$SC" && python3 -I freeze.py "$WT/TCSlib/Complexity/SpaceComplexity/Hierarchy.lean" \
  "$WK/patched/TCSlib/Complexity/SpaceComplexity/Hierarchy.lean"; echo "exit status $?") | san | grep 'space_universal\|RESULT\|exit status'
echo '```'
for f in TuringMachine SpaceComplexity; do
  echo; echo "## facade $f.lean (no declarations)"
  echo '```'
  echo "imports added: $(diff "$WT/TCSlib/Complexity/$f.lean" "$WK/patched/TCSlib/Complexity/$f.lean" | grep -c '^> import')"
  echo "imports removed: $(diff "$WT/TCSlib/Complexity/$f.lean" "$WK/patched/TCSlib/Complexity/$f.lean" | grep -c '^< import')"
  echo "other changed lines: $(diff "$WT/TCSlib/Complexity/$f.lean" "$WK/patched/TCSlib/Complexity/$f.lean" | grep '^[<>]' | grep -vc '^[<>] import')  (the Contents list)"
  echo '```'
done
} > "$LOGF"

# ---------------------------------------------------------------- elaboration, probes, lint
{
echo "# B6 hosts statement gate: elaboration log"
echo; prov; echo
echo "In the repository the files map as in \`BUNDLE-MISSING.txt\`: <OUT>/B6Hosts.lean ->"
echo "audits/evidence/b6hosts/gate/B6Hosts.lean.txt, <OUT>/probes/<P>.lean ->"
echo "audits/evidence/b6hosts/gate/probes/<P>.lean.txt, <OUT>/scripts/<s> ->"
echo "audits/evidence/b6hosts/gate/scripts/<s>(.txt), <OUT>/patches/<p> ->"
echo "audits/evidence/b6hosts/gate/patches/<p>."
echo
echo "## 1. The landing-form unit"
out=$(el "$O/B6Hosts.lean"); ex=$?
echo; echo "### B6Hosts.lean ($(wc -l < "$O/B6Hosts.lean" | tr -d ' ') lines; SHA-256 $(shasum -a 256 "$O/B6Hosts.lean" | cut -c1-64))"
echo "$(summ "$out" "$ex")"
echo '```'; san <<<"$out"; echo '```'
echo "The sorry warnings, by declaration:"
echo '```'
grep "declaration uses 'sorry'" <<<"$out" | sed -E 's/.*:([0-9]+):[0-9]+: .*/\1/' | while read -r l; do
  echo "line $l: $(sed -n "${l}p" "$O/B6Hosts.lean" | sed -E 's/^(theorem|def) ([^ ]+).*/\2/')"
done
echo '```'
echo
echo "## 2. Semantic sanity probes and negative controls (evidence only; not landing material)"
out=$(el "$O/probes/Sanity.lean"); ex=$?
n=$(grep -c '^example' "$O/probes/Sanity.lean"); m=$(grep -c '^theorem emitHalt\|^def emitHalt' "$O/probes/Sanity.lean")
echo; echo "### probes/Sanity.lean: the unit plus $n \`example\`s and $m helper declarations"
echo "$(summ "$out" "$ex")"
echo '```'; san <<<"$out" | grep -v "declaration uses 'sorry'"; echo "(the sorry warnings are the unit's ten)"; echo '```'
echo
echo "Negative controls: each is the probe file with one probe made false; each must fail."
for nn in neg1 neg2 neg3 neg4; do
  out=$(el "$WK/$nn.lean"); ex=$?
  echo "* \`$nn\`: exit $ex, errors $(grep -c ': error' <<<"$out"): $(grep ': error' <<<"$out" | san | head -1 | sed -E 's/.*error[^:]*: //' | cut -c1-90)"
done
echo "  (neg1: \`summaryTag 1 (some true) = 1\` (true value 2); neg2: on \`z = [true]\` with \`ℓ = 1\`,"
echo "  the cell probed from \`p = 2\` (the header's cell) claimed blank; neg3: \`[true, true]\` claimed"
echo "  to have tag \`1\` (accept); neg4: one round of the last-transition machine claimed"
echo "  \`halted\`, the surplus round removed.)"
echo
echo "## 3. The gated statement follows from the strengthened one"
out=$(el "$O/probes/GatedFormProbe.lean"); ex=$?
echo; echo "\`probes/GatedFormProbe.lean\`: the patched \`Hierarchy.lean\` in its patched closure (the cut"
echo "check file) plus \`Complexity.space_universal_gated_form\`, whose statement is the worktree's"
echo "gated \`space_universal\` extracted by \`probes.py\` (asserted to contain"
echo "\`C * (s + logSpace x.length + 1)\`) and renamed. $(san <<<"$PROBES")"
echo "$(summ "$out" "$ex")"
echo '```'; san <<<"$out"; echo '```'
echo
echo "### The draft's statement of the step clock follows from the landing form's"
out=$(el "$O/probes/StepClockDraftFormProbe.lean"); ex=$?
echo; echo "\`probes/StepClockDraftFormProbe.lean\`: the unit plus"
echo "\`Turing.exists_stepClockTMVia_draft_form\`, whose statement is the draft's"
echo "\`exists_stepClockTMVia\` (\`audits/evidence/b6hosts/B6HostsDraft.lean.txt\`, which the C1 pack"
echo "cites), extracted by \`probes.py\` and renamed, proved from the landing form's statement by"
echo "dropping the frame clause's extra conjuncts."
echo "$(summ "$out" "$ex")"
echo '```'; san <<<"$out" | grep -v "declaration uses 'sorry'"; echo "(the sorry warnings are the unit's ten)"; echo '```'
echo
echo "## 4. Line widths (Unicode characters, not bytes)"
echo '```'
python3 -I - "$O" <<'PYEOF'
import os, sys
O = sys.argv[1]; bad = 0; files = [os.path.join(O, "B6Hosts.lean")]
for d in ("landing", "probes"):
    for dp, _, fs in os.walk(os.path.join(O, d)):
        files += [os.path.join(dp, f) for f in fs if f.endswith(".lean")]
for p in sorted(files):
    for i, l in enumerate(open(p, encoding="utf-8").read().split("\n"), 1):
        if len(l) > 100: print(f"{os.path.relpath(p, O)}:{i}: {len(l)}"); bad += 1
added = 0
for f in sorted(os.listdir(os.path.join(O, "patches"))):
    for l in open(os.path.join(O, "patches", f), encoding="utf-8").read().split("\n"):
        if l.startswith("+") and not l.startswith("+++"):
            added += 1
            if len(l) - 1 > 100: print(f"patches/{f}: added line of {len(l) - 1}"); bad += 1
print(f"{len(files)} files and {added} added patch lines checked; over 100 characters: {bad}")
PYEOF
echo '```'
echo
echo "## 5. Style lint (\`scripts/campaign_style_lint.py\`, its ROOT pointed at a copy of the landing"
echo "modules and the patched files)"
rm -rf "$WK/lintroot"; mkdir -p "$WK/lintroot"
cp -R "$WK/landing/TCSlib" "$WK/lintroot/"; cp -R "$WK/patched/TCSlib" "$WK/lintroot/"
sed "s|^ROOT = .*|ROOT = Path(\"$WK/lintroot\")|" "$WT/scripts/campaign_style_lint.py" > "$WK/lint.py"
echo '```'; (cd "$WK" && python3 -I "$WK/lint.py" TCSlib/Complexity) | san; echo '```'
echo
echo "## 6. Statement correspondence with the draft"
echo
echo "\`python3 -I <OUT>/scripts/freeze.py --report <draft> <unit>\` (the comparison mode of the freeze"
echo "script: comment-stripped statements and bodies, docstrings reported separately). The draft is"
echo "\`audits/evidence/b6hosts/B6HostsDraft.lean.txt\`; its \`Complexity.B6Draft\` names appear here"
echo "as removed, and \`Complexity.space_universal\` as added (the same text, part K)."
echo '```'
(cd "$SC" && python3 -I freeze.py --report "$WT/audits/evidence/b6hosts/B6HostsDraft.lean.txt" "$O/B6Hosts.lean") | san
echo '```'
echo
echo "## 7. Sizes (MEASURED, \`wc -l\`)"
echo '```'
for f in $(cd "$O/landing" && find . -name '*.lean' | sort); do echo "new  $(wc -l < "$O/landing/$f" | tr -d ' ') ${f#./}"; done
for f in $EXIST; do echo "edit $(wc -l < "$WT/TCSlib/Complexity/$f.lean" | tr -d ' ') -> $(wc -l < "$WK/patched/TCSlib/Complexity/$f.lean" | tr -d ' ') TCSlib/Complexity/$f.lean"; done
echo '```'
} > "$LOGE"

# ---------------------------------------------------------------- axioms
python3 -I "$SC/names.py" "$O/B6Hosts.lean" "$WT" --replaces Complexity.space_universal --list "$WK/decls.txt" > /dev/null
{ cat "$O/B6Hosts.lean"; echo
  echo "/-! Axiom probe (evidence only): one \`#print axioms\` per declaration of the unit. -/"
  while read -r n; do echo "#print axioms $n"; done < "$WK/decls.txt"; } > "$WK/AxProbe.lean"
{ cat "$WK/cut/Encoding.patched.check.lean"; echo; echo "#print axioms Turing.exists_codeTM"; } > "$WK/AxEncoding.lean"
{ cat "$WK/cut/ConfigGraph.patched.check.lean"; echo
  echo "#print axioms Turing.FinNDTM.acceptsWithin_of_spaceUsedWith_le"
  echo "#print axioms Turing.FinNDTM.DecidesInSpace.mem_iff_acceptsWithin_configBound"; } > "$WK/AxConfigGraph.lean"
{ cat "$O/probes/GatedFormProbe.lean"; echo; echo "#print axioms Complexity.space_universal_gated_form"; } > "$WK/AxGated.lean"
{
echo "# B6 hosts statement gate: axiom prints"
echo; prov; echo
echo "Separate probe copies (never landing material): the unit with one \`#print axioms\` per"
echo "declaration ($(wc -l < "$WK/decls.txt" | tr -d ' ') names, from the name screen's listing), and the patched"
echo "\`Encoding.lean\` and \`ConfigGraph.lean\` check files with prints of the re-derived"
echo "\`exists_codeTM\` and of the public theorems above the re-pointed private lemmas."
for f in AxProbe AxEncoding AxConfigGraph AxGated; do
  out=$(el "$WK/$f.lean"); ex=$?
  echo; echo "## $f.lean: $(summ "$out" "$ex")"
  echo '```'
  san <<<"$out" | grep -v "declaration uses 'sorry'" | sed -E 's/^<OUT>[^ ]*: info: //' | tr '\n' ' ' |
    sed -E "s/ '/\n'/g" | sed -E 's/  +/ /g'; echo
  echo '```'
done
echo
echo "Summary (unit): the names whose prints contain \`sorryAx\`:"
echo '```'
el "$WK/AxProbe.lean" | tr '\n' ' ' | sed -E "s/ '/\n'/g" | grep sorryAx | sed -E "s/^'([^']+)'.*/\1/"
echo '```'
} > "$LOGA"

# ---------------------------------------------------------------- names and citations
python3 -I "$SC/cited.py" "$O/B6Hosts.lean" "$O"/patches/*.patch > "$WK/cited.txt"
{ cat "$O/B6Hosts.lean"; echo; echo "open Turing Turing.FinTM Turing.MultiTapeTM Complexity"
  while read -r t; do echo "#check @$t"; done < "$WK/cited.txt"; } > "$WK/cite_probe.lean"
{
echo "# B6 hosts statement gate: name screen and cited names"
echo; prov; echo
echo "## 1. Name screen: the unit's declarations against every declaration of the worktree's TCSlib"
echo '```'
python3 -I "$SC/names.py" "$O/B6Hosts.lean" "$WT" --replaces Complexity.space_universal | san
echo '```'
echo "Positive control (\`scripts/screen_ctrl.lean\`: \`Turing.FinTM.configBound\`, \`Turing.outSummary\`,"
echo "\`Turing.logSpace\`):"
echo '```'
python3 -I "$SC/names.py" "$SC/screen_ctrl.lean" "$WT" | san
echo '```'
echo
echo "## 2. Cited names: every backticked identifier of the unit's comments and of the patches'"
echo "added lines, as \`#check @…\` after the unit (\`open Turing Turing.FinTM Turing.MultiTapeTM"
echo "Complexity\`)"
out=$(el "$WK/cite_probe.lean")
echo; echo "$(wc -l < "$WK/cited.txt" | tr -d ' ') tokens; those that do not resolve:"
echo '```'
grep ': error' <<<"$out" | sed -E 's/.*error[^:]*: //' | sort | uniq | sed -E 's/Unknown identifier //' | tr '\n' ' ' | fold -s -w 98; echo
echo '```'
} > "$LOGN"
echo "logs written: $(ls "$O"/*.log | san | tr '\n' ' ')"
