#!/usr/bin/env bash
# Re-run every check of the C1 guess-then-run assembly statement gate and write the logs.
# Read-only on the repository: `lean` only through tools/leanelab.sh (no -o, no olean written),
# python3 -I only, no lake/elan; git only read-only (rev-parse, ls-tree, archive to stdout,
# status with optional locks off). FAIL-CLOSED: every check records PASS or FAIL in
# <OUT>/logs/summary.txt, and the script exits 1 if any check failed.
# Usage: bash runall.sh <S>
#   WT   = <S>/wt-c1asm (read-only checkout; supplies the Mathlib packages, whose manifest is
#          unchanged at the tip, and the repository's object store)
#   TIP  = the campaign tip e831b5b0; BASE = <OUT>/base, its sources (git archive of TIP)
#   OL   = <S>/oleans-lm0b (MIG-0b's replay snapshot; Lean content of 13a16a69 = the tip's,
#          up to docstrings of #89 and #91)
export LC_ALL=C
S="$1"; WT="$S/wt-c1asm"; OL="$S/oleans-lm0b"; O="$S/gate-c1asm"; SC="$O/scripts"; L="$O/logs"
BASE="$O/base"; TIP=$(cd "$WT" && git rev-parse --verify e831b5b0^{commit})
mkdir -p "$L"; : > "$L/summary.txt"; FAILS=0
el() { bash "$S/tools/leanelab.sh" "$WT" "$OL" "$1" 2>&1; }
san() { sed "s|$O/|<OUT>/|g; s|$S/|<S>/|g"; }
cnt() { grep -c -- "$1" <<<"$2"; }
summ() { # output exit
  local e w s
  e=$(cnt ': error' "$1"); w=$(cnt ': warning' "$1"); s=$(cnt "declaration uses 'sorry'" "$1")
  echo "  exit $2 | errors $e | warnings $w | of which \`declaration uses 'sorry'\` $s | other warnings $((w - s))"
}
check() { # name condition-result(0/1)
  if [ "$2" -eq 0 ]; then echo "PASS $1" >> "$L/summary.txt"
  else echo "FAIL $1" >> "$L/summary.txt"; FAILS=$((FAILS + 1)); fi
}
rm -rf "$BASE"; mkdir -p "$BASE"
(cd "$WT" && git archive "$TIP" TCSlib lean-toolchain lake-manifest.json scripts/campaign_style_lint.py \
  audits/evidence) | tar -x -C "$BASE"; check "base sources archived from the tip" $?
python3 -I "$SC/mkprobes.py" "$O" >/dev/null; check "probe files built" $?
rm -rf "$O/cut" "$O/landed"
MKL=$(python3 -I "$SC/mklanded.py" "$BASE" "$O/C1Assembly.lean" "$O"); check "cut and landed files built" $?
HDR="Tool: \`bash <S>/tools/leanelab.sh <S>/wt-c1asm <S>/oleans-lm0b <file>\` (direct \`lean\`, no \`-o\`,
no olean written). Campaign tip: $TIP. Sources: <OUT>/base, the tip's tree
(\`git archive\`, read-only). Snapshot: \`oleans-lm0b\` (MIG-0b's replay output; the tip's Lean content up
to docstrings, \`base.log\`). \`wt-c1asm\` (at $(cd "$WT" && git rev-parse HEAD | cut -c1-8), read-only) supplies only the
Mathlib packages (manifest unchanged at the tip). Toolchain: \`$(cat "$BASE/lean-toolchain")\`.
<OUT> is the gate's output directory; <S> the scratchpad. Run: $(date -u '+%Y-%m-%d %H:%M UTC')."

# ---------- 0. base and snapshot
{
echo "# C1 guess-then-run assembly statement gate: base sources and snapshot"; echo; echo "$HDR"; echo
echo "## 1. The sources"
echo
echo "\`git archive $TIP\` of \`TCSlib\`, \`lean-toolchain\`, \`lake-manifest.json\`,"
echo "\`scripts/campaign_style_lint.py\` and \`audits/evidence\`, extracted to <OUT>/base."
nt=$(cd "$WT" && git ls-tree -r --name-only "$TIP" TCSlib | wc -l | tr -d ' ')
nb=$(find "$BASE/TCSlib" -type f | wc -l | tr -d ' ')
echo "Tree $(cd "$WT" && git rev-parse "$TIP^{tree}"); files under TCSlib: in the commit $nt, extracted $nb."
[ "$nt" = "$nb" ]; check "base: every TCSlib file of the tip extracted" $?
d1=$(cd "$WT" && GIT_OPTIONAL_LOCKS=0 git diff --name-only 13a16a69 "$TIP" -- '*.lean' | wc -l | tr -d ' ')
d2=$(cd "$WT" && GIT_OPTIONAL_LOCKS=0 git diff --name-only "$(git rev-parse HEAD)" "$TIP" -- lake-manifest.json lean-toolchain | wc -l | tr -d ' ')
echo "Lean files changed between 13a16a69 (PR #91's merge, the snapshot's content) and the tip: $d1."
echo "lake-manifest.json and lean-toolchain changed between wt-c1asm's HEAD and the tip: $d2."
[ "$d1" = 0 ] && [ "$d2" = 0 ]; check "base: tip Lean content = 13a16a69; manifest unchanged" $?
echo
echo "## 2. Snapshot consistency"
echo
echo "The tip's sources of \`Build/NDHost\`, the new import \`Build/Catalog\`, and the three MIG-0b-changed"
echo "modules in NDHost's closure that the unit uses (\`Build/Embed\`, \`Build/Seam\`, \`StateRenaming\`),"
echo "copied to <OUT>/work/srccheck/ and elaborated against the snapshot:"
rm -rf "$O/work/srccheck"; mkdir -p "$O/work/srccheck"
for f in Build/NDHost Build/Catalog Build/Embed Build/Seam StateRenaming; do
  b=$(basename "$f"); cp "$BASE/TCSlib/Complexity/TuringMachine/$f.lean" "$O/work/srccheck/$b.lean"
  out=$(el "$O/work/srccheck/$b.lean"); ex=$?
  echo "* \`$f\` (SHA-256 $(shasum -a 256 "$O/work/srccheck/$b.lean" | cut -c1-16)…):"; summ "$out" "$ex"
  [ "$ex" -eq 0 ] && [ "$(cnt ': error' "$out")" -eq 0 ]; check "snapshot consistency: $f elaborates" $?
done
echo
echo "Provenance of the snapshot: \`<S>/land-b6r/LANDING-NOTES.md\` (the B6 hosts' landing run at 13a16a69"
echo "used it: \"MIG-0b's replay output. It differs from the tip only in the docstrings of the 18 files of"
echo "#89 and #91\")."
} > "$L/base.log"

# ---------- 1. elaboration: unit, sanity probes, negative controls, consumer probe
{
echo "# C1 guess-then-run assembly statement gate: elaboration log"; echo; echo "$HDR"; echo
echo "In the repository the files map as: <OUT>/C1Assembly.lean -> audits/evidence/c1/assembly/"
echo "C1Assembly.lean.txt; <OUT>/AssemblyConsumerProbe.lean -> audits/evidence/c1/assembly/"
echo "AssemblyConsumerProbe.lean.txt; <OUT>/C1-assembly-design.md -> audits/evidence/c1/assembly/"
echo "C1-assembly-design.md; <OUT>/probes/<x>.lean -> audits/evidence/c1/assembly/probes/<x>.lean.txt;"
echo "<OUT>/cut/NDHost.check.lean -> audits/evidence/c1/assembly/cut/NDHost.check.lean.txt;"
echo "<OUT>/landed/TCSlib/Complexity/TuringMachine/Build/NDHost.lean -> audits/evidence/c1/assembly/"
echo "landed/NDHost.lean.txt; <OUT>/scripts/<x> -> audits/evidence/c1/assembly/scripts/<x>;"
echo "<OUT>/logs/<x>.log -> audits/logs/c1-assembly-statements-<x>.log (summary.txt -> -summary.log)."
echo "<OUT>/work/ holds generated files (negative controls, isolation copies, the cited-name file),"
echo "regenerated by this script; <OUT>/scripts/lint.py is scripts/campaign_style_lint.py with ROOT"
echo "taken from its second argument."
echo
echo "## 1. The unit"
out=$(el "$O/C1Assembly.lean"); ex=$?
echo; echo "### C1Assembly.lean ($(wc -l < "$O/C1Assembly.lean" | tr -d ' ') lines; SHA-256 $(shasum -a 256 "$O/C1Assembly.lean" | cut -d' ' -f1))"
summ "$out" "$ex"; echo '```'; san <<<"$out"; echo '(end of output)'; echo '```'
[ "$ex" -eq 0 ] && [ "$(cnt ': error' "$out")" -eq 0 ]; check "unit: 0 errors" $?
[ "$(cnt ': warning' "$out")" -eq 0 ]; check "unit: 0 warnings" $?
echo
echo "## 2. Sanity probes (evidence only; not landing material)"
out=$(el "$O/probes/C1AssemblySanity.lean"); ex=$?
n=$(grep -c '^example' "$O/probes/C1AssemblySanity.lean")
echo; echo "### probes/C1AssemblySanity.lean: the unit and the tail \`scripts/sanity_tail.lean.txt\` ($n \`example\`s)"
summ "$out" "$ex"; echo '```'; san <<<"$out"; echo '(end of output)'; echo '```'
[ "$ex" -eq 0 ] && [ "$(cnt ': error' "$out")" -eq 0 ]; check "sanity probes: 0 errors" $?
echo
echo "Negative controls (copies of the sanity file with one example made false; each must fail):"
for n in neg1 neg2 neg3 neg4; do out=$(el "$O/work/$n.lean"); ex=$?; e=$(cnt ': error' "$out")
  echo "* \`$n\`: exit $ex, errors $e: $(grep ': error' <<<"$out" | san | head -1 | cut -c1-120)"
  [ "$e" -ge 1 ]; check "negative control $n fails" $?
done
echo "  (neg1: the stream read two bits early; neg2: the captured host's output claimed noisy;"
echo "  neg3: the immediate-accept host claimed halted at length 10; neg4: liveness claimed for"
echo "  words of length 15, the handoff time.)"
echo
echo "## 3. Consumer probe (evidence only)"
out=$(el "$O/AssemblyConsumerProbe.lean"); ex=$?
echo; echo "### AssemblyConsumerProbe.lean: the unit, two extra imports, and \`scripts/consumer_tail.lean.txt\`"
summ "$out" "$ex"; echo '```'; san <<<"$out"; echo '(end of output)'; echo '```'
[ "$ex" -eq 0 ] && [ "$(cnt ': error' "$out")" -eq 0 ]; check "consumer probe: 0 errors" $?
echo
echo "## 4. Line widths (characters, not bytes)"
echo '```'
w=$(python3 -I "$SC/widths.py" "$O/C1Assembly.lean" "$O/probes/C1AssemblySanity.lean" \
  "$O/probes/C1AssemblyAxioms.lean" "$O/AssemblyConsumerProbe.lean" \
  "$O/landed/TCSlib/Complexity/TuringMachine/Build/NDHost.lean" | san); echo "$w"
echo '```'
grep -q 'over-100 lines: 0' <<<"$w"; check "widths: no line over 100 characters" $?
echo
echo "## 5. Forbidden constructs in the gate's Lean files"
echo
echo "Screened files: the unit, the three probe files, the consumer probe, the cut and landed files."
echo "Pattern: \`#eval\`, \`run_cmd\`, the word \`IO\`, \`unsafe\`, \`implemented_by\`, \`extern\`,"
echo "\`native_decide\`, and lines starting with \`syntax\`, \`macro\`, \`macro_rules\` or \`elab\`."
echo '```'
hits=$(grep -nE '#eval|run_cmd|\bIO\b|\bunsafe\b|implemented_by|@\[extern|\bnative_decide\b|^\s*(syntax|macro|macro_rules|elab)\b' \
  "$O/C1Assembly.lean" "$O"/probes/*.lean "$O/AssemblyConsumerProbe.lean" "$O/cut/NDHost.check.lean" \
  "$O/landed/TCSlib/Complexity/TuringMachine/Build/NDHost.lean" | san)
echo "${hits:-(no hits)}"; echo '```'
[ -z "$hits" ]; check "no forbidden constructs" $?
echo
echo "## 6. Style lint (\`scripts/campaign_style_lint.py\`, as \`<OUT>/scripts/lint.py\` with ROOT its second argument)"
rm -rf "$O/work/lintroot"; mkdir -p "$O/work/lintroot"; cp -R "$O/landed/TCSlib" "$O/work/lintroot/"
ld=$(diff "$BASE/scripts/campaign_style_lint.py" "$SC/lint.py" | grep -c '^[<>]')
echo "\`lint.py\` against the tip's \`scripts/campaign_style_lint.py\`: $ld differing lines (the ROOT line, each side)."
[ "$ld" = 2 ]; check "lint.py is the tip's lint up to ROOT" $?
echo '```'; lo=$(cd "$O/work/lintroot" && python3 -I "$SC/lint.py" TCSlib "$O/work/lintroot" 2>&1); r=$?; echo "$lo" | san; echo "lint exit $r"; echo '```'
[ "$r" -eq 0 ] && grep -q ' 0 FAIL' <<<"$lo"; check "style lint: 0 FAIL on the landed NDHost" $?
echo
echo "## 7. Cited names: every backticked identifier in the unit's comments, as \`#check @…\`"
echo
echo "Population: \`<OUT>/scripts/cited_asm.py\` (lexical comment extraction; every plain identifier"
echo "token, no further filter). Checked in the unit plus \`NDCodeSimulator\`, \`ClassNP.NTIME\`,"
echo "\`Diagonalization.NTimeHierarchy\` and \`Build.OracleCall\`."
n=$(python3 -I "$SC/cited_asm.py" "$O/C1Assembly.lean" "$O/work/cite_unit.lean" \
  TCSlib.Complexity.TuringMachine.NDCodeSimulator TCSlib.Complexity.ClassNP.NTIME \
  TCSlib.Complexity.Diagonalization.NTimeHierarchy TCSlib.Complexity.TuringMachine.Build.OracleCall)
out=$(el "$O/work/cite_unit.lean")
un=$(grep ': error' <<<"$out" | sed -E 's/.*Unknown identifier `([^`]*)`.*/\1/; s/.*error[^:]*: (.*)/OTHER: \1/' | sort | uniq)
echo; echo "$n tokens; $(grep -c . <<<"$un") do not resolve:"
echo '```'; tr '\n' ' ' <<<"$un" | fold -s -w 98; echo; echo '```'
echo "(Maintainer classification: bound variables of the statements and sketches; module names;"
echo "\`done\`, the writer's and the seeks' exit constructor; \`start\`, the core contract's local name.)"
echo
echo "## 8. Nothing in the repository was changed"
echo
echo "\`GIT_OPTIONAL_LOCKS=0 git status --porcelain --untracked-files=no\` in the checkout (no index refresh):"
st=$(cd "$WT" && GIT_OPTIONAL_LOCKS=0 git status --porcelain --untracked-files=no | head -5)
echo '```'; echo "${st:-(clean)}"; echo '```'
[ -z "$st" ]; check "checkout unchanged (tracked files)" $?
echo "All outputs are under <OUT>. Git ran read-only (rev-parse, ls-tree, archive to stdout, diff, status"
echo "with optional locks off). No lake or elan command was run; \`lean\` ran only through"
echo "\`tools/leanelab.sh\`, which writes no olean; Python ran only as \`python3 -I\`."
} > "$L/elaboration.log"

# ---------- cut check and landing form
{
echo "# C1 guess-then-run assembly statement gate: cut check"; echo; echo "$HDR"; echo
echo "\`python3 -I <OUT>/scripts/mklanded.py <OUT>/base <OUT>/C1Assembly.lean <OUT>\` writes the cut"
echo "file (the tip's \`Build/NDHost.lean\` byte for byte, plus one import, plus the part) and the"
echo "landing form (the same with the module docstring's lists extended)."
echo '```'; echo "$MKL" | san; echo '```'
for f in cut/NDHost.check.lean landed/TCSlib/Complexity/TuringMachine/Build/NDHost.lean; do
  out=$(el "$O/$f"); ex=$?
  echo "* \`<OUT>/$f\` ($(wc -l < "$O/$f" | tr -d ' ') lines; imports: $(grep '^import' "$O/$f" | cut -d' ' -f2 | tr '\n' ' ')):"
  summ "$out" "$ex"; echo '```'; san <<<"$out"; echo '(end of output)'; echo '```'
  [ "$ex" -eq 0 ] && [ "$(cnt ': error' "$out")" -eq 0 ]; check "$f: 0 errors" $?
  [ "$(cnt ': warning' "$out")" -eq "$(cnt "declaration uses 'sorry'" "$out")" ] && \
    [ "$(cnt "declaration uses 'sorry'" "$out")" -eq 1 ]; check "$f: only warning is the writer's sorry" $?
done
echo "The one \`sorry\` warning is \`Turing.ndWriterTM_run_block\` (line 178 of the tip's file, 195 of"
echo "the landed file), already sorried at the tip."
} > "$L/cutcheck.log"

# ---------- freeze
{
echo "# C1 guess-then-run assembly statement gate: freeze check of Build/NDHost.lean"; echo; echo "$HDR"; echo
echo "SHA-256: tip NDHost     $(shasum -a 256 "$BASE/TCSlib/Complexity/TuringMachine/Build/NDHost.lean" | cut -d' ' -f1)"
echo "         landed NDHost  $(shasum -a 256 "$O/landed/TCSlib/Complexity/TuringMachine/Build/NDHost.lean" | cut -d' ' -f1)"
echo '```'
python3 -I "$SC/freeze_ndhost.py" "$BASE/TCSlib/Complexity/TuringMachine/Build/NDHost.lean" \
  "$O/landed/TCSlib/Complexity/TuringMachine/Build/NDHost.lean" "$O/C1Assembly.lean"; r=$?
echo "freeze_ndhost.py exit $r"; echo '```'
check "freeze: NDHost's existing code and text unchanged" $r
echo
echo "Raw diff, the tip's NDHost against the landing form, up to the appended part (the module"
echo "docstring edits and the import line):"
python3 -I - "$O" <<'PY'
import sys
O = sys.argv[1]
u = open(O + "/C1Assembly.lean", encoding="utf-8").read().split("\n")
last = max(i for i, l in enumerate(u) if l.startswith("-- @imports "))
part = "\n".join(u[last + 1:]).strip("\n") + "\n"
b = open(O + "/landed/TCSlib/Complexity/TuringMachine/Build/NDHost.lean", encoding="utf-8").read()
assert b.endswith("\n" + part)
open(O + "/work/landed_head.lean", "w", encoding="utf-8").write(b[:-len("\n" + part)])
PY
echo '```diff'
diff -u "$BASE/TCSlib/Complexity/TuringMachine/Build/NDHost.lean" "$O/work/landed_head.lean" | san | tail -n +3
echo '```'
echo
echo "No other repository file changes: the landing touches \`Build/NDHost.lean\` only (records and the"
echo "design registry aside)."
} > "$L/freeze.log"

# ---------- axioms
{
echo "# C1 guess-then-run assembly statement gate: axiom prints"; echo; echo "$HDR"; echo
echo "## 1. Every new public declaration, the derived instances, and the cited lemmas"
echo
echo "\`<OUT>/probes/C1AssemblyAxioms.lean\` is the unit followed by \`scripts/axioms_tail.lean.txt\`."
out=$(el "$O/probes/C1AssemblyAxioms.lean"); ex=$?
summ "$out" "$ex"; echo '```'; san <<<"$out"; echo '```'
[ "$ex" -eq 0 ]; check "axioms probe elaborates" $?
sa=$(grep "sorryAx" <<<"$out" | sed -E "s/^'([^']*)'.*/\1/" | sort | tr '\n' ' ')
echo "Declarations with \`sorryAx\`: $sa"
[ "$sa" = "Turing.guessRunTM_accepts_iff Turing.guessRunTM_haltsWithin Turing.guessRunTM_runWith Turing.guessRunTM_runWith_handoff Turing.guessRunTM_runWith_live Turing.guessRunTM_silent_spec Turing.ndWriterTM_run_block " ]
check "sorryAx exactly on the six run theorems and the writer's contract" $?
echo
echo "## 2. Isolation of the sorry sources"
echo
echo "\`<OUT>/scripts/isolate.py\` copies a file and replaces each use of the two sorried contracts by an"
echo "axiom whose statement is the tip's statement, verbatim (\`isoWriterBlock\` for"
echo "\`Turing.ndWriterTM_run_block\`, \`isoInterpreterCore\` for \`Turing.exists_ndInterpreterCore\`)."
echo "The prints then name the contracts each theorem rests on, in place of \`sorryAx\`."
for f in C1Assembly AssemblyConsumerProbe; do
  python3 -I "$SC/isolate.py" "$BASE" "$O/$f.lean" "$O/work/Iso$f.lean" | san
  out=$(el "$O/work/Iso$f.lean"); ex=$?
  echo "* \`<OUT>/work/Iso$f.lean\`:"; summ "$out" "$ex"; echo '```'; san <<<"$out" | tr -d '\n' | sed "s/'Turing/\n'Turing/g"; echo; echo '```'
  [ "$ex" -eq 0 ] && ! grep -q sorryAx <<<"$out"; check "isolation $f: no sorryAx" $?
done
} > "$L/axioms.log"

# ---------- names
{
echo "# C1 guess-then-run assembly statement gate: name screen"; echo; echo "$HDR"; echo
echo "Pending units and drafts screened: every \`*.lean.txt\` under \`audits/evidence/\` at the tip; the"
echo "scratchpad's gate units of MIG-1 round 2, the ARM fill gate and the B6 hosts; and the landing trees"
echo "of the two open PRs, #92 (the B6 hosts, \`<S>/land-b6r/tree\`) and #93 (the ARM minor fixes,"
echo "\`<S>/armfix/tree\`)."
drafts=(); while IFS= read -r f; do drafts+=("$f"); done < <(find "$BASE/audits/evidence" -name '*.lean.txt' | sort)
extra=(); while IFS= read -r f; do extra+=("$f"); done < <(find "$S/gate-mig1-r2" "$S/gate-arm" "$S/gate-b6hosts" -maxdepth 2 -name '*.lean' 2>/dev/null | sort)
prs=(); while IFS= read -r f; do prs+=("$f"); done < <(find "$S/land-b6r/tree" "$S/armfix/tree" -name '*.lean' 2>/dev/null | sort)
echo "(${#drafts[@]} repository drafts, ${#extra[@]} scratchpad gate units, ${#prs[@]} open-PR files)"
echo '```'
python3 -I "$SC/names_asm.py" "$O/C1Assembly.lean" "$BASE" "${drafts[@]}" "${extra[@]}" "${prs[@]}" | san; r=${PIPESTATUS[0]}
echo '```'
check "names: no clash" $r
echo "Positive control (\`<OUT>/work/screen_ctrl.lean\` declares two existing full names):"
echo '```'; po=$(python3 -I "$SC/names_asm.py" "$O/work/screen_ctrl.lean" "$BASE" | san); echo "$po"; echo '```'
[ "$(grep -c '   CLASH' <<<"$po")" -eq 2 ]; check "names: positive control catches both" $?
echo
echo "In-closure check: the unit, the cut file and the landed file elaborate (elaboration and cut logs),"
echo "so no new name clashes with anything in \`Build.NDHost\`'s import closure plus \`Build.Catalog\`."
echo "Downstream of \`Build.NDHost\` there is only the \`TCSlib.Complexity.TuringMachine\` facade:"
echo '```'
python3 -I - "$BASE" <<'PY'
import os, sys
wt = sys.argv[1]; imps = {}
for d, _, fs in os.walk(os.path.join(wt, "TCSlib")):
    for f in fs:
        if f.endswith(".lean"):
            p = os.path.join(d, f); m = os.path.relpath(p, wt)[:-5].replace("/", ".")
            imps[m] = [l.split()[1] for l in open(p, encoding="utf-8") if l.startswith("import ")]
def clo(m, seen):
    if m in seen: return seen
    seen.add(m)
    for x in imps.get(m, []): clo(x, seen)
    return seen
nd = "TCSlib.Complexity.TuringMachine.Build.NDHost"; cat = "TCSlib.Complexity.TuringMachine.Build.Catalog"
down = sorted(m for m in imps if m != nd and nd in clo(m, set()))
print(f"{len(imps)} modules; with Build.NDHost in their closure: {down}")
print("of these, without Build.Catalog in their closure:", [m for m in down if cat not in clo(m, set())])
print("Build.NDHost in Build.Catalog's closure (a cycle at landing):", nd in clo(cat, set()))
PY
echo '```'
echo
echo "Open PRs against the unit's closure (the landed NDHost's imports, and the probes' extra imports):"
echo '```'
python3 -I - "$BASE" "$S" <<'PY'
import os, sys
base, S = sys.argv[1], sys.argv[2]; imps = {}
for d, _, fs in os.walk(os.path.join(base, "TCSlib")):
    for f in fs:
        if f.endswith(".lean"):
            p = os.path.join(d, f); m = os.path.relpath(p, base)[:-5].replace("/", ".")
            imps[m] = [l.split()[1] for l in open(p, encoding="utf-8") if l.startswith("import ")]
def clo(m, seen):
    if m in seen: return seen
    seen.add(m)
    for x in imps.get(m, []): clo(x, seen)
    return seen
c = set()
for m in ["TCSlib.Complexity.TuringMachine.Build.NDHost", "TCSlib.Complexity.TuringMachine.Build.Catalog"]:
    clo(m, c)
pr = set(c)
for m in ["TCSlib.Complexity.TuringMachine.NDCodeSimulator", "TCSlib.Complexity.ClassNP.NTIME",
          "TCSlib.Complexity.Diagonalization.NTimeHierarchy", "TCSlib.Complexity.TuringMachine.Build.OracleCall"]:
    clo(m, pr)
print(f"closure of the landed NDHost: {len(c)} modules; with the probes' extra imports: {len(pr)}")
for name, root in [("#92 (<S>/land-b6r/tree)", S + "/land-b6r/tree"), ("#93 (<S>/armfix/tree)", S + "/armfix/tree")]:
    fs = [os.path.relpath(os.path.join(d, f), root)[:-5].replace("/", ".")
          for d, _, ff in os.walk(root) for f in ff if f.endswith(".lean")]
    print(f"{name}: {len(fs)} files; in the landed NDHost's closure: {sorted(set(fs) & c)}; "
          f"in the probes' closure: {sorted(set(fs) & pr)}")
PY
echo '```'
} > "$L/names.log"

echo "failed checks: $FAILS" >> "$L/summary.txt"
cat "$L/summary.txt"
[ "$FAILS" -eq 0 ]
