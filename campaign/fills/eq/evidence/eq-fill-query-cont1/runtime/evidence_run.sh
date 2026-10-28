#!/usr/bin/env bash
# Checkpoint evidence on the owned module as it stands (one Lean process at a time):
# 1. the elaborated-constant walk (scratch copy + walk_tail.lean) -> <out>/walk.out;
# 2. the seal test: gen_seal.py, then the controls file and the sealed copy -> controls.out,
#    sealed.out;
# 3. the axiom prints (scratch copy + `#print axioms` for the target and every new private)
#    -> axioms.out.
# Usage: evidence_run.sh <outdir>
set -u
ROOT=/home/user/tcslib
cd $ROOT
export PATH=$HOME/.elan/bin:$PATH
OUT="$1"; mkdir -p "$OUT"
F=TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.lean
S=evidence/seal
run() { # module-path log
  { echo "\$ bash scripts/lean_check_tree.sh $1"; echo "start=$(date -u +%FT%TZ)";
    bash scripts/lean_check_tree.sh "$1"; echo "exit=$? end=$(date -u +%FT%TZ)"; } > "$2" 2>&1
}
cat $F $S/walk_tail.lean > $S/QyWalk.lean
run $S/QyWalk "$OUT/walk.out"
python3 -I evidence/runtime/gen_seal.py $F "$OUT/walk.out" $S
cp $S/sealed-names.txt $S/QySealed.lean $S/QySealControls.lean "$OUT/"
run $S/QySealControls "$OUT/controls.out"
run $S/QySealed "$OUT/sealed.out"
python3 -I - "$F" "$S/QyAxioms.lean" <<'PY'
import re, sys
src = open(sys.argv[1]).read().split("\n")
i0 = next(i for i, l in enumerate(src) if l.startswith("private theorem qy_query_of_main"))
names = []
for l in src[i0 + 1:]:
    m = re.match(r"^private (?:noncomputable )?(?:theorem|lemma|def|abbrev|inductive|structure|instance) "
                 r"(\S+)", l)
    if m:
        names.append(m.group(1))
assert src[-2] == "end Turing.NTimeDiag"
body = src[:-2] + ["", "#print axioms exists_queryTM"] + \
    [f"#print axioms {n}" for n in names] + src[-2:]
open(sys.argv[2], "w").write("\n".join(body))
print(f"axiom prints: target + {len(names)} privates")
PY
run $S/QyAxioms "$OUT/axioms.out"
cp $S/QyAxioms.lean "$OUT/"
echo "walk: $(grep QYWALK "$OUT/walk.out")"
echo "controls: closes=$(grep -c 'closes by rfl' "$OUT/controls.out") errors=$(grep -cE ':[0-9]+:[0-9]+: error' "$OUT/controls.out") sealed=$(wc -l < $S/sealed-names.txt)"
echo "sealed copy: $(grep -cE 'QySealed.lean:[0-9]+:[0-9]+: error' "$OUT/sealed.out") errors; $(grep -c "declaration uses 'sorry'" "$OUT/sealed.out") sorry warnings; $(tail -1 "$OUT/sealed.out")"
echo "axioms: $(grep -c "depends on axioms\|does not depend" "$OUT/axioms.out") prints; sorryAx in $(grep -c sorryAx "$OUT/axioms.out")"
# 4. the import probe, extended by the walk's citations
python3 -I evidence/runtime/gen_probe.py \
  campaign/fills/eq/inputs/eq-fill-query-cont1/EQImportProbe.lean.txt "$OUT/walk.out" \
  evidence/probes/QyImportProbe.lean > "$OUT/probe-gen.txt"
run evidence/probes/QyImportProbe "$OUT/probe.out"
cp evidence/probes/QyImportProbe.lean "$OUT/"
echo "probe: $(cat "$OUT/probe-gen.txt"); $(grep -c '^#check' evidence/probes/QyImportProbe.lean) checks of $(grep '^#check' evidence/probes/QyImportProbe.lean | sort -u | wc -l) names; errors=$(grep -cE ':[0-9]+:[0-9]+: error' "$OUT/probe.out"); $(tail -1 "$OUT/probe.out")"
# 5. the inspection table
python3 -I evidence/runtime/gen_inspect.py $F 43fe918f $S > "$OUT/inspect-gen.txt"
run $S/QyInspect "$OUT/inspect.out"
python3 -I evidence/runtime/inspect_table.py $S/inspect-idents.tsv "$OUT/inspect.out" \
  "$OUT/inspection-table.md" > "$OUT/inspection-summary.txt"
echo "inspection: $(cat "$OUT/inspect-gen.txt")"; cat "$OUT/inspection-summary.txt"
# 6. lint
python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/Diagonalization > "$OUT/lint.log" 2>&1
echo "lint: $(tail -1 "$OUT/lint.log")"
# 7. rule 11 grep: the six R3 rows and other files' private names in the diff
git diff 43fe918f -- $F | grep '^+' | grep -nE '\b(copyTM_run|transferTM_run|clearTM_run|compareTM_run|incrementTM_run_succ|incrementTM_run_overflow)\b' > "$OUT/rule11-grep.txt"
echo "rule 11 (R3 rows in the diff): $(wc -l < "$OUT/rule11-grep.txt") hits; walk private names: $(grep -c _private "$OUT/walk.out")"
