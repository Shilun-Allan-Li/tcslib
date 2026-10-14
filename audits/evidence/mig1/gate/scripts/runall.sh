#!/usr/bin/env bash
# MIG-1 statement gate: rebuild every artifact and rerun every check (read-only on the worktree).
# Usage: [MIG0B_LANDING=<dir>] bash runall.sh <worktree> <olean snapshot> <leanelab.sh> <gate dir>
# Writes <gate dir>/logs/mig1-statements-{elaboration,identity,axioms,cutcheck,names,
# consumers,replay}.log. Elaboration goes only through leanelab.sh (no olean output).
set -u
WT="$1"; OL="$2"; ELAB="$3"; G="$4"
cd "$G" || exit 1
P="python3 -I"
mkdir -p logs cuts data work probes lintdir
LOG=logs/mig1-statements-elaboration.log
: > "$LOG"
say() { printf '%s\n' "$*" | tee -a "$LOG"; }
elab() {  # elab <label> <file>
  local out="work/$(basename "$2").out"
  bash "$ELAB" "$WT" "$OL" "$G/$2" > "$out" 2>&1
  local e=$?
  say "$1: $2 -- exit $e; errors $(grep -c ': error' "$out"); 'declaration uses sorry' warnings $(grep -c "declaration uses 'sorry'" "$out"); other warnings $(grep ': warning' "$out" | grep -vc "declaration uses 'sorry'"); lines $(wc -l < "$2" | tr -d ' ')"
}
say "# MIG-1 statement gate, elaboration log"
say "worktree HEAD: $(cat "$(sed -n 's/^gitdir: //p' "$WT/.git")/HEAD" 2>/dev/null) (read from the git metadata file; no git command)"
say "olean snapshot: $OL; toolchain file: $(cat "$WT/lean-toolchain")"
say ""
say "## 1. Build of the unit and the probes from their templates (scripts/build_unit.py)"
$P scripts/build_unit.py "$WT" parts MIG1Statements.lean && say "built MIG1Statements.lean"
$P scripts/build_unit.py "$WT" probe-parts work/probe-tail.lean && cat MIG1Statements.lean work/probe-tail.lean > probes/SpecProbe.lean && say "built probes/SpecProbe.lean (the unit followed by the spec-probe tail)"
$P scripts/build_unit.py "$WT" bridge-parts probes/BridgeProbe.lean && say "built probes/BridgeProbe.lean"
say ""
say "## 2. Elaboration"
elab "unit" MIG1Statements.lean
elab "spec probe" probes/SpecProbe.lean
elab "bridge probe" probes/BridgeProbe.lean
say ""
say "## 3. Cut checks (scripts/cutcheck.py, from audits/evidence/stage2-gate/scripts/)"
rm -f cuts/*.check.lean
$P scripts/cutcheck.py MIG1Statements.lean "$WT" cuts > logs/mig1-statements-cutcheck.log
cat logs/mig1-statements-cutcheck.log >> "$LOG"
for f in cuts/*.check.lean; do elab "cut" "$f"; done
grep "^cut" "$LOG" >> logs/mig1-statements-cutcheck.log
say ""
say "## 4. Identity (scripts/identity.py) and its negative controls"
$P scripts/identity.py "$WT" MIG1Statements.lean scripts/identity-manifest.json work/probe-tail.lean probes/BridgeProbe.lean > logs/mig1-statements-identity.log
say "identity: exit $? ($(tail -1 logs/mig1-statements-identity.log))"
$P - <<'EOF'
s = open('MIG1Statements.lean').read()
for a, b in [("            controlAction .neg (some (.inr (.inr (.inl (b, true)))))",
              "            controlAction .pos (some (.inr (.inr (.inl (b, true)))))"),
             ("(prependTM w).ComputesFunInTime (fun x => w ++ x) (fun n => w.length + n + 1) := by",
              "(prependTM w).ComputesFunInTime (fun x => w ++ x) (fun n => w.length + n + 2) := by"),
             ("          | some _ => act 0 none (none, .neg) (none, .neg) none (some (ctrl 3))",
              "          | some _ => act 0 none (none, .neg) (none, .pos) none (some (ctrl 3))")]:
    assert s.count(a) == 1, a
    s = s.replace(a, b)
open('work/mutant.lean', 'w').write(s)
EOF
$P scripts/identity.py "$WT" work/mutant.lean scripts/identity-manifest.json work/probe-tail.lean probes/BridgeProbe.lean > work/identity-control.out
say "negative controls (three single-token mutations: a timedCondTM transition, the prependTM_computes bound, a loopHostM transition): $(grep -c '^FAIL' work/identity-control.out) failures, expected 3"
{ echo; echo "## negative controls"; grep '^FAIL' work/identity-control.out; } >> logs/mig1-statements-identity.log
say ""
say "## 5. Axioms (probes/AxiomProbe.lean: the unit followed by #print axioms of its public declarations)"
$P scripts/gatenames.py MIG1Statements.lean --public > work/gate-public.txt
{ cat MIG1Statements.lean; printf '\n/-! Axiom probe (not landed): every public declaration of the unit. -/\n\n'; awk '{print "#print axioms " $4}' work/gate-public.txt; } > probes/AxiomProbe.lean
bash "$ELAB" "$WT" "$OL" "$G/probes/AxiomProbe.lean" > work/axioms.out 2>&1
say "axiom probe: exit $?"
$P - <<'EOF' > logs/mig1-statements-axioms.log
import re
t = open('work/axioms.out').read()
items = re.findall(r"'([^']+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", t, re.S)
std = {'propext', 'Classical.choice', 'Quot.sound'}
res = [(n, [a.strip() for a in ax.replace('\n', ' ').split(',') if a.strip()]) for n, _, ax in items]
print(f'declarations reported: {len(res)}')
print(f'non-standard axioms (other than propext, Classical.choice, Quot.sound, sorryAx): '
      f'{[n for n, a in res if set(a) - std - {"sorryAx"}]}')
print(f'with sorryAx: {sum(1 for _, a in res if "sorryAx" in a)}; '
      f'sorry-free: {sum(1 for _, a in res if "sorryAx" not in a)}')
print()
for n, a in res:
    print(f"{n}: {', '.join(a) if a else '(none)'}")
EOF
head -3 logs/mig1-statements-axioms.log >> "$LOG"
say ""
say "## 6. Names (scripts/namescreen.py)"
$P - <<'EOF'
import json
lines = open('MIG1Statements.lean').read().split('\n')
json.dump({l.split()[2].split('.')[-1]: i for i, l in enumerate(lines, 1)
           if l.startswith('-- @landing ')}, open('work/part-lines.json', 'w'))
EOF
$P scripts/namescreen.py "$WT" work/gate-public.txt data/moved-names.json logs/mig1-statements-names.log | tail -1 | tee -a "$LOG"
if [ -n "${MIG0B_LANDING:-}" ]; then  # optional: MIG-0b's round-2 landing set (not in the worktree)
  { echo; echo "## 6. The MIG-0b round-2 landing set ($MIG0B_LANDING)"; \
    $P scripts/namescreen_extra.py "$MIG0B_LANDING" work/gate-public.txt data/moved-names.json; } \
    >> logs/mig1-statements-names.log
  tail -3 logs/mig1-statements-names.log | tee -a "$LOG"
fi
say ""
say "## 7. Widths and style"
$P scripts/widths.py MIG1Statements.lean probes/SpecProbe.lean probes/BridgeProbe.lean | tail -1 | tee -a "$LOG"
rm -f lintdir/*.lean; cp MIG1Statements.lean probes/SpecProbe.lean probes/BridgeProbe.lean lintdir/
$P scripts/campaign_style_lint.py lintdir 2>&1 | tail -6 | tee -a "$LOG"
say ""
say "## 8. Consumers of the rows (scripts/consumers.py) and replay closure (scripts/importgraph.py)"
$P scripts/consumers.py "$WT" work/consumer-names.json data/consumers.json > logs/mig1-statements-consumers.log
tail -1 logs/mig1-statements-consumers.log | tee -a "$LOG"
T=TCSlib.Complexity
{
  for set in "whole MIG-1 (ten files):$T.TuringMachine.Simulation $T.TuringMachine.Composition $T.TuringMachine.Build.Wrappers $T.TuringMachine.Encoding $T.ClassP.TimeConstructible $T.TuringMachine.Build.Loop $T.TuringMachine.Build.Primitives $T.TuringMachine.Build.Catalog $T.TuringMachine.Build.CertShell $T.TuringMachine.CodeSimulator" \
             "PR S (statements):$T.TuringMachine.Simulation $T.TuringMachine.Composition $T.TuringMachine.Build.Wrappers $T.TuringMachine.Encoding $T.ClassP.TimeConstructible $T.TuringMachine.Build.Loop $T.TuringMachine.Build.Primitives $T.TuringMachine.Build.Catalog" \
             "F-A:$T.TuringMachine.Composition $T.TuringMachine.Simulation $T.TuringMachine.Build.Wrappers $T.TuringMachine.Encoding $T.ClassP.TimeConstructible" \
             "F-B:$T.TuringMachine.Build.Primitives" \
             "F-C:$T.TuringMachine.Build.Loop" \
             "F-D:$T.TuringMachine.Build.Catalog $T.TuringMachine.Build.CertShell $T.TuringMachine.CodeSimulator" \
             "F-D without CodeSimulator:$T.TuringMachine.Build.Catalog $T.TuringMachine.Build.CertShell"; do
    echo "== ${set%%:*}"
    mods=${set#*:}
    # shellcheck disable=SC2086
    $P scripts/importgraph.py "$WT" replay $mods
  done
} > logs/mig1-statements-replay.log
grep -A1 "^==" logs/mig1-statements-replay.log | grep -v "^--" | paste - - | tee -a "$LOG"
say ""
say "## 9. Deletion plan (scripts/region.py)"
$P scripts/region.py "$WT" data | tee -a "$LOG" > /dev/null
say ""
say "done"
