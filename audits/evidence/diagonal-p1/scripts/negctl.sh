#!/usr/bin/env bash
# Negative controls: each check must FAIL on a deliberately broken input (fail-closed evidence).
# Usage: bash negctl.sh <S> <D>. Writes work/negctl/; prints one line per control.
set -uo pipefail
S="$1"; D="$2"; SC="$D/scripts"; N="$D/work/negctl"; L="$D/tree/TCSlib/Complexity/TimeHierarchy/Diagonal.lean"
B="$D/base/TCSlib/Complexity/TimeHierarchy/Diagonal.lean"
rm -rf "$N"; mkdir -p "$N"
mut() {  # mut <out> <old> <new>: asserted single replacement on a copy of the landed file
  python3 -I - "$L" "$1" "$2" "$3" <<'PY'
import sys
src, out, old, new = sys.argv[1:5]
s = open(src, encoding="utf-8").read()
assert s.count(old) == 1, f"mutation anchor occurs {s.count(old)} times: {old!r}"
open(out, "w", encoding="utf-8").write(s.replace(old, new))
PY
}
expect_fail() {  # expect_fail <label> <command...>
  local label="$1"; shift
  if "$@" > "$N/$label.out" 2>&1; then echo "NEGCTL $label: check PASSED on broken input — FAIL"; return 1
  else echo "NEGCTL $label: check failed as required — PASS"; fi
}
rc=0
mut "$N/freeze-head.lean" "    diagLang g ∈ DTIME (fun n => g n + 1) :=" "    diagLang g ∈ DTIME (fun n => g n + 2) :="
expect_fail freeze-head python3 -I "$SC/freeze.py" "$B" "$N/freeze-head.lean" || rc=1
mut "$N/freeze-sorry.lean" "  sqDiagSimulator.diagLang_not_mem_DTIME hT" "  sorry"
expect_fail freeze-sorry python3 -I "$SC/freeze.py" "$B" "$N/freeze-sorry.lean" || rc=1
mut "$N/hygiene-tab.lean" "theorem le_sq_overhead (t n : ℕ)" "theorem le_sq_overhead	(t n : ℕ)"
expect_fail hygiene-tab python3 -I "$SC/hygiene.py" "$B" "$N/hygiene-tab.lean" || rc=1
mkdir -p "$N/nameroot/TCSlib"; printf 'def DiagSimulator := 0\n' > "$N/nameroot/TCSlib/X.lean"; : > "$N/nameroot/TCSlib.lean"
expect_fail names-hit python3 -I "$SC/names.py" "$N/nameroot" "$B" "$L" || rc=1
printf "'X' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]\n" > "$N/ax.out"
expect_fail axioms-sorry python3 -I "$SC/axcheck.py" "$N/ax.out" 1 || rc=1
# cut-check control: drop the generic positive-bound theorem's name, so the landed
# `time_hierarchy_of_pos` no longer elaborates; the Separation cut must report an error.
mkdir -p "$N/tree/TCSlib/Complexity/TimeHierarchy"
mut "$N/tree/TCSlib/Complexity/TimeHierarchy/Diagonal.lean" \
  "  sqDiagSimulator.time_hierarchy_of_pos le_sq_overhead hg hpos hfg" \
  "  sqDiagSimulator.time_hierarchy_of_pos_missing le_sq_overhead hg hpos hfg"
grep "TimeHierarchy.Separation:" "$D/work/graph/chains.txt" > "$N/chains.txt"
python3 -I "$SC/cutcheck.py" "$D/base" "$N/tree" "$N/chains.txt" "$N/cut" > /dev/null
bash "$S/tools/leanelab.sh" "$S/wt-u2" "$S/oleans-lh1" "$N/cut/TimeHierarchy.Separation.cut.lean" \
  > "$N/cut-separation.lean.out" 2>&1 || true
if grep -q "error" "$N/cut-separation.lean.out"; then
  echo "NEGCTL cut-separation: the cut check reports the broken landed text — PASS"
else echo "NEGCTL cut-separation: no error reported — FAIL"; rc=1; fi
exit $rc
