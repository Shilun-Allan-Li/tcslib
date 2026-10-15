#!/usr/bin/env bash
# Negative controls: each check must FAIL on a deliberately broken input (fail-closed evidence).
# Usage: bash negctl.sh <S> <D> [<snapshot>] (default <S>/oleans-lh1). Writes work/negctl/;
# prints one line per control.
set -uo pipefail
S="$1"; D="$2"; OL="${3:-$S/oleans-lh1}"; SC="$D/scripts"; N="$D/work/negctl"; L="$D/tree/TCSlib/Complexity/TimeHierarchy/Diagonal.lean"
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
# gate m1: a fully qualified declaration, and a fully qualified reference, of new names
mkdir -p "$N/nameroot2/TCSlib"; : > "$N/nameroot2/TCSlib.lean"
printf 'def Complexity.TimeHierarchy.DiagSimulator := 0\n' > "$N/nameroot2/TCSlib/X.lean"
expect_fail names-qualified-decl python3 -I "$SC/names.py" "$N/nameroot2" "$B" "$L" || rc=1
mkdir -p "$N/nameroot3/TCSlib"; : > "$N/nameroot3/TCSlib.lean"
printf 'example : True := by\n  have := @Complexity.TimeHierarchy.SelfSimulator.normalForm\n  trivial\n' \
  > "$N/nameroot3/TCSlib/X.lean"
expect_fail names-qualified-ref python3 -I "$SC/names.py" "$N/nameroot3" "$B" "$L" || rc=1
# gate m2: restore the received `Complexity.time_hierarchy_of_pos` proof from the base beside the
# generic `DiagSimulator.time_hierarchy_of_pos` (same short name, same file); the screen must
# report a new pair against the base's screen
P=(); while read -r f; do P+=("$f"); done < "$SC/screen-population.txt"
for f in "${P[@]}"; do mkdir -p "$N/screenroot/$(dirname "$f")"; cp "$D/base/$f" "$N/screenroot/$f"; done
M="$N/screenroot/TCSlib/Complexity/TimeHierarchy/Diagonal.lean"; rm -f "$M"
python3 -I - "$B" "$L" "$M" <<'EOF' || { echo "NEGCTL screen-restore: mutation not built — FAIL"; rc=1; }
import sys
b = open(sys.argv[1], encoding="utf-8").read(); s = open(sys.argv[2], encoding="utf-8").read()
i = b.index("theorem time_hierarchy_of_pos {f g"); j = b.index("\nend Complexity", i)
recv = b[b.index("    DTIME f ⊂ DTIME g := by\n", i):j]
old = "    DTIME f ⊂ DTIME g :=\n  sqDiagSimulator.time_hierarchy_of_pos le_sq_overhead hg hpos hfg\n"
assert s.count(old) == 1, f"restore anchor occurs {s.count(old)} times"
open(sys.argv[3], "w", encoding="utf-8").write(s.replace(old, recv))
EOF
screen_no_new_pair() {  # the check under test; without the mutation it "passes", so the control fails
  [ -s "$M" ] || return 0
  nice -n 10 python3 -I "$SC/copy-text-screen-v3.py" "$D/base" "${P[@]}" > "$N/screen-base.txt" &&
  nice -n 10 python3 -I "$SC/copy-text-screen-v3.py" "$N/screenroot" "${P[@]}" > "$N/screen-restore.txt" &&
  python3 -I "$SC/screendelta.py" "$N/screen-base.txt" "$N/screen-restore.txt" | tee "$N/screen-delta.txt" |
    grep -q "new 0 (cross-file 0)"
}
expect_fail screen-restore screen_no_new_pair || rc=1
grep -q "in-file Diagonal.lean::Complexity.time_hierarchy_of_pos <- Diagonal.lean::Complexity.TimeHierarchy.DiagSimulator.time_hierarchy_of_pos" "$N/screen-delta.txt" \
  || { echo "NEGCTL screen-restore: the restored pair is not the one reported — FAIL"; rc=1; }
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
bash "$S/tools/leanelab.sh" "$S/wt-u2" "$OL" "$N/cut/TimeHierarchy.Separation.cut.lean" \
  > "$N/cut-separation.lean.out" 2>&1 || true
if grep -q "error" "$N/cut-separation.lean.out"; then
  echo "NEGCTL cut-separation: the cut check reports the broken landed text — PASS"
else echo "NEGCTL cut-separation: no error reported — FAIL"; rc=1; fi
exit $rc
