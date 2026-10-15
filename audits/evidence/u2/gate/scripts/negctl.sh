#!/usr/bin/env bash
# Negative controls of the U2 gate: each check must FAIL on a deliberately broken input.
# Usage: bash negctl.sh <S> <G> <olean snapshot>. Writes work/negctl/; one line per control.
set -uo pipefail
S="$1"; G="$2"; OL="$3"; SC="$G/scripts"; N="$G/work/negctl"; TM=TCSlib/Complexity/TuringMachine
rm -rf "$N"; mkdir -p "$N"
mutroot() {  # mutroot <name> <file rel> <old> <new>: a copy of landed/ with one asserted edit
  rm -rf "$N/$1"; cp -R "$G/landed" "$N/$1"
  python3 -I - "$N/$1/$2" "$3" "$4" <<'PY'
import sys
p, old, new = sys.argv[1:4]
s = open(p, encoding="utf-8").read()
assert s.count(old) == 1, f"mutation anchor occurs {s.count(old)} times"
open(p, "w", encoding="utf-8").write(s.replace(old, new))
PY
  [ $? -eq 0 ] || { echo "NEGCTL $1: the mutation did not apply — FAIL"; exit 1; }
}
expect_fail() { local label="$1"; shift
  if "$@" > "$N/$label.out" 2>&1; then echo "NEGCTL $label: check PASSED on broken input — FAIL"; return 1
  else echo "NEGCTL $label: check failed as required — PASS"; fi; }
rc=0
mutroot sig "$TM/SelfUniversal.lean" "∃ U₀ : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, 0 < C ∧" "∃ U₀ : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, 1 < C ∧"
expect_fail freeze-signature python3 -I "$SC/freeze.py" "$G/base" "$N/sig" || rc=1
mutroot sry "$TM/Codes2Tape.lean" "  rw [tableBitsK_two]
  simp only [codeTable2Bits, actionBits₂_eq_actionBitsK]" "  sorry"
expect_fail freeze-sorry python3 -I "$SC/freeze.py" "$G/base" "$N/sry" || rc=1
mutroot vis "$TM/Build/StepBlockLoop.lean" "theorem loopTM_run {k n : ℕ}" "private theorem loopTM_run {k n : ℕ}"
expect_fail freeze-visibility python3 -I "$SC/freeze.py" "$G/base" "$N/vis" || rc=1
rm -rf "$N/nameroot"; cp -R "$G/base" "$N/nameroot"; printf 'def universalK := 0\n' > "$N/nameroot/TCSlib/X.lean"
expect_fail names-hit python3 -I "$SC/names.py" "$N/nameroot" "$G/landed" || rc=1
mutroot wide "$TM/UniversalK.lean" "/-- The bundled machine a string denotes" "/-- The bundled machine a string denotes, padded to make this line wider than one hundred characters"
expect_fail widths python3 -I "$SC/hygiene.py" "$G/base" "$N/wide" || rc=1
printf "'Turing.EffectiveCodeK' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]\n" > "$N/ax.out"
: > "$N/ax.lean"
expect_fail axioms-sorry python3 -I "$SC/check_diag.py" "$N/ax.lean" "$N/ax.out" "sorried=;std=Turing.EffectiveCodeK;sorryAx=" || rc=1
# cut control: break the k = 1 corollary's proof; the SelfUniversal cut must report an error
mutroot cut "$TM/SelfUniversal.lean" "  exact hsp.trans (Nat.mul_le_mul_left C (by omega))" "  exact hsp"
python3 -I "$SC/mkcuts.py" "$G/base" "$N/cut" "$G/inputs/Diagonal.p1.lean" "$G/probes" "$N/cuts" > /dev/null
bash "$S/tools/leanelab.sh" "$S/wt-u2" "$OL" "$N/cuts/SelfUniversal.cut.lean" > "$N/cut.lean.out" 2>&1 || true
if grep -q "error" "$N/cut.lean.out"; then echo "NEGCTL cut-selfuniversal: the cut check reports the broken proof — PASS"
else echo "NEGCTL cut-selfuniversal: no error reported — FAIL"; rc=1; fi
exit $rc
