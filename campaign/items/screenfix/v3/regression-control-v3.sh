#!/usr/bin/env bash
# Regression control for the copy-text screen's same-name defect (Diagonal Part 1 gate, m2).
# One file holds three pairs of distinct declarations with the same extracted name:
#   N1.dup / N2.dup              the same name in two namespaces;
#   A.B.gen / A.gen              a generic proof beside a same-named received one, the first in a
#                                dotted `namespace A.B` closed by `end B`, `end A` (as in Lean);
#   two anonymous instances      whose extracted "name" is the next token, `:`.
# Expected: the old screen (v2) reports none of them; the fixed screen (v3) reports all three in
# both directions, with namespace-qualified labels (`#k` for the instances), and never a
# declaration paired with itself. (The screen's bodies run to the next declaration, so the
# closing `end`/`namespace` commands are part of them and the ratios are below 100%.)
# Exits 0 only if both expectations hold.
# Usage: bash regression-control-v3.sh <old-screen.py> <new-screen.py> <empty-scratch-dir>
set -u
old=$1; new=$2; d=$3
mkdir -p "$d" || exit 2
[ -z "$(ls -A "$d")" ] || { echo "scratch dir not empty: $d" >&2; exit 2; }
mkdir -p "$d/Diag"
cat > "$d/Diag/Machine.lean" <<'EOF'
namespace N1
def dup : List Nat := [201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]
end N1
namespace N2
def dup : List Nat := [201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]
end N2

namespace A.B
theorem gen : (1 : Nat) + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 = 55 := by
  show (1 : Nat) + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 = 55
  simp only [Nat.add_eq, Nat.add_assoc, Nat.add_comm]
  rfl
end B
end A

namespace A
theorem gen : (1 : Nat) + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 = 55 := by
  show (1 : Nat) + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 = 55
  simp only [Nat.add_eq, Nat.add_assoc, Nat.add_comm]
  rfl
end A

instance : Inhabited (List Nat) := ⟨[301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318]⟩
instance : Inhabited (List Nat) := ⟨[301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318]⟩
EOF
o=$(python3 -I "$old" "$d" Diag/Machine.lean) || exit 2
n=$(python3 -I "$new" "$d" Diag/Machine.lean) || exit 2
printf '## old screen\n%s\n## new screen\n%s\n' "$o" "$n"
ok=0
printf '%s\n' "$o" | head -1 | grep -qF 'copy pairs (target reproduces >= half of source): 0;' \
  || { echo "FAIL: the old screen reports a pair (control not reproduced)"; ok=1; }
for want in '   Machine.lean::N2.dup  reproduces  Machine.lean::N1.dup: ' \
            '   Machine.lean::N1.dup  reproduces  Machine.lean::N2.dup: ' \
            '   Machine.lean::A.gen  reproduces  Machine.lean::A.B.gen: ' \
            '   Machine.lean::A.B.gen  reproduces  Machine.lean::A.gen: ' \
            '   Machine.lean:::#2  reproduces  Machine.lean:::#1: ' \
            '   Machine.lean:::#1  reproduces  Machine.lean:::#2: '; do
  printf '%s\n' "$n" | grep -qF -- "$want" || { echo "FAIL: the new screen lacks: $want"; ok=1; }
done
printf '%s\n' "$n" | head -1 | grep -qF 'copy pairs (target reproduces >= half of source): 6;' \
  || { echo "FAIL: new pair count is not 6"; ok=1; }
printf '%s\n' "$n" | awk '$2 == "reproduces" && $1 == substr($3, 1, length($3) - 1) {f = 1} END {exit f}' \
  || { echo "FAIL: the new screen pairs a declaration with itself"; ok=1; }
[ $ok -eq 0 ] && echo "PASS: the old screen drops the three same-name pairs, the new screen reports them"
exit $ok
