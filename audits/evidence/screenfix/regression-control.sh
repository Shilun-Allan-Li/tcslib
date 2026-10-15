#!/bin/zsh
# Regression control for the copy-text screen's basename defect.
# Two files with the same basename in different directories share a copied declaration under the
# same name (`shI`) and a copied proof under different names (`cpA`/`cpB`); one file also has two
# same-named declarations in two namespaces (`N1.dup`/`N2.dup`, the known residual, see NOTES).
# Expected: the old screen drops shI <-> shI (and labels cpA/cpB ambiguously); the fixed screen
# reports shI in both directions with repository paths. Exits 0 only if both expectations hold.
# Usage: zsh regression-control.sh <old-screen.py> <new-screen.py> <empty-scratch-dir>
set -u
old=$1; new=$2; d=$3
mkdir -p "$d" || exit 2
[ -z "$(ls -A "$d")" ] || { echo "scratch dir not empty: $d" >&2; exit 2; }
mkdir -p "$d/Codec" "$d/ExpBFS"
cat > "$d/Codec/Machine.lean" <<'EOF'
def shI : List Nat := [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117]

theorem cpA : (1 : Nat) + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 = 55 := by
  show (1 : Nat) + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 = 55
  simp only [Nat.add_eq, Nat.add_assoc, Nat.add_comm]
  rfl

namespace N1
def dup : List Nat := [201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]
end N1
namespace N2
def dup : List Nat := [201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]
end N2
EOF
cat > "$d/ExpBFS/Machine.lean" <<'EOF'
def shI : List Nat := [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117]

theorem cpB : (1 : Nat) + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 = 55 := by
  show (1 : Nat) + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 = 55
  simp only [Nat.add_eq, Nat.add_assoc, Nat.add_comm]
  rfl
EOF
o=$(python3 -I "$old" "$d" Codec/Machine.lean ExpBFS/Machine.lean) || exit 2
n=$(python3 -I "$new" "$d" Codec/Machine.lean ExpBFS/Machine.lean) || exit 2
print -r -- "## old screen"; print -r -- "$o"; print -r -- "## new screen"; print -r -- "$n"
ok=0
print -r -- "$o" | grep -q 'shI  reproduces .*shI' && { echo "FAIL: the old screen reports shI (control not reproduced)"; ok=1; }
for want in 'ExpBFS/Machine.lean::shI  reproduces  Codec/Machine.lean::shI: 69/69 = 100%' \
            'Codec/Machine.lean::shI  reproduces  ExpBFS/Machine.lean::shI: 69/69 = 100%' \
            'Codec/Machine.lean::cpA  reproduces  ExpBFS/Machine.lean::cpB: 85/85 = 100%'; do
  print -r -- "$n" | grep -qF -- "$want" || { echo "FAIL: the new screen lacks: $want"; ok=1; }
done
print -r -- "$n" | head -1 | grep -qF 'copy pairs (target reproduces >= half of source): 4;' || { echo "FAIL: new pair count is not 4"; ok=1; }
[ $ok -eq 0 ] && echo "PASS: the old screen drops the same-basename pair, the new screen reports it"
exit $ok
