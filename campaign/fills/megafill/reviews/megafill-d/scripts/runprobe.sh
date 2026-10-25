#!/usr/bin/env bash
# runprobe.sh <record .lean.txt or .lean> [name]: copy the record into the review worktree's
# ReviewProbe/<name>.lean, elaborate it once through leanelab.sh against oleans-lrcan3, and write
# probe/<name>.out (header: source path, SHA-256 of the record and of the copy; then lean's output;
# then the exit status and the wall time).
set -u
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
R=$S/review/megafill-d; W=$R/wt; OL=$S/oleans-lrcan3
src="$1"; name="${2:-$(basename "$src" | sed -e 's/\.lean\.txt$//' -e 's/\.lean$//')}"
mkdir -p "$W/ReviewProbe"
dst="$W/ReviewProbe/$name.lean"
cp "$src" "$dst"
cmp -s "$src" "$dst" || { echo "copy mismatch" >&2; exit 3; }
out="$R/probe/$name.out"
{
  echo "# $name: source $src"
  echo "# record sha256 $(shasum -a 256 "$src" | cut -d' ' -f1); copy sha256 $(shasum -a 256 "$dst" | cut -d' ' -f1)"
  echo "# worktree HEAD $(git -C "$W" rev-parse HEAD); oleans $OL; start $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  t0=$(date +%s)
  bash "$S/tools/leanelab.sh" "$W" "$OL" "ReviewProbe/$name.lean"
  rc=$?
  echo "# exit=$rc secs=$(( $(date +%s) - t0 ))"
} > "$out" 2>&1
tail -1 "$out"
