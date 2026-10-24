#!/usr/bin/env bash
# One v3 screen run of the drafted 20-file population on the review worktree, under the
# machine-wide screen lock (released on any exit).
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
R=$S/review/megafill-c-u2
P=$S/wt-hk/campaign/fills/u2s/drafts/u2s-fill-universal/preship-77f1eb4f
FILES=()
while IFS= read -r l; do FILES+=("$l"); done < <(grep -v '^#' "$P/screen-population.txt")
[ "${#FILES[@]}" -eq 20 ] || { echo "expected 20 files, got ${#FILES[@]}"; exit 2; }
echo "waiting $(date -u +%FT%TZ)" > "$R/out/14-screen.status"
until mkdir "$S/locks/screen.lock" 2>/dev/null; do sleep 15; done
trap 'rmdir "$S/locks/screen.lock"' EXIT
echo "start $(date -u +%FT%TZ)" >> "$R/out/14-screen.status"
cd "$R/wt" || exit 1
nice -n 10 python3 -I scripts/copy-text-screen-v3.py . "${FILES[@]}" > "$R/out/14-screen.txt" 2> "$R/out/14-screen.stderr"
rc=$?
echo "exit $rc end $(date -u +%FT%TZ)" >> "$R/out/14-screen.status"
exit $rc
