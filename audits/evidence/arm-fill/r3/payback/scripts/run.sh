#!/usr/bin/env bash
# Dedup payback PR: build the landing tree and re-run every check (read-only on the repository).
# Usage: bash run.sh <S> <olean snapshot> <packages worktree> [<base revision>]
#   The base: <base revision> (resolved with `git rev-parse --verify`), by default the campaign tip
#   (origin/complexity/arora-barak-ch3-4), exported read-only to <L>/work/base by `git archive`.
#   The final run: the tip (no fourth argument), the snapshot <S>/oleans-ltip3 (the catch-up
#   replay of the merged tip c9cc485b, #95-#97) and the packages of <S>/wt-mig1s. The base must
#   be an ancestor of the tip, with the snapshot base's Lean files, and the tip must not have
#   changed a touched file since (precheck.py, graph.py, verify.py).
# Lean only through <S>/tools/leanelab.sh (no -o, no olean written), at most 2 at a time, niced;
# Python only as python3 -I -B; git read-only (rev-parse, archive, cat-file, ls-tree, status).
# Fails closed: the source precheck exits 2 before anything is written; a failed step or a failed
# check of verify.py exits non-zero.
set -eo pipefail
S="${1:?scratchpad}"; OL="${2:?olean snapshot}"; WT="${3:?packages worktree}"
L="$S/land-payback"; SC="$L/scripts"; W="$L/work"; LG="$L/logs"; B="$W/base"
REPO=/Users/seyoonr/phd_experiments/tcslib
TIP=$(git -C "$REPO" rev-parse --verify "${4:-origin/complexity/arora-barak-ch3-4}^{commit}")
# the read-only export of the tip (re-made only if it is missing or at another commit)
if [ ! -d "$B/TCSlib" ] || [ "$(cat "$W/base-commit.txt" 2>/dev/null)" != "$TIP" ]; then
  if [ -d "$B" ]; then chmod -R u+w "$B"; rm -rf "$B"; fi
  mkdir -p "$B"; git -C "$REPO" archive --format=tar "$TIP" | tar -x -C "$B"; chmod -R a-w "$B"
  echo "$TIP" > "$W/base-commit.txt"
fi
echo "$TIP" > "$W/tip-at-start.txt"
# 0. the source precheck, before any output is created
python3 -I -B "$SC/precheck.py" "$S" "$B" "$OL" "$WT" "$L"
mkdir -p "$LG"
san() { sed "s|$L|<L>|g; s|$S|<S>|g"; }
git -C "$REPO" status --porcelain > "$W/repo-status-before.txt"
# 1. the landing: tree, patches
python3 -I -B "$SC/land.py" "$S" "$B" "$OL" "$WT" "$L" | san > "$LG/land.out"
# 2. cut files and probes
rm -rf "${W:?}/cut" "${W:?}/probes"
python3 -I -B "$SC/cuts.py" "$L/tree" "$W/cut" | san > "$LG/cuts.log"
python3 -I -B "$SC/probes.py" "$L" | san > "$LG/probes.log"
# 3. elaboration (read-only): every probe
rm -rf "${W:?}/out"
nice -n 10 bash "$SC/elab.sh" "$S" "$WT" "$OL" "$W/out" 2 "$W"/probes/*.lean
# 4. freeze, API delta, controls, names
python3 -I -B "$SC/freeze.py" "$B" "$L/tree" --json "$W/api-delta.json" > "$W/freeze.out" 2>&1 || true
python3 -I -B "$SC/freezectl.py" "$B" "$L" "$WT" > "$W/controls.out" 2>&1 || true
nice -n 10 python3 -I -B "$SC/names.py" "$B" "$L" "$WT" > "$W/names.out" 2>&1 || true
# 5. graph and replay list; hygiene and cut identity; lint; ledger map
python3 -I -B "$SC/graph.py" "$B" "$L" --oleans "$OL" --packages "$WT" | san > "$LG/graph.log"
python3 -I -B "$SC/hygiene.py" "$B" "$L" > "$W/hygiene.out" 2>&1 || true
nice -n 10 bash "$SC/lint.sh" "$B" "$L" | san > "$W/lint.summary"
python3 -I -B "$SC/ledger.py" "$B" "$L" | san > "$LG/ledger.log"
for f in freeze controls names hygiene; do san < "$W/$f.out" > "$LG/$f.log"; done
# elaboration summary log
for f in "$W"/out/*.exit; do b=$(basename "$f" .exit)
  printf '%s exit %s secs %s errors %s warnings %s\n' "$b" "$(cat "$f")" "$(cat "$W/out/$b.secs")" \
    "$(grep -c ': error' "$W/out/$b.out" || true)" "$(grep -c ': warning' "$W/out/$b.out" || true)"
done > "$LG/elaboration.log"
# 6. negative control of the precheck: a mirror of the export without Codec/Word.lean
NC="$W/negctl"; rm -rf "$NC"; mkdir -p "$NC/base"
python3 -I -B - "$B" "$NC/base" <<'PY'
import os, sys
src, dst = sys.argv[1], sys.argv[2]
for dp, ds, fs in os.walk(src):
    rel = os.path.relpath(dp, src)
    os.makedirs(os.path.join(dst, rel), exist_ok=True)
    for f in fs:
        r = os.path.normpath(os.path.join(rel, f))
        if r == "TCSlib/Complexity/SpaceComplexity/Codec/Word.lean":
            continue
        os.symlink(os.path.join(dp, f), os.path.join(dst, r))
PY
find "$L" -path "$NC" -prune -o -type f -print0 | LC_ALL=C sort -z | xargs -0 stat -f '%N %m %z' > "$NC/before.txt"
set +e
python3 -I -B "$SC/precheck.py" "$S" "$NC/base" "$OL" "$WT" "$L" > "$NC/precheck.out" 2>&1; echo $? > "$NC/precheck.exit"
python3 -I -B "$SC/land.py" "$S" "$NC/base" "$OL" "$WT" "$L" --out work/negctl/out > "$NC/land.out" 2>&1; echo $? > "$NC/land.exit"
set -e
find "$L" -path "$NC" -prune -o -type f -print0 | LC_ALL=C sort -z | xargs -0 stat -f '%N %m %z' > "$NC/after.txt"
[ -e "$NC/out" ] && echo present > "$NC/out-exists.txt" || echo absent > "$NC/out-exists.txt"
cmp -s "$NC/before.txt" "$NC/after.txt" && echo unchanged > "$NC/files.txt" || echo CHANGED > "$NC/files.txt"
git -C "$REPO" status --porcelain > "$W/repo-status-after.txt"
# 7. the verdict
if python3 -I -B "$SC/verify.py" "$S" "$L" "$B" "$OL" "$WT" > "$W/verify.out" 2>&1; then VR=0; else VR=$?; fi
san < "$W/verify.out" > "$LG/verify.log"
bash "$SC/sums.sh" "$L"
[ "$VR" = 0 ] || { echo "verify.py: FAIL (see logs/verify.log)"; exit 1; }
echo "verify.py: PASS ($(tail -2 "$LG/verify.log" | head -1))"
