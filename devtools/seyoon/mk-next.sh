#!/usr/bin/env bash
# Merge the campaign into a PR branch and write its merged-tree replay, chained from a snapshot.
# Paths: $TCSLIB_SCRATCH holds the worktrees (<worktree dir> is relative to it), the snapshots and
# fills/replay/ (scripts, closures, logs).
# Usage: mk-next.sh <name> <worktree dir> <branch> <snapshot-tree commit> <prev snap> <prev log>
#                   <new snap> "<base label>" "<label>" <expected changed .lean count>
# <snapshot-tree commit>: a commit whose Lean tree is exactly <prev snap>'s; the campaign tip's
# Lean must equal it. Stops before any push if a check fails.
set -euo pipefail
S="${TCSLIB_SCRATCH:-$HOME/.tcslib-scratch}"
R="${TCSLIB_REPO:-$HOME/tcslib}"
T="$(cd "$(dirname "$0")" && pwd)"   # this folder, devtools/seyoon
mkdir -p "$S/fills/replay"
NAME=$1; W=$S/$2; BR=$3; SNAPC=$4; PREV=$5; PREVLOG=$6; NEW=$7; BLABEL=$8; LABEL=$9; NF=${10}
cd "$W"
git fetch -q origin
BASE=$(git rev-parse origin/complexity/arora-barak-ch3-4)
git cat-file -e "$SNAPC^{commit}" 2>/dev/null || { echo "the snapshot-tree commit $SNAPC does not exist" >&2; exit 2; }
[ -z "$(git diff --name-only $SNAPC $BASE -- '*.lean')" ] || { echo "the campaign's Lean differs from $SNAPC: $PREV is not its snapshot" >&2; exit 2; }
[ "$(git rev-parse HEAD)" = "$(git rev-parse origin/$BR)" ] || { echo "$W is not at origin/$BR" >&2; exit 2; }
[ -z "$(git status --porcelain --untracked-files=no)" ] || { echo "$W has local changes" >&2; exit 2; }
if ! git merge-base --is-ancestor $BASE HEAD; then
  git merge -q -m "Merge remote-tracking branch 'origin/complexity/arora-barak-ch3-4' into $BR

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>" origin/complexity/arora-barak-ch3-4
fi
FILES=(); while read -r f; do FILES+=("$f"); done < <(git diff --name-only $BASE HEAD -- '*.lean')
[ "${#FILES[@]}" = "$NF" ] || { echo "expected $NF changed files, got: ${FILES[*]}" >&2; exit 2; }
git push -q origin HEAD:$BR
MODS=(); PINS=""
for f in "${FILES[@]}"; do m=${f%.lean}; MODS+=("${m//\//.}"); PINS="$PINS$f:$(git rev-parse HEAD:$f);"; done
echo "changed: ${FILES[*]}; head $(git rev-parse HEAD)"
python3 -I $T/mkdownmulti.py $W $T $S/fills/replay/down-$NAME.txt "${MODS[@]}"
TCSLIB_SCRATCH=$S python3 -I $T/mkreplay.py $S/fills/replay/replay-$NAME.sh $NAME $2 $BR $BASE "$BLABEL" $S/fills/replay/down-$NAME.txt $PREVLOG $PREV $NEW "$LABEL" "${PINS%;}"
awk '/^cp -R/ {print "echo PRECHECK-PASSED; exit 0"; exit} {print}' $S/fills/replay/replay-$NAME.sh > $S/fills/replay/precheck-$NAME.sh
bash $S/fills/replay/precheck-$NAME.sh
