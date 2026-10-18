"""Write a 2-module chained replay script (maintainer tool).
Usage: mkreplay.py <out.sh> <name> <worktree> <branch> <base-full> <base-label> <list> <prev-log> <prev-snap> <new-snap> <label> <pins (path:blob;...)>"""
import os, sys
out, name, wt, br, base, blabel, lst, prevlog, prevsnap, newsnap, label, pins = sys.argv[1:13]
pins = pins.replace(';', '\n')
n = len([l for l in open(lst) if l.strip()])
S = os.environ.get('TCSLIB_SCRATCH', os.path.expanduser('~/.tcslib-scratch'))
s = f'''#!/usr/bin/env bash
# Replay {name} ({label}; branch {br}, stacked on {blabel}): its downstream closure ({n} modules),
# fresh .oleans into {newsnap}, a copy of {prevsnap}, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S={S}
WT="$S/{wt}"
LIST="{lst}"
LOG="$S/fills/replay/replay-{name}.log"
PINS="{pins}"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || {{ echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }}
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/{br} 2>/dev/null)" ] || {{ echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }}
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || {{ echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }}
git -C "$WT" merge-base --is-ancestor {base} HEAD || {{ echo "precheck: the head must contain {blabel}; nothing copied" >&2; exit 2; }}
[ "$(git -C "$WT" diff --name-only {base} HEAD -- '*.lean' | sort)" = "$(printf '%s\\n' "$PINS" | cut -d: -f1 | sort)" ] || {{ echo "precheck: the Lean diff from {blabel} must be exactly the pinned files; nothing copied" >&2; exit 2; }}
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || {{ echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }}
done <<< "$PINS"
tail -1 "{prevlog}" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || {{ echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }}
[ "$(wc -l < "$LIST" | tr -d ' ')" = "{n}" ] || {{ echo "precheck: the replay list must have {n} modules; nothing copied" >&2; exit 2; }}
grep -qx "TCSlib" "$LIST" && {{ echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }}
[ -d "$S/{newsnap}" ] && {{ echo "precheck: $S/{newsnap} already exists; remove it for a fresh copy" >&2; exit 2; }}
[ -d "$S/{prevsnap}" ] || {{ echo "precheck: {prevsnap} is missing; nothing copied" >&2; exit 2; }}
cp -R "$S/{prevsnap}" "$S/{newsnap}" || exit 1
cd "$WT" || exit 1
{{ echo "# replay-{name} at $(git rev-parse --short HEAD): {label} ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into {newsnap}"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/{newsnap} nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && {{ f=$((f+1)); printf '%s\\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }}
  done < "$LIST"
  echo "# modules=$n failed=$f"
}} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${{LOG%.log}}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${{LOG%.log}}-static.txt"
'''
open(out, 'w').write(s); print('written', out, n)
