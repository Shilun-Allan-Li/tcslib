#!/usr/bin/env bash
# Replay mepad1 (E-PAD #228; branch lean/epad-padding-fill, stacked on complete Mac campaign bootstrap): its downstream closure (2 modules),
# fresh .oleans into oleans-mepad1, a copy of oleans-mac0, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch
WT="$S/wt-epad"
LIST="/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/down-mepad1.txt"
LOG="$S/fills/replay/replay-mepad1.log"
PINS="TCSlib/Complexity/SpaceComplexity/Padding.lean:d39aecb7d17552c94d254033d45698eac42708df"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/epad-padding-fill 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 680760723d72826469d0fc294e4d7ee2ecac3e6c HEAD || { echo "precheck: the head must contain complete Mac campaign bootstrap; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 680760723d72826469d0fc294e4d7ee2ecac3e6c HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from complete Mac campaign bootstrap must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/bootstrap-oleans-mac0.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "2" ] || { echo "precheck: the replay list must have 2 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-mepad1" ] && { echo "precheck: $S/oleans-mepad1 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-mac0" ] || { echo "precheck: oleans-mac0 is missing; nothing copied" >&2; exit 2; }
echo PRECHECK-PASSED; exit 0
