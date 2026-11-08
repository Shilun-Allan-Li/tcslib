#!/usr/bin/env bash
# Replay mf62 (F6 canonical seam citation: current downstream replay; branch codex/f6-space-universal, stacked on complete MF61/f72 snapshot): its downstream closure (2 modules),
# fresh .oleans into oleans-mf62, a copy of oleans-mf61, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch
WT="$S/wt-f6"
LIST="/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/order-mf62.txt"
LOG="$S/fills/replay/replay-mf62.log"
PINS="TCSlib/Complexity/SpaceComplexity/Hierarchy.lean:b9a7162841b98bdab13be5c03ae48e1954fa16c9"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/codex/f6-space-universal 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor f72a807e2376a2b986675c992745d6affc23b96f HEAD || { echo "precheck: the head must contain complete MF61/f72 snapshot; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only f72a807e2376a2b986675c992745d6affc23b96f HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from complete MF61/f72 snapshot must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/replay-mf61.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "2" ] || { echo "precheck: the replay list must have 2 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-mf62" ] && { echo "precheck: $S/oleans-mf62 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-mf61" ] || { echo "precheck: oleans-mf61 is missing; nothing copied" >&2; exit 2; }
echo PRECHECK-PASSED
exit 0
