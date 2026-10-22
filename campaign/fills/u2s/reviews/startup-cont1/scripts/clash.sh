#!/usr/bin/env bash
S=$S
R=<repo>
for ref in b7447492 7cd01f84 origin/lean/exhaustive-sketches; do
  git -C $R rev-parse -q --verify "$ref^{commit}" >/dev/null || { echo "## $ref: no such ref"; continue; }
  echo "## $ref: TCSlib files mentioning ss_RewindState / Ss_RewindState other than UniversalK:"
  r=$(git -C $R grep -l -E 'ss_RewindState|Ss_RewindState' "$ref" -- 'TCSlib/*.lean' | grep -v 'UniversalK.lean')
  echo "  ${r:-none}"
done
for d in $S/inbox-megaB/fill-b6-rulerdevice-cont1 $S/inbox-megaB/fill-s13d-g4-cont3-cp1; do
  r=$(grep -rl -E 'ss_RewindState|Ss_RewindState' "$d" --include=*.lean 2>/dev/null)
  echo "## $(basename $d): ${r:-none}"
done
