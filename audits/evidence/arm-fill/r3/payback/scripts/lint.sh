#!/usr/bin/env bash
# The base's style lint (scripts/campaign_style_lint.py, copied unchanged) over TCSlib/Complexity,
# once on a copy of the base export and once on the same copy with the landed files overlaid.
# Usage: bash lint.sh <base export> <L>. Writes <L>/work/lint/{base,land}.out.
set -eo pipefail
B="$1"; L="$2"; LW="$L/work/lint"
rm -rf "$LW"; mkdir -p "$LW"
for r in base land; do
  mkdir -p "$LW/$r/scripts" "$LW/$r/TCSlib"
  cp "$B/scripts/campaign_style_lint.py" "$LW/$r/scripts/"
  cp -R "$B/TCSlib/Complexity" "$LW/$r/TCSlib/"
  cp "$B/TCSlib/Complexity.lean" "$LW/$r/TCSlib/" 2>/dev/null || true
  chmod -R u+w "$LW/$r"
done
(cd "$L/tree" && find TCSlib -name '*.lean' -type f) | while read -r f; do
  case "$f" in TCSlib/Complexity/*) cp "$L/tree/$f" "$LW/land/$f";; esac
done
cmp -s "$B/scripts/campaign_style_lint.py" "$LW/land/scripts/campaign_style_lint.py"
for r in base land; do
  (cd "$LW/$r" && python3 -I -B scripts/campaign_style_lint.py TCSlib/Complexity > "$LW/$r.out") || true
done
echo "lint: $(tail -1 "$LW/base.out") (base); $(tail -1 "$LW/land.out") (landing)"
