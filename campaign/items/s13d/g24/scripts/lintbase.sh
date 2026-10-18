#!/usr/bin/env bash
# Baseline of the campaign lint's facade rule on the base tree (read-only; python3 -I only).
# Usage: bash lintbase.sh <S>
S="$1"; O="$S/gate-g24"
{ echo "# §13d G2–G4 statement gate: campaign-lint baseline on the base tree"
  echo
  echo "\`scripts/campaign_style_lint.py\` (as <OUT>/scripts/lint.py) over \`TCSlib/Complexity\` of <OUT>/base"
  echo "(the tip's tree, before this gate). Its FAIL lines naming the \`TuringMachine\` facade:"
  echo '```'
  (cd "$O/base" && python3 -I "$O/scripts/lint.py" TCSlib/Complexity "$O/base" 2>&1) |
    grep -E 'FAIL.*TCSlib/Complexity/TuringMachine\.lean|style_lint:' | sed "s|$O/|<OUT>/|g" | sed -E 's/  +/ /g'
  echo '```'
  echo "The rule looks for an intermediate facade at \`<dir>/<dir>.lean\` (\`check_facade\`: \`child.parent /"
  echo "(child.parent.name + \".lean\")\`), so every child of \`Build/Contract/\` already fails it at the base; the one"
  echo "FAIL in elaboration.log §5 (\`Build.Contract.Catalog\`) is one of these, not new."
} > "$O/lint-baseline.log"
echo "wrote $O/lint-baseline.log"
