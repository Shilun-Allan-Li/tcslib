#!/usr/bin/env bash
# The copy-text screens of the §13d G2–G4 gate, before and after, one at a time and niced
# (maintainer's CPU rule, 2026-10-14). Read-only; python3 -I only.
# Usage: bash screens.sh <S>   (run after runall.sh, which writes the landed forms)
S="$1"; O="$S/gate-g24"; WT="$O/base"; SC="$O/scripts"; B=TCSlib/Complexity/TuringMachine/Build
hdr() {
  echo "# §13d G2–G4 statement gate: copy-text screen, $1"
  echo
  echo "\`nice -n 10 python3 -I <OUT>/scripts/copy-text-screen.py <root> <files>\` (the retrofit screen,"
  echo "verbatim: like-kind pairs in which one declaration reproduces at least half of another's body,"
  echo "at least 60 characters, greedy tiling with blocks of at least 25). Declarations are labelled by"
  echo "file **basename**: \`Catalog.lean\` covers both \`Build/Catalog.lean\` and"
  echo "\`Build/Contract/Catalog.lean\`. Root: $2. Files: $3. Run: $(date -u '+%Y-%m-%d %H:%M UTC')."
  echo
}
{ hdr "before (the base, git archive of $(git -C "$S/wt-g24" rev-parse --short f2d48ad5))" "<OUT>/base" \
    "$B/Zone.lean $B/Catalog.lean $B/Contract/Catalog.lean"
  nice -n 10 python3 -I "$SC/copy-text-screen.py" "$WT" $B/Zone.lean $B/Catalog.lean \
    $B/Contract/Catalog.lean
} > "$O/screen-before.txt"
{ hdr "after (the landed forms)" "<OUT>/landed" \
    "$B/Zone.lean $B/ZoneTape.lean $B/ZoneRebalance.lean $B/Catalog.lean $B/Contract/Catalog.lean"
  nice -n 10 python3 -I "$SC/copy-text-screen.py" "$O/landed" $B/Zone.lean $B/ZoneTape.lean \
    $B/ZoneRebalance.lean $B/Catalog.lean $B/Contract/Catalog.lean
} > "$O/screen-after.txt"
d1=$(python3 -I "$S/tools/screendelta.py" "$O/screen-before.txt" "$O/screen-after.txt")
d2=$(python3 -I "$S/tools/pairdiff.py" "$O/screen-after.txt" "$O/screen-before.txt" | grep -E '^head pairs|GONE')
{ echo
  echo "## Delta against the before screen (\`<S>/tools/screendelta.py\`, \`pairdiff.py\`, verbatim)"
  echo '```'; echo "$d1"; echo "$d2"; echo '```'
} >> "$O/screen-after.txt"
echo "wrote $O/screen-before.txt and $O/screen-after.txt"
