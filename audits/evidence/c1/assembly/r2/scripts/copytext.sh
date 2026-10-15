#!/usr/bin/env bash
# Copy-text screens of round 2 (the campaign's audits/evidence/retrofit/copy-text-screen.py at the tip),
# one at a time, under nice -n 10. Populations: the three landing files and the modules whose
# declarations their new code cites (P1), and P1 plus Build/Catalog (P2). Roots: the tip (before),
# the tip with round 1's landed NDHost (r1), the tip with round 2's three landed files (after).
# Usage: bash copytext.sh <S>; writes <OUT>/logs/copytext-*.txt and prints the new pairs.
set -o pipefail
S="$1"; O="$S/gate-c1asm/r2"; BASE="$O/base"; SC="$BASE/audits/evidence/retrofit/copy-text-screen.py"
P="TCSlib/Complexity/TuringMachine"
P1="$P/Build/NDHost.lean $P/Build/Embed.lean TCSlib/Complexity/SpaceComplexity/Inclusions.lean $P/Build/Seam.lean $P/Nondeterministic.lean $P/StateRenaming.lean $P/ChoiceReplay.lean $P/NDCodeSimulator.lean $P/Simulation.lean"
P2="$P1 $P/Build/Catalog.lean"
mkroot() { # name, then pairs of (repo path, source file)
  local d="$O/work/root_$1"; shift; rm -rf "$d"
  for f in $P2; do mkdir -p "$d/$(dirname "$f")"; cp "$BASE/$f" "$d/$f"; done
  while [ $# -gt 0 ]; do cp "$2" "$d/$1"; shift 2; done
}
mkroot before
mkroot r1 "$P/Build/NDHost.lean" "$S/gate-c1asm/landed/$P/Build/NDHost.lean"
mkroot after "$P/Build/NDHost.lean" "$O/landed/$P/Build/NDHost.lean" "$P/Build/Embed.lean" "$O/landed/$P/Build/Embed.lean" \
  "TCSlib/Complexity/SpaceComplexity/Inclusions.lean" "$O/landed/TCSlib/Complexity/SpaceComplexity/Inclusions.lean"
fail=0
exec 3>"$O/logs/copytext.log"
{ echo "# C1-A assembly gate, round 2: copy-text screens"; echo
  echo "Screen: the tip's \`audits/evidence/retrofit/copy-text-screen.py\`, run one at a time under \`nice -n 10\`."
  echo "P1 = $P1"; echo "P2 = P1 + $P/Build/Catalog.lean"
  echo "Roots: before = the tip; r1 = the tip with round 1's landed NDHost; after = the tip with round 2's"
  echo "three landed files. Raw outputs: <OUT>/logs/copytext-<pop>-<root>.txt."; echo; } >&3
for pop in P1 P2; do
  for r in before r1 after; do
    nice -n 10 python3 -I "$SC" "$O/work/root_$r" ${!pop} > "$O/logs/copytext-$pop-$r.txt" 2>&1 || fail=1
  done
done
{ for pop in P1 P2; do
  echo "## $pop"; echo; echo "before: $(head -1 "$O/logs/copytext-$pop-before.txt")"
  for r in r1 after; do
    echo "$r: $(head -1 "$O/logs/copytext-$pop-$r.txt")"
    echo "pairs in $r and not before:"; echo '```'
    comm -13 <(grep '  reproduces  ' "$O/logs/copytext-$pop-before.txt" | sort) <(grep '  reproduces  ' "$O/logs/copytext-$pop-$r.txt" | sort)
    echo '```'
  done
  echo "pairs before and not after:"; echo '```'
  comm -23 <(grep '  reproduces  ' "$O/logs/copytext-$pop-before.txt" | sort) <(grep '  reproduces  ' "$O/logs/copytext-$pop-after.txt" | sort)
  echo '```'; echo
done
echo "copy-text screens exit status: $fail"; } >&3
cat "$O/logs/copytext.log"
exit $fail
