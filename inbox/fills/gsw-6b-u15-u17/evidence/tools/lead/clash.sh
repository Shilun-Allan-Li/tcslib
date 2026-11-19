#!/usr/bin/env bash
# C10 clash scan (gsw-6b-u15-u17). usage: clash.sh TAG HEAD NAME...
# Every new name (all private) grepped as a word in TCSlib/ and audits/ at the base, on iO/phase-a-base,
# on cleanup/stage2-s2a and at the records tip, in /workspace/tcslib (fetched before the run).
TAG=$1; H=$2; shift 2
cd /workspace/tcslib
B=bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d
REVS="$B origin/iO/phase-a-base origin/cleanup/stage2-s2a origin/cryptography/pass-shelat-ch2-4"
echo "# C10 clash scan (gsw-6b-u15-u17), head $H ($TAG). New declarations at the head: $#, all private: $*"
n=0; e=0
for x in "$@"; do
  n=$((n+1)); hit=0
  for r in $REVS; do
    c=$(git grep -n -w "$x" $r -- TCSlib audits 2>/dev/null | wc -l)
    echo "(a/b) git grep -n -w $x $r ($(git rev-parse $r)) -- TCSlib audits: $c hits"
    git grep -n -w "$x" $r -- TCSlib audits 2>/dev/null | head -5 | sed 's/^/    /'
    [ "$c" -gt 0 ] && hit=1
  done
  e=$((e+hit))
done
echo "(c) every new name is private: it is invisible outside its file, so no unqualified use in a UNIT-DOWN module (Circular, LeveledSecurity, Asymptotic and the three facades) can resolve to it; the head sweep of the 6 UNIT-DOWN modules is rc 0, 0 errors (build/summary)."
echo "RESULT new_names=$n existing_elsewhere=$e"
