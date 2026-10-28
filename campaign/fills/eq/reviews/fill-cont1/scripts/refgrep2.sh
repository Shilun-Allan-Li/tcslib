#!/bin/bash
# git grep over every ref of the main repository (unique commits), .lean files only, for a pattern;
# prints hits outside the owned file, and the number of refs/commits searched.
G=/Users/seyoonr/phd_experiments/tcslib; PAT="$1"
F=TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.lean
C=$(git -C $G for-each-ref --format='%(objectname)' | sort -u)
echo "refs: $(git -C $G for-each-ref | wc -l); distinct commits: $(echo "$C" | wc -l); pattern: $PAT"
git -C $G grep -I -n -E "$PAT" $C -- '*.lean' 2>/dev/null | grep -v ":$F:" | sed -E 's/^([0-9a-f]{12})[0-9a-f]*:/\1:/' | sort -u > /tmp/.rg$$ ; n=$(wc -l < /tmp/.rg$$)
echo "hits outside the owned file: $n"; head -40 /tmp/.rg$$; rm -f /tmp/.rg$$
