#!/usr/bin/env bash
# Grep every ref tip's .lean files for the new names (word match) and for any dz/Dz identifier.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad; R=$S/review/ed-fill; G=/Users/seyoonr/phd_experiments/tcslib
H=$(git -C $G rev-parse refs/deliv/eq-diagonalizer)
# search patterns: each new name's last component, word-matched (dotted names checked by their full form too)
# a dotted new name lives in a new namespace (DzKit.*), so its first component is what can collide
awk -F. '{print $1}' $R/out/18-newnames.txt | sort -u > $R/out/18-patterns.txt
git -C $G for-each-ref --format='%(objectname) %(refname)' | sort -u -k1,1 > $R/out/18-refs.txt
n=0; : > $R/out/18-hits-raw.txt
while read sha ref; do
  [ "$sha" = "$H" ] && continue
  git -C $G grep -I -n -w -F -f $R/out/18-patterns.txt $sha -- '*.lean' >> $R/out/18-hits-raw.txt 2>/dev/null
  n=$((n+1))
done < $R/out/18-refs.txt
echo "ref tips searched (excluding the delivery head): $n" > $R/out/18-rule11.txt
echo "hits: $(wc -l < $R/out/18-hits-raw.txt)" >> $R/out/18-rule11.txt
cut -d: -f2 $R/out/18-hits-raw.txt | sort | uniq -c >> $R/out/18-rule11.txt
# control: the delivery head itself must hit the owned file
echo "control (delivery head):" >> $R/out/18-rule11.txt
git -C $G grep -I -c -w -F -f $R/out/18-patterns.txt $H -- '*.lean' >> $R/out/18-rule11.txt
# any dz/Dz-prefixed identifier anywhere on other refs
echo "dz/Dz-prefixed identifiers on other ref tips (regex \\b[dD]z[A-Z_][A-Za-z_]*):" >> $R/out/18-rule11.txt
: > $R/out/18-dzprefix-raw.txt
while read sha ref; do
  [ "$sha" = "$H" ] && continue
  git -C $G grep -I -n -E '(^|[^A-Za-z0-9_.])[dD]z[A-Z_][A-Za-z0-9_]*' $sha -- '*.lean' >> $R/out/18-dzprefix-raw.txt 2>/dev/null
done < $R/out/18-refs.txt
echo "lines: $(wc -l < $R/out/18-dzprefix-raw.txt)" >> $R/out/18-rule11.txt
cut -d: -f2 $R/out/18-dzprefix-raw.txt | sort | uniq -c | head -20 >> $R/out/18-rule11.txt
