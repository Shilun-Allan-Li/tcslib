#!/usr/bin/env bash
# Every 40-hex word in the files #163 delivered (fe666d60..tip under campaign/), with git's type for it.
cd /Users/seyoonr/phd_experiments/tcslib || exit 1
R=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/review/megafill-d
TIP=5cade0b848a3bb6d87a2149aacecf4a2af923889; BASE=fe666d60f21e51438374e7c3f3a966eaa93862c0
git diff --name-only $BASE $TIP -- campaign/ > $R/probe/delivered-files.txt
while read -r f; do
  git show "$TIP:$f" | grep -oE '\b[0-9a-f]{40}\b|\b[0-9a-f]{64}\b' | sort -u | while read -r h; do echo "$f $h"; done
done < $R/probe/delivered-files.txt > $R/probe/fullhashes.txt
awk '{print $2}' $R/probe/fullhashes.txt | sort -u | while read -r h; do
  if [ ${#h} -eq 40 ]; then t=$(git cat-file -t "$h" 2>&1 | head -1); else t="sha256"; fi
  n=$(grep -c " $h\$" $R/probe/fullhashes.txt)
  echo "$h $t (in $n files)"
done > $R/probe/fullhashes-types.txt
wc -l < $R/probe/delivered-files.txt
cat $R/probe/fullhashes-types.txt
