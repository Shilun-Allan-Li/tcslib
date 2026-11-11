#!/usr/bin/env bash
# sweep.sh <order-file> <logdir> <tsv> : check modules one at a time in order; stop on first failure
ORDER=$(realpath "$1"); LD=$(realpath -m "$2"); TSV=$(realpath -m "$3"); mkdir -p "$LD"; : > "$TSV"
while read -r m; do
  [ -z "$m" ] && continue
  lf="$LD/$(echo "$m" | tr '/' '.').log"
  /home/user/tools/chk "$m" "$lf" > /dev/null 2>&1; st=$?
  el=$(awk '/^Elapsed seconds/{print $3}' "$lf"); rss=$(awk '/^Maximum child RSS/{print $5}' "$lf")
  ns=$(grep -c "declaration uses 'sorry'" "$lf")
  printf '%s\t%s\t%s\t%s\t%s\n' "$m" "$st" "$el" "$rss" "$ns" >> "$TSV"
  if [ $st -ne 0 ]; then echo "FAIL $m"; exit 1; fi
done < "$ORDER"
echo "ALL PASS $(wc -l < "$TSV")"
