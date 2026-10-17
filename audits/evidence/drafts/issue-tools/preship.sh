#!/usr/bin/env bash
# The six briefs' pre-ship elaborations against oleans-lbapi3 (#118's round-2 replay), in wt-bapi
# at 4624fc05, one at a time. Each file is copied in as TCSlib/<name>.lean and removed after.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
cd "$S/wt-bapi" || exit 1
while IFS=$'\t' read -r b n src; do
  mkdir -p "$S/issue/preship/$b"
  if [ "$n" = "CodeSimulator" ]; then f=TCSlib/Complexity/TuringMachine/CodeSimulator.lean; else f=TCSlib/$n.lean; cp "$src" "$f"; fi
  bash "$S/tools/leanelab.sh" "$S/wt-bapi" "$S/oleans-lbapi3" "$f" > "$S/issue/preship/$b/$n.out" 2>&1; st=$?
  [ "$n" = "CodeSimulator" ] || rm -f "$f"
  echo "$b $n exit=$st errors=$(grep -c ': error' "$S/issue/preship/$b/$n.out") warnings=$(grep -c ': warning' "$S/issue/preship/$b/$n.out") sorry=$(grep -c "uses 'sorry'" "$S/issue/preship/$b/$n.out")"
done < "$S/issue/preship.tsv"
git status --short | head -3
