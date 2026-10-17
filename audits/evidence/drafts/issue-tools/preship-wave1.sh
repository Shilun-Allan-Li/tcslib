#!/usr/bin/env bash
# C1 wave 1's pre-ship elaborations against oleans-lndnf (#120's replay, which contains #119), in
# wt-ndnf at #120's head, one at a time. A source file is copied in as TCSlib/<name>.lean and removed
# after; "OwnedFile" rows elaborate the in-tree module at its path.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
[ -d "$S/oleans-lndnf" ] || { echo "precheck: oleans-lndnf missing (run #119's and #120's replays first)" >&2; exit 2; }
cd "$S/wt-ndnf" || exit 1
[ -z "$(git status --porcelain --untracked-files=no)" ] || { echo "precheck: wt-ndnf has local changes" >&2; exit 2; }
while IFS=$'\t' read -r b n src; do
  mkdir -p "$S/issue2/preship/$b"
  if [ "$n" = "OwnedFile" ]; then f="$src"; else f=TCSlib/$n.lean; [ -e "$f" ] && { echo "exists: $f" >&2; exit 2; }; cp "$src" "$f"; fi
  bash "$S/tools/leanelab.sh" "$S/wt-ndnf" "$S/oleans-lndnf" "$f" > "$S/issue2/preship/$b/$n.out" 2>&1; st=$?
  [ "$n" = "OwnedFile" ] || rm -f "$f"
  echo "$b $n exit=$st errors=$(grep -c ': error' "$S/issue2/preship/$b/$n.out") warnings=$(grep -c ': warning' "$S/issue2/preship/$b/$n.out") sorry=$(grep -c "uses 'sorry'" "$S/issue2/preship/$b/$n.out")"
done < "$S/issue2/preship.tsv"
git status --short | head -3
