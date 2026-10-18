#!/usr/bin/env bash
# The overnight screens, one at a time, at #118's round-2 head (wt-bapi, 4624fc05), after any running
# screen: the F3 and cont6 screen bases re-measured (their populations contain round-2 files),
# then MIG-24's library-wide screens of TuringMachine/ and SpaceComplexity/.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
N=$S/mig24
busy() { pgrep -f 'Python -I audits/evidence/retrofit/[c]opy-text-screen-v3' >/dev/null; }
run() {  # name, population file, output
  while busy; do sleep 30; done
  echo "$(date +%H:%M) start $1" >> "$N/overnight.log"
  nice -n 10 python3 -I audits/evidence/retrofit/copy-text-screen-v3.py . $(grep -v '^#' "$2") > "$3" 2>&1
  echo "$(date +%H:%M) $1: $(sed -n 1p "$3")" >> "$N/overnight.log"
}
cd "$S/wt-bapi" || exit 1
run f3-r2 "$S/issue5/f3-pop.txt" "$S/issue5/f3-screen-base-r2.txt"
run c6-r2 "$S/issue5/c6-pop.txt" "$S/issue5/c6-screen-base-r2.txt"
for b in tm sc; do
  run "mig24-$b" "$N/pop-$b.txt" "$N/screen-$b.txt"
  python3 -I - "$N/screen-$b.txt" "$N/pairs90-$b.txt" <<'PY'
import sys, re
rows = [l.rstrip('\n') for l in open(sys.argv[1], encoding='utf-8') if (m := re.search(r'= (\d+)%$', l.rstrip())) and int(m.group(1)) >= 90]
open(sys.argv[2], 'w', encoding='utf-8').write('\n'.join(rows) + '\n')
PY
  echo "$(date +%H:%M) mig24-$b pairs at 90% or more: $(grep -c . "$N/pairs90-$b.txt")" >> "$N/overnight.log"
done
cat "$N/overnight.log"
