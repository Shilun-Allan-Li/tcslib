"""Parse the `first | exact? | sorry` probe's output into one verdict per probed declaration.
A failed `exact?` leaves a positioned `declaration uses 'sorry'` warning at the declaration's
line; a closed one prints a bare `Try this:` block (the CLI prints info messages without a
position), in source order. Usage: parse_exactq.py <map.tsv> <probe.out> <result.tsv>"""
import re
import sys
mp_path, out_path, res_path = sys.argv[1:4]
probes = []
for l in open(mp_path):
    ln, n = l.rstrip("\n").split("\t")
    probes.append((int(ln), n))
lines = open(out_path).read().split("\n")
sorry_lines = set()
events = []  # ('hdr', line) or ('try', text, last_hdr_line)
last = 0
i = 0
while i < len(lines):
    l = lines[i]
    m = re.match(r"^evidence/dup/QyExactProbe\.lean:(\d+):(\d+): (\w+)", l)
    if m:
        last = int(m.group(1))
        if "declaration uses 'sorry'" in l:
            sorry_lines.add(last)
        i += 1
        continue
    if l.startswith("Try this:"):
        block = [l]
        i += 1
        while i < len(lines) and lines[i].startswith("  "):
            block.append(lines[i].strip())
            i += 1
        events.append((" ".join(block), last))
        continue
    i += 1
closed = [(ln, n) for ln, n in probes if ln not in sorry_lines]
rows = {n: "could not close the goal (exact? failed; sorry fallback)" for ln, n in probes
        if ln in sorry_lines}
ok = len(closed) == len(events)
for (ln, n), (txt, hdr) in zip(closed, events):
    rows[n] = "CLOSED: " + txt
    if hdr > ln:
        ok = False
with open(res_path, "w") as f:
    for ln, n in probes:
        f.write(f"{n}\t{rows.get(n, 'UNMATCHED')}\n")
print(f"probes {len(probes)}; failed {len(sorry_lines & {ln for ln, _ in probes})}; "
      f"closed {len(closed)}; try-this blocks {len(events)}; consistent {ok}")
for ln, n in closed:
    print(n, "::", rows.get(n, "UNMATCHED")[:200])
