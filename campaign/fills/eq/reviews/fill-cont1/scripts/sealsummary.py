"""Summarize a seal run: errors in the module body versus per control line (python3 -I).
usage: python3 -I sealsummary.py <probe .lean> <elab .out> <body first line> <body last line>"""
import re, sys
src, out, a, b = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
L = open(src, encoding='utf-8').read().split('\n')
T = open(out, encoding='utf-8').read()
errs = [(int(m.group(1)), m.group(2)) for m in re.finditer(r'^\S+?:(\d+):\d+: error: (.*)$', T, re.M)]
body = [e for e in errs if a <= e[0] <= b]
other = [e for e in errs if not (a <= e[0] <= b)]
ctl_lines = [i + 1 for i, l in enumerate(L) if l.startswith('#rfl_control') or l.startswith('#simp_control')]
ex = [i + 1 for i, l in enumerate(L) if l.startswith('example') and i + 1 > b]
by_line = {}
for ln, msg in other: by_line.setdefault(ln, []).append(msg[:70])
print(f'errors: {len(errs)}; in the module body (lines {a}-{b}): {len(body)}')
for e in body: print('   BODY', e)
print(f'controls: {len(ctl_lines)} commands + {len(ex)} usage examples')
items = sorted(ctl_lines + ex)
for k, ln in enumerate(items):
    hi = items[k + 1] - 1 if k + 1 < len(items) else len(L)
    if ln in ctl_lines: hi = ln
    n = sum(len(m) for l2, m in by_line.items() if ln <= l2 <= hi)
    print(f'   line {ln}: {L[ln-1][:60]:60s} -> {"FAILS (" + str(n) + " error(s))" if n else "closes"}')
passes = re.findall(r'(RFL|SIMP)_CONTROL_PASS (\S+)', T)
print('PASS messages:', len(passes))
print('errors outside the body and the control lines:', [(l, m) for l, m in by_line.items() if l not in ctl_lines and not any(e <= l <= e + 2 for e in ex)])
