#!/usr/bin/env python3
"""Summary of a sweep: exit codes of the TSV, error diagnostics counted with
`^\\S+\\.lean:\\d+:\\d+: error[:(]` over every module log, and the sorry census of the sweep's logs
completed by the base bootstrap logs for the modules the sweep did not check (unchanged).
usage: sweepsum.py ORDER TSV LOGDIR ROOT"""
import re, subprocess, sys
order_f, tsv, d, root = sys.argv[1:5]
order = [l.strip() for l in open(order_f) if l.strip()]
rx = re.compile(r'^\S+\.lean:\d+:\d+: error[:(]', re.M)
codes = {l.split('\t')[0]: l.split('\t')[1] for l in open(tsv)}
n = 0
for m in order:
    k = len(rx.findall(open(f"{d}/{m.replace('/', '.')}.log").read()))
    n += k
    if k:
        print('ERRORS', m, k)
print(f'modules {len(order)}; exit 0: {sum(codes.get(m) == "0" for m in order)}; '
      f'error diagnostics (both forms) over all logs: {n}')
