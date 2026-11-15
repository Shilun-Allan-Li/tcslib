#!/usr/bin/env python3
"""Line widths (Python len) and line counts of the changed and new files of the prf-long fill.
A line over 100 characters is a violation unless it is a line of the base file (frozen text: the
frozen-statement rule forbids changing it); those are listed as INHERITED.
usage: widths2.py REPO BASE_REV FILE..."""
import subprocess, sys
repo, rev, files = sys.argv[1], sys.argv[2], sys.argv[3:]
bad = 0
for f in files:
    p = subprocess.run(['git', '-C', repo, 'show', f'{rev}:{f}'], capture_output=True, text=True)
    base = set(p.stdout.split('\n')) if p.returncode == 0 else set()
    blines = len(p.stdout.split('\n')) - 1 if p.returncode == 0 else 0
    lines = open(f'{repo}/{f}', encoding='utf-8').read().split('\n')
    if lines and lines[-1] == '':
        lines = lines[:-1]
    new_over = [(i + 1, len(l)) for i, l in enumerate(lines) if len(l) > 100 and l not in base]
    inh = [(i + 1, len(l)) for i, l in enumerate(lines) if len(l) > 100 and l in base]
    print(f'{f}: {blines} -> {len(lines)} lines; max width {max(len(l) for l in lines)}; '
          f'{len(new_over)} new lines over 100; {len(inh)} inherited base lines over 100'
          + ('' if len(lines) <= 1000 else '; FILE OVER 1000 LINES'))
    for i, w in new_over:
        print(f'  OVER {f}:{i} width {w}')
    for i, w in inh:
        print(f'  INHERITED {f}:{i} width {w} (byte-identical base line)')
    bad += len(new_over) + (len(lines) > 1000)
print('RESULT', 'OK' if bad == 0 else f'{bad} violations')
