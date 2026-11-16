"""Line width (Python len, at most 100) and file length (at most 1000 lines) check (python3 -I).

usage: width.py FILE...
"""
import sys

bad = 0
for path in sys.argv[1:]:
    lines = open(path, encoding='utf-8').read().split('\n')
    if lines and lines[-1] == '':
        lines.pop()
    long = [(i + 1, len(l)) for i, l in enumerate(lines) if len(l) > 100]
    tabs = [i + 1 for i, l in enumerate(lines) if '\t' in l]
    trail = [i + 1 for i, l in enumerate(lines) if l != l.rstrip()]
    micro = [i + 1 for i, l in enumerate(lines) if 'µ' in l]
    ok = not long and len(lines) <= 1000 and not micro
    bad += not ok
    print(f'{"OK  " if ok else "FAIL"} {path}: {len(lines)} lines, max width '
          f'{max((len(l) for l in lines), default=0)}, over-100 {long}, micro-sign lines {micro}, '
          f'tab lines {tabs}, trailing-space lines {trail}')
print(f'WIDTH/SIZE {"PASS" if not bad else "FAIL"}')
sys.exit(1 if bad else 0)
