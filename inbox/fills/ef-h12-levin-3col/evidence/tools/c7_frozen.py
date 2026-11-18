"""C7: compare a changed existing file at base and head; only the listed inserted lines are allowed.
Usage: c7_frozen.py <base-rev> <path> <allowed-insertions.txt> [--control]"""
import sys, subprocess, difflib
base, path, allowf = sys.argv[1:4]
allowed = [l.rstrip('\n') for l in open(allowf, encoding='utf-8')]
b = subprocess.run(['git', 'show', f'{base}:{path}'], capture_output=True, text=True).stdout.split('\n')
h = subprocess.run(['git', 'show', f'HEAD:{path}'], capture_output=True, text=True).stdout.split('\n')
if '--control' in sys.argv:  # alter one character of one unchanged line of the head copy
    i = next(k for k, l in enumerate(h) if l.startswith('import TCSlib.Cryptography.ZeroKnowledge.Encoding'))
    h[i] = h[i][:-1] + ('X' if h[i][-1] != 'X' else 'Y')
diffs = []
ins = []
for op in difflib.SequenceMatcher(None, b, h, autojunk=False).get_opcodes():
    tag, i1, i2, j1, j2 = op
    if tag == 'equal': continue
    if tag == 'insert': ins += h[j1:j2]
    else: diffs.append((tag, b[i1:i2], h[j1:j2]))
bad_ins = [l for l in ins if l not in allowed]
print(f'{path}: base {len(b)} lines, head {len(h)} lines; inserted {len(ins)} (allowed {len(ins)-len(bad_ins)}), '
      f'non-insert differences {len(diffs)}, disallowed insertions {len(bad_ins)}')
for d in diffs: print('  DIFF', d)
for l in bad_ins: print('  BAD-INSERT', l)
print('RESULT', 'PASS' if not diffs and not bad_ins and len(ins) == len(allowed) else 'FAIL')
