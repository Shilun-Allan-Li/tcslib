# Sorry census of the sweep log, compared with the pack's base-sorries.txt.
import re, sys
F = '/home/user/fill'
log = open(F + '/evidence/logs/sweep.log').read().splitlines()
cur = None; found = {}
for l in log:
    m = re.match(r'== (\S+) start', l)
    if m: cur = m.group(1); continue
    m = re.match(r"(\S+\.lean):(\d+):(\d+): warning: declaration uses 'sorry'", l)
    if m and cur:
        path, ln, col = m.group(1), int(m.group(2)), int(m.group(3))
        line = open(F + '/' + path).read().splitlines()[ln - 1]
        tok = re.match(r"[\w.'₀-₉!?]+", line[col:])
        found.setdefault(cur, []).append(tok.group(0) if tok else f'?{ln}:{col}')
def short(m):
    return m[len('TCSlib/Complexity/'):] if m.startswith('TCSlib/Complexity/') else m
base = {}
for l in open(sys.argv[1]):
    if l.startswith('TOTAL'): continue
    mod, cnt, names = [x.strip() for x in l.split(':', 2)]
    base[mod] = sorted(n.strip() for n in names.split(','))
now = {short(m): sorted(v) for m, v in found.items()}
out = []
for m in sorted(set(base) | set(now)):
    b, n = base.get(m, []), now.get(m, [])
    out.append(f"{m}: {len(n)}: {', '.join(n)}" + ('' if b == n else f"   [base {len(b)}: {', '.join(b)}]"))
out.append(f"TOTAL {sum(len(v) for v in now.values())} (base {sum(len(v) for v in base.values())})")
removed = sorted(set((m, x) for m in base for x in base[m]) - set((m, x) for m in now for x in now[m]))
added = sorted(set((m, x) for m in now for x in now[m]) - set((m, x) for m in base for x in base[m]))
out.append(f"removed vs base: {removed}")
out.append(f"added vs base: {added}")
print('\n'.join(out))
