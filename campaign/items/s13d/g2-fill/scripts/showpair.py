"""Print the tiled common segments (>= 25 chars) of two declarations' whitespace-free bodies, as
the v3 screen measures them. Usage: python3 -I showpair.py <file> <declA> <declB>  (A reproduces B)"""
import re, sys
src, A, Bn = sys.argv[1:4]
def strip(s):
    out = []; i = 0; depth = 0; n = len(s)
    while i < n:
        if s.startswith('/-', i): depth += 1; i += 2; continue
        if depth and s.startswith('-/', i): depth -= 1; i += 2; continue
        if depth: i += 1; continue
        if s.startswith('--', i):
            j = s.find('\n', i); i = n if j < 0 else j; continue
        out.append(s[i]); i += 1
    return ''.join(out)
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?((?:(?:noncomputable|private|protected)\s+)*)(def|theorem|lemma|abbrev|instance|structure|inductive)\s+(\S+)", re.M)
def body(b):
    d = 0
    for i, ch in enumerate(b):
        if ch in '([{⟨': d += 1
        elif ch in ')]}⟩': d -= 1
        elif b.startswith(':=', i) and d == 0: return b[i + 2:]
    return ''
t = strip(open(src, encoding='utf-8').read()); ms = list(DECL.finditer(t)); bodies = {}
for i, m in enumerate(ms):
    end = ms[i + 1].start() if i + 1 < len(ms) else len(t)
    bodies[m.group(3)] = re.sub(r'\s+', '', body(t[m.start():end]))
def lcs(a, b):
    lo, hi, best = 0, min(len(a), len(b)), ''
    while lo < hi:
        mid = (lo + hi + 1) // 2
        subs = {b[i:i + mid] for i in range(len(b) - mid + 1)}
        hit = next((a[i:i + mid] for i in range(len(a) - mid + 1) if a[i:i + mid] in subs), None)
        if hit is not None: lo, best = mid, hit
        else: hi = mid - 1
    return lo, best
a, b = bodies[A], bodies[Bn]; tot = 0
while True:
    n, seg = lcs(b, a)
    if n < 25: break
    tot += n; print(f'[{n}] {seg}'); b = b.replace(seg, '\x00', 1); a = a.replace(seg, '\x01', 1)
print('total', tot, 'of', len(bodies[Bn]))
