import re, sys
# usage: pairseg.py <fileA> <nameA> <fileB> <nameB>: the v3 screen's tiled segments (>= 25 chars) of B's body found in A's
# (same stripping, body extraction and greedy tiling as scripts/copy-text-screen-v3.py).
def strip(src):
    out = []; i = 0; depth = 0; n = len(src)
    while i < n:
        if src.startswith('/-', i): depth += 1; i += 2; continue
        if depth and src.startswith('-/', i): depth -= 1; i += 2; continue
        if depth: i += 1; continue
        if src.startswith('--', i):
            j = src.find('\n', i); i = n if j < 0 else j; continue
        out.append(src[i]); i += 1
    return ''.join(out)
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?((?:(?:noncomputable|private|protected)\s+)*)"
                  r"(def|theorem|lemma|abbrev|instance|structure|inductive)\s+(\S+)", re.M)
def body(b):
    d = 0
    for i, ch in enumerate(b):
        if ch in '([{⟨': d += 1
        elif ch in ')]}⟩': d -= 1
        elif b.startswith(':=', i) and d == 0: return b[i + 2:]
    return ''
def get(path, name):
    t = strip(open(path, encoding='utf-8').read()); ms = list(DECL.finditer(t))
    for i, m in enumerate(ms):
        if m.group(3) == name:
            end = ms[i + 1].start() if i + 1 < len(ms) else len(t)
            return re.sub(r'\s+', '', body(t[m.start():end]))
    sys.exit('not found ' + name)
def lcs(a, b):
    lo, hi, best = 0, min(len(a), len(b)), ''
    while lo < hi:
        mid = (lo + hi + 1) // 2
        subs = {b[i:i + mid] for i in range(len(b) - mid + 1)}
        hit = next((a[i:i + mid] for i in range(len(a) - mid + 1) if a[i:i + mid] in subs), None)
        if hit is not None: lo, best = mid, hit
        else: hi = mid - 1
    return lo, best
a = get(sys.argv[1], sys.argv[2]); b = get(sys.argv[3], sys.argv[4])
print(f'{sys.argv[2]} (len {len(a)}) reproduces {sys.argv[4]} (len {len(b)}); source body: {b}')
c = 0
while True:
    n, seg = lcs(a, b)
    if n < 25: break
    c += n; print(f'  segment {n}: {seg}')
    a = a.replace(seg, '\x00', 1); b = b.replace(seg, '\x01', 1)
print(f'total {c}')
