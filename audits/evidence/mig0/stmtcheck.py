import sys
# usage: stmtcheck.py <earlier> <later>: every comment-stripped code line of <earlier>, except the
# `sorry` proof lines, appears in <later> in order (with `:= sorry` read as the start of a proof).
def strip(src):
    out, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith('/-', i): depth += 1; i += 2; continue
        if src.startswith('-/', i) and depth > 0: depth -= 1; i += 2; continue
        if depth == 0: out.append(src[i])
        i += 1
    return [l.split('--')[0].rstrip() for l in ''.join(out).split('\n') if l.split('--')[0].strip()]
a, b = (strip(open(p, encoding='utf-8').read()) for p in sys.argv[1:3])
j, miss = 0, []
for l in a:
    if l.strip() in ('run := sorry', 'exit_mem := sorry', 'cut := sorry', 'env := sorry'): continue
    probe = l[:-len('sorry')].rstrip() if l.endswith(':= sorry') else l
    k = next((t for t in range(j, len(b)) if b[t] == probe or (probe.endswith(':=') and b[t].startswith(probe))), None)
    if k is None: miss.append(l)
    else: j = k + 1
print(f'{sys.argv[1]} -> {sys.argv[2]}: {len(a)} code lines, {len(miss)} not found in order')
for m in miss: print('   MISSING:', m)
