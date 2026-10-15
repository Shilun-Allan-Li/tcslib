"""Round-2 pair enumeration for the ARM fill gate (read-only analysis of round-1 screen output).

Reads the round-1 combined screen output over flattened, path-encoded byte-identical copies
(the repository's copy-text-screen.py, unmodified), and enumerates every UNORDERED pair with at
least one side in an added file, INCLUDING same-file pairs (round 1's ledger.py skipped
pa == pb). Declaration spans/body sizes use ledger.py's own rules (comment-stripped text that
keeps line structure; body = whitespace-free text after the first depth-0 `:=`, or the
`|`/`where` part; code lines = non-blank comment-stripped lines of the span).

usage: python3 -I pairs.py <screen.out> <labels.tsv> <added.txt> <screen-root> <out.tsv>
out.tsv columns: pid, cat (same|internal|lib), A path, A name, A lines, A code, A chars,
B path, B name, B lines, B code, B chars, hits (directed, 'A>B sh/len' meaning A reproduces
sh chars of B's len-char body), maxshared
"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from leancore import strip_keep_lines, DECL, body
out, labels, added, sroot, dst = sys.argv[1:6]
lab = {}
for l in open(labels, encoding='utf-8'):
    a, p, _ = l.rstrip('\n').split('\t'); lab[a] = p
new = {l.strip() for l in open(added) if l.strip()}
spans = {}
for flat, path in lab.items():
    t = strip_keep_lines(open(os.path.join(sroot, flat), encoding='utf-8').read())
    ms = list(DECL.finditer(t))
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(t)
        seg = t[m.start():end]
        bd = re.sub(r'\s+', '', body(seg))
        l0 = t.count('\n', 0, m.start()) + 1
        l1 = l0 + seg.rstrip().count('\n')
        cl = sum(1 for l in seg.split('\n') if l.strip())
        spans.setdefault((path, m.group(3)), []).append((l0, l1, cl, len(bd)))
P = re.compile(r'^\s+(\S+?)::(\S+)\s+reproduces\s+(\S+?)::(\S+): (\d+)/(\d+) = (\d+)%')
pairs = {}; directed = {'same': 0, 'internal': 0, 'lib': 0}
for l in open(out, encoding='utf-8'):
    m = P.match(l)
    if not m: continue
    fa, a, fb, b, sh, ln, pct = m.groups()
    pa, pb = lab[fa], lab[fb]
    if pa not in new and pb not in new: continue
    cat = 'same' if pa == pb else ('internal' if (pa in new and pb in new) else 'lib')
    directed[cat] += 1
    A, B = (pa, a), (pb, b)
    key = tuple(sorted([A, B]))
    if cat == 'lib':   # orient: added side first
        key = (A, B) if pa in new else (B, A)
    pairs.setdefault((cat, key), []).append((A, B, int(sh), int(ln)))
def sp(k):
    s = spans.get(k, [])
    return s[0] if s else (0, 0, 0, 0), len(s)
order = {'same': 0, 'internal': 1, 'lib': 2}
rows = sorted(pairs.items(), key=lambda kv: (order[kv[0][0]], kv[0][1][0][0], sp(kv[0][1][0])[0][0], kv[0][1][1][0], sp(kv[0][1][1])[0][0]))
pref = {'same': 'S', 'internal': 'I', 'lib': 'L'}; cnt = {'same': 0, 'internal': 0, 'lib': 0}
with open(dst, 'w', encoding='utf-8') as f:
    f.write('pid\tcat\tA_path\tA_name\tA_lines\tA_code\tA_chars\tB_path\tB_name\tB_lines\tB_code\tB_chars\thits\tmaxshared\tname_multiplicity\n')
    for (cat, (A, B)), hs in rows:
        cnt[cat] += 1; pid = f'{pref[cat]}{cnt[cat]:03d}'
        (sa, na), (sb, nb) = sp(A), sp(B)
        hits = '; '.join(f'{"A>B" if x == A else "B>A"} {sh}/{ln}' for x, y, sh, ln in sorted(hs, key=lambda h: h[0] != A))
        f.write(f'{pid}\t{cat}\t{A[0]}\t{A[1]}\t{sa[0]}-{sa[1]}\t{sa[2]}\t{sa[3]}\t{B[0]}\t{B[1]}\t{sb[0]}-{sb[1]}\t{sb[2]}\t{sb[3]}\t{hits}\t{max(h[2] for h in hs)}\t{na}/{nb}\n')
print('directed hits touching an added file:', directed, 'total', sum(directed.values()))
print('unordered pairs:', cnt, 'total', sum(cnt.values()))
