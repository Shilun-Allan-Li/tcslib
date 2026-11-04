"""Docstrings, proof lengths and sketches of the new declarations; campaign words in new text
(python3 -I).  usage: python3 -I doccheck.py <base> <head>"""
import re, sys, difflib
A = open(sys.argv[1], encoding='utf-8').read().split('\n'); B = open(sys.argv[2], encoding='utf-8').read().split('\n')
DECL = re.compile(r'^(private\s+)?(theorem|def|abbrev|lemma|instance|structure|inductive)\s+(\S+)')
decls = [(i, m.group(3), m.group(2), bool(m.group(1))) for i, l in enumerate(B) for m in [DECL.match(l)] if m]
print('## declarations at head:', len(decls))
rows = []
for k, (i, name, kind, priv) in enumerate(decls):
    end = decls[k + 1][0] if k + 1 < len(decls) else len(B)
    # back off the next declaration's docstring
    j = end
    while j > i and not B[j - 1].startswith('/--') and j != end - 0 and False: j -= 1
    seg = B[i:end]
    # the next docstring starts at the last '/--' line before end
    cut = len(seg)
    for t in range(len(seg) - 1, 0, -1):
        if seg[t].startswith('/--'): cut = t; break
        if seg[t].startswith('end ') or seg[t].startswith('namespace'): cut = t
    seg = seg[:cut]
    while seg and not seg[-1].strip(): seg.pop()
    proof = 0
    for t, l in enumerate(seg):
        if ':= by' in l or l.rstrip().endswith(':=') or ' := ' in l:
            proof = len(seg) - t - 1; break
    # docstring above
    d = i - 1
    doc = []
    if d >= 0 and B[d].rstrip().endswith('-/'):
        s = d
        while not B[s].startswith('/--'): s -= 1
        doc = B[s:d + 1]
    sketch = any('**Proof sketch.**' in l for l in doc)
    rows.append((i + 1, name, kind, priv, len(doc), proof, sketch))
for r in rows:
    flag = 'NEEDS SKETCH' if r[5] > 20 and not r[6] else ''
    print(f'  head {r[0]:4d} {"private " if r[3] else "public  "}{r[2]:8s} {r[1]:32s} doc {r[4]:2d} lines; proof {r[5]:3d} lines; sketch {r[6]} {flag}')
print('without a docstring:', [r[1] for r in rows if r[4] == 0])
print('proofs over 20 lines without a sketch:', [r[1] for r in rows if r[5] > 20 and not r[6]])
print('proofs over 20 lines:', [(r[1], r[5]) for r in rows if r[5] > 20])
sm = difflib.SequenceMatcher(a=A, b=B, autojunk=False)
added = [(j + 1, B[j]) for tag, a1, a2, b1, b2 in sm.get_opcodes() if tag != 'equal' for j in range(b1, b2)]
pat = re.compile(r'\b(NF|C1|E-?Q|checkpoint|cp\d|gate|finding|round|phase P|P3\.3|campaign|audits?/|brief|ruling|D[1-4]\b|rule 1[01]|user,|20\d\d-\d\d-\d\d|fill|worker|Codex|review|sweep 0|sweep zero|sorry)\b', re.I)
print('## campaign-like words in added lines (all hits; judged in REVIEW.md):')
for n, l in added:
    for m in pat.finditer(l): print(f'  head {n}: [{m.group(0)}] {l.strip()[:110]}')
