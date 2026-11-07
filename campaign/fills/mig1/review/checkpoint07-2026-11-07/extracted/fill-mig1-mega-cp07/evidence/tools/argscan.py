"""argscan.py <repo> <module file> <decl,names> : list every simp/simp only/simpa/dsimp/rw/rewrite/
erw/unfold/delta/show/change argument in the named declarations that names a TCSlib definition
(def/abbrev/structure-valued def) from another file. Definition index: declfreeze chunks over
TCSlib/**/*.lean (namespace-qualified)."""
import os, re, sys
repo, mod, names = sys.argv[1], sys.argv[2], [n for n in sys.argv[3].split(',') if n]
code = open(os.path.join(repo, 'devtools/seyoon/declfreeze.py'), encoding='utf-8').read()
code = code[:code.index('a = chunks(open(sys.argv[1])')]; ns = {}; exec(compile(code, 'df', 'exec'), ns); chunks = ns['chunks']
defs = {}
KW = re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*(def|abbrev)\s', re.M)
for root, _, fs in os.walk(os.path.join(repo, 'TCSlib')):
    for f in fs:
        if not f.endswith('.lean'): continue
        p = os.path.join(root, f); rel = os.path.relpath(p, repo)
        try: t = open(p, encoding='utf-8').read()
        except Exception: continue
        for n, priv, txt in chunks(t):
            body = txt.split('-/', 1)[1] if txt.startswith('/--') else txt
            m = KW.search(body)
            if m and not priv:
                defs.setdefault(n, set()).add((rel, m.group(1)))
short = {}
for n, s in defs.items():
    parts = n.split('.')
    for k in range(1, len(parts) + 1): short.setdefault('.'.join(parts[-k:]), set()).update((n, r, kd) for r, kd in s)
text = open(os.path.join(repo, mod), encoding='utf-8').read(); relmod = os.path.relpath(os.path.join(repo, mod), repo)
ch = {n: t for n, p, t in chunks(text)}
TAC = re.compile(r'\b(simp only|simp|simpa only|simpa|dsimp only|dsimp|rw|rewrite|erw|simp_rw|unfold|delta)\b\s*(\[[^\]]*\]|[^\n]*)')
SC = re.compile(r'\b(show|change)\b([^\n]*)')
tot = 0
for want in names:
    key = [k for k in ch if k == want or k.endswith('.' + want)]
    if len(key) != 1: print('?? not found', want); continue
    t = ch[key[0]]; t = t.split('-/', 1)[1] if t.startswith('/--') else t
    hits = []
    for m in TAC.finditer(t):
        arglist = m.group(2)
        if m.group(1) in ('unfold', 'delta'):
            toks = re.findall(r'[A-Za-z_][A-Za-z0-9_.\'₀-₉]*', arglist)
        elif arglist.startswith('['):
            elems, d, cur = [], 0, ''
            for c in arglist[1:-1]:
                if c in '([{⟨': d += 1
                if c in ')]}⟩': d -= 1
                if c == ',' and d == 0: elems.append(cur); cur = ''
                else: cur += c
            elems.append(cur)
            toks = []
            for e in elems:
                mm = re.match(r'\s*(?:←\s*)?([A-Za-z_][A-Za-z0-9_.\'₀-₉]*)', e)
                if mm: toks.append(mm.group(1))
        else:
            toks = []
        for tok in toks:
            tok = tok.lstrip('←')
            for (full, rel, kd) in short.get(tok, ()):
                if rel != relmod: hits.append((m.group(1), tok, full, rel, kd))
    for m in SC.finditer(t):
        for tok in re.findall(r'[A-Za-z_][A-Za-z0-9_.\'₀-₉]*', m.group(2)):
            for (full, rel, kd) in short.get(tok, ()):
                if rel != relmod and '.' in tok: hits.append((m.group(1), tok, full, rel, kd))
    seen = set()
    for h in hits:
        if h in seen: continue
        seen.add(h); tot += 1
        print(f'{key[0]}: {h[0]} [{h[1]}] -> {h[2]} ({h[4]} in {h[3]})')
print(f'TOTAL foreign-definition arguments: {tot}')
