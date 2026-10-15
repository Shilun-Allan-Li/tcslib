import re, sys, json
sys.path.insert(0, sys.argv[1])
from decls import scan
# For each public theorem/lemma: extract statement text (from decl line to the first top-level ':=' ), strip comments
def stmt_of(lines, d):
    txt = []
    for i in range(d['line'] - 1, d['end']):
        txt.append(lines[i])
    s = '\n'.join(txt)
    # remove comments
    s = re.sub(r'/-.*?-/', '', s, flags=re.S)
    s = re.sub(r'--[^\n]*', '', s)
    # find ':=' at depth 0 of brackets
    depth = 0; j = 0
    while j < len(s):
        c = s[j]
        if c in '([{⟨': depth += 1
        elif c in ')]}⟩': depth -= 1
        elif s.startswith(':=', j) and depth == 0:
            return s[:j]
        elif s.startswith(' where', j) and depth == 0:
            return s[:j]
        j += 1
    return s
def concl(st):
    # conclusion: after the last top-level ':' that separates binders from type
    depth = 0
    for j, c in enumerate(st):
        if c in '([{⟨': depth += 1
        elif c in ')]}⟩': depth -= 1
        elif c == ':' and depth == 0 and not st.startswith(':=', j):
            return st[j+1:].strip()
    return ''
out = []
for f in sys.argv[3:]:
    r, lines = scan(f)
    for d in r:
        if d['kind'] not in ('theorem', 'lemma'):
            continue
        st = stmt_of(lines, d)
        c = concl(st)
        cn = ' '.join(c.split())
        m = re.match(r'^∃\s*\(?\s*([A-Za-z_][\w₀-₉\']*)', cn)
        ex = False
        if m:
            # Is the first existential binder a machine?
            ex = bool(re.match(r'^∃\s*(\(\s*)?[A-Za-z_][\w₀-₉\' ]*\s*:\s*(FinTM|MultiTapeTM|Turing\.FinTM|OracleTM|FinNDTM|CodeTM)', cn)) or bool(re.match(r'^∃\s*(M|D|N|U|T|C)\b', cn))
        # also existentials nested after ∀ ... , ∃ M
        nested = bool(re.search(r'∃\s*\(?\s*[A-Za-z_][\w₀-₉\']*\s*:\s*(FinTM|MultiTapeTM|OracleTM|FinNDTM)', cn)) or bool(re.search(r',\s*∃\s*\(?(M|D|N|U)\b', cn))
        out.append(dict(private=d['private'], file=f.split('TCSlib/')[-1], line=d['line'], name=d['name'], top=ex, nested=nested and not ex, concl=cn[:400], stmt=' '.join(st.split())[:900]))
json.dump(out, open(sys.argv[2], 'w'), indent=0, ensure_ascii=False)
for o in out:
    if o['top'] or o['nested']:
        print(o['file'].split('/')[-1], o['line'], o['name'], 'TOP' if o['top'] else 'NESTED')
