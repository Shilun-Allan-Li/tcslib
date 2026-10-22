import sys, re
# usage: static_sorry.py <root> <module list>...: per module, declarations whose comment-stripped text has `sorry`
root, lists = sys.argv[1], sys.argv[2:]
def strip(src):
    out, i, d = [], 0, 0
    while i < len(src):
        if src.startswith('/-', i): d += 1; i += 2; continue
        if src.startswith('-/', i) and d > 0: d -= 1; i += 2; continue
        if d == 0: out.append(src[i])
        i += 1
    return '\n'.join(l.split('--')[0] for l in ''.join(out).splitlines())
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(theorem|lemma|def|abbrev|instance|example|structure|inductive)\b', re.M)
for lf in lists:
    mods = [l.strip() for l in open(lf) if l.strip()]
    tot, hit = 0, {}
    for m in mods:
        s = strip(open(f'{root}/{m}.lean', encoding='utf-8').read())
        starts = [x.start() for x in DECL.finditer(s)] + [len(s)]
        k = sum(1 for a, b in zip(starts, starts[1:]) if re.search(r'\bsorry\b', s[a:b]))
        if k: hit[m.replace('TCSlib/Complexity/', '')] = k; tot += k
    print(f'{lf.split("/")[-1]} at {root.split("/")[-1]}: {tot} in {len(hit)} modules {hit}')
