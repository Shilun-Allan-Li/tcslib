#!/usr/bin/env python3
"""Draft owner-side `<name>_def` readers for simple definitions (cleanup-part2).
python3 -I gen_readers.py <missing-readers.json> <root> [--apply]
For each (count, full name, owner path, role): locate `def <short>` in the owner file (namespace
aware by the last component and the `namespace` stack), require a plain `:= body` definition
(no top-level `|` pattern clauses, no `where`, no `termination_by`/`decreasing_by`), and insert
after the definition block:

    /-- The defining equation of `short`: `short args = body`. -/
    theorem short_def <binders> : short <explicit args> = <body> := rfl

Prints the drafts; lists the definitions needing manual readers (pattern clauses, recursion,
structures, abbrevs/instances, not found)."""
import sys, json, re
miss = json.load(open(sys.argv[1])); root = sys.argv[2]; apply = '--apply' in sys.argv
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*(theorem|lemma|def|instance|structure|inductive|abbrev|class|example|opaque)\b")
def split_binders(h):
    out = []; i = 0
    while i < len(h):
        c = h[i]
        if c in '({[⦃':
            close = {'(': ')', '{': '}', '[': ']', '⦃': '⦄'}[c]; d = 0; j = i
            while j < len(h):
                if h[j] == c: d += 1
                elif h[j] == close:
                    d -= 1
                    if d == 0: break
                j += 1
            out.append(h[i:j + 1]); i = j + 1
        elif c.isspace(): i += 1
        else:
            break
    return out, h[i:]
manual = []; drafts = {}
for cnt, full, path, role in miss:
    short = full.split('.')[-1]
    src = open(f'{root}/{path}').read(); lines = src.split('\n')
    # namespace stack per line
    ns = []; found = None
    for k, l in enumerate(lines):
        m = re.match(r'^namespace\s+(\S+)', l)
        if m: ns.append(m.group(1))
        if re.match(r'^end\s+(\S+)', l) and ns and l.split()[1] == ns[-1]: ns.pop()
        m = re.match(r'^(?:@\[[^\]]*\]\s*)*((?:(?:private|protected|noncomputable)\s+)*)def\s+(\S+)', l)
        if m:
            nm = m.group(2)
            fullhere = '.'.join(['TCSlib'] if False else []) 
            cand = '.'.join(ns + [nm]) if ns else nm
            if cand == full or cand.endswith('.' + full) or full.endswith('.' + cand) and full.split('.')[-1] == nm.split('.')[-1] and cand.split('.')[-1] == short:
                if cand == full or full.endswith(cand): found = (k, m.group(1), nm); break
    if not found: manual.append((full, 'definition line not found')); continue
    k, mods, nm = found
    j = k + 1
    while j < len(lines) and lines[j].strip() and not DECL.match(lines[j]) and not lines[j].startswith('/--'): j += 1
    block = '\n'.join(lines[k:j])
    hdr_body = block.split(':=', 1)
    if len(hdr_body) < 2 or re.search(r'\n\s*\|', block) or ' where' in hdr_body[0] or 'termination_by' in block or 'decreasing_by' in block:
        manual.append((full, 'pattern clauses / where / recursion / no := body')); continue
    header = hdr_body[0]; body = hdr_body[1].strip()
    head = re.sub(r'^(?:@\[[^\]]*\]\s*)*((?:(?:private|protected|noncomputable)\s+)*)def\s+\S+', '', header).strip()
    binders, rest = split_binders(head)
    rest = rest.strip()
    if not rest.startswith(':'): manual.append((full, 'no result type')); continue
    # recursive self-reference in body
    if re.search(r'(?<![\w.])' + re.escape(nm.split('.')[-1]) + r'(?![\w\'])', body): manual.append((full, 'self-reference (recursive)')); continue
    expl = []
    for b in binders:
        if b.startswith('('):
            inner = b[1:-1]; names_ = inner.split(':')[0].split()
            expl += names_
    priv = 'private ' if 'private' in mods else ''
    app = ' '.join([nm] + expl)
    bodyfmt = re.sub(r'\s*\n\s*', ' ', body)
    doc = f'/-- The defining equation of `{nm}`: `{app} = {bodyfmt}`. -/' if len(bodyfmt) < 160 else f'/-- The defining equation of `{nm}` (its body, unfolded once). -/'
    thm = f"{doc}\n{priv}theorem {nm}_def {' '.join(binders)} :\n    {app} =\n      {body.replace(chr(10), chr(10) + '  ')} := rfl"
    thm = re.sub(r'theorem (\S+)  :', r'theorem \1 :', thm)
    drafts.setdefault(path, []).append((j, thm, full))
for p, ds in drafts.items():
    print('==', p)
    for j, t, f in ds: print(t, '\n')
print('MANUAL:', len(manual)); [print('  ', m) for m in manual]
if apply:
    for p, ds in drafts.items():
        lines = open(f'{root}/{p}').read().split('\n')
        for j, t, f in sorted(ds, reverse=True):
            lines.insert(j, '\n' + t)
        open(f'{root}/{p}', 'w').write('\n'.join(lines))
print('DRAFTED:', sum(len(v) for v in drafts.values()))
