#!/usr/bin/env python3
"""Explicit-source review (cleanup-part2): every identifier passed to simp/simp only/simp_all/simpa/
dsimp/simp_rw/field_simp/norm_num/rw/rwa/erw/rewrite/nth_rewrite/nth_rw/unfold/delta in the given
files, resolved against the dumped name table under the file's namespace/section/open context.

python3 -I explicit_scan.py <name-table.tsv> <out.json> <file.lean>...

Comments are blanked first (positions kept), so bracketed lists spanning blank or comment-only
lines are read to their balanced `]`; `unfold`/`delta` read identifiers to the end of the tactic.
Each identifier is classified: THEOREM (any home), OWN_DEF (definition of the scanned module),
FOREIGN_TCS_DEF (definition homed in another TCSlib module; reducible/instance/matcher flagged),
CORE_MATHLIB_DEF (definition homed outside TCSlib), LOCAL_OR_UNRESOLVED (hypotheses, terms)."""
import sys, re, json, collections
table, out = sys.argv[1], sys.argv[2]
files = sys.argv[3:]
by_user = collections.defaultdict(list)
for line in open(table):
    if not line.startswith('NAME\t'): continue
    _, name, kind, status, home, flags = line.rstrip('\n').split('\t')
    user = name
    m = re.match(r'_private\.(.+?)\.0\.(.+)$', name)
    if m: user = m.group(2)
    by_user[user].append((name, kind, status, home, flags))
KW = re.compile(r"(?<![\w.'])(simp_all|simp_rw|simpa|simp|dsimp|field_simp|norm_num|rwa|rewrite|erw|rw|nth_rewrite|nth_rw|unfold|delta)\b")
IDENT = re.compile(r"[A-Za-z_\u00c0-\u024f\u0370-\u03ff\u1d00-\u1dbf\u2100-\u214f][\w.'?!\u2080-\u209c\u1d62-\u1d6a\u00c0-\u024f\u0370-\u03ff]*")
def blank(s):
    out = []; i = 0; n = len(s); depth = 0
    while i < n:
        if s.startswith('/-', i): depth += 1; out.append('  '); i += 2; continue
        if depth:
            if s.startswith('-/', i): depth -= 1; out.append('  '); i += 2
            else: out.append('\n' if s[i] == '\n' else ' '); i += 1
            continue
        if s.startswith('--', i):
            j = s.find('\n', i); j = n if j < 0 else j; out.append(' ' * (j - i)); i = j; continue
        if s[i] == '"':
            j = i + 1
            while j < n and s[j] != '"': j += 2 if s[j] == '\\' else 1
            out.append(' ' * (j + 1 - i)); i = j + 1; continue
        out.append(s[i]); i += 1
    return ''.join(out)
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*(theorem|lemma|def|instance|structure|inductive|abbrev|class|example|opaque)\b\s*([^\s(:{\[]*)")
res = {'items': [], 'summary': {}}
for f in files:
    mod = f[:-5].replace('/', '.')
    raw = open(f).read(); code = blank(raw)
    lines = code.split('\n')
    # namespace/section stack with opens
    stack = [('', [])]  # (namespace prefix, opens)
    ctx_at = []  # per line: (ns, opens)
    decl_at = []
    cur_decl = None
    for i, l in enumerate(lines):
        t = l.strip()
        m = re.match(r'^namespace\s+(\S+)', t)
        if m:
            base = stack[-1][0]
            stack.append(((base + '.' if base else '') + m.group(1), list(stack[-1][1])))
        elif re.match(r'^section\b', t):
            stack.append((stack[-1][0], list(stack[-1][1])))
        elif re.match(r'^end\b', t) and len(stack) > 1:
            stack.pop()
        m = re.match(r'^open\s+(.*)$', t)
        if m and not t.startswith('open scoped') and ' in' not in t:
            for o in m.group(1).split():
                if o in ('in',) or o.startswith('('): break
                stack[-1][1].append(o)
        d = DECL.match(l)
        if d: cur_decl = d.group(2) or f'<anonymous {d.group(1)}>'
        ctx_at.append((stack[-1][0], list(stack[-1][1])))
        decl_at.append(cur_decl)
    offs = [0]
    for l in lines: offs.append(offs[-1] + len(l) + 1)
    import bisect
    def line_of(p): return bisect.bisect_right(offs, p) - 1
    for m in KW.finditer(code):
        kw = m.group(1); p = m.end(); ln = line_of(m.start())
        ids = []
        if kw in ('unfold', 'delta'):
            e = len(code)
            for stop in ['\n', ';', '<;>', ' at ', ')']:
                q = code.find(stop, p)
                if q >= 0: e = min(e, q)
            ids = [(x, ln) for x in IDENT.findall(code[p:e])]
        else:
            q = p
            while q < len(code) and code[q] in ' \t': q += 1
            if code.startswith('only', q): q += 4
            while q < len(code) and code[q] in ' \t\n': q += 1
            if q >= len(code) or code[q] != '[': continue
            depth = 0; e = q
            while e < len(code):
                if code[e] in '[(': depth += 1
                elif code[e] in '])':
                    depth -= 1
                    if depth == 0: break
                e += 1
            inner = code[q + 1:e]
            # split at top-level commas
            parts = []; d = 0; cur = ''; start = q + 1
            for k, ch in enumerate(inner):
                if ch in '([{⟨': d += 1
                elif ch in ')]}⟩': d -= 1
                if ch == ',' and d == 0:
                    parts.append((cur, start)); cur = ''; start = q + 2 + k; continue
                cur += ch
            parts.append((cur, start))
            for item, st in parts:
                it = item.strip()
                it = re.sub(r'^(←|<-)\s*', '', it); it = re.sub(r'^-\s*', '', it); it = re.sub(r'^↓\s*', '', it)
                if it.startswith(('show ', '(', 'fun ', '@')):
                    if it.startswith('@'): it = it[1:]
                    else: continue
                mm = IDENT.match(it)
                if mm: ids.append((mm.group(0), line_of(st + (len(item) - len(item.lstrip())))))
        for ident, iln in ids:
            ns, opens = ctx_at[iln]
            cands = []
            parts = ns.split('.') if ns else []
            for k in range(len(parts), -1, -1):
                pre = '.'.join(parts[:k])
                cands.append((pre + '.' if pre else '') + ident)
            for o in opens:
                # an `open X` inside namespace N also resolves N.X
                cands.append(o + '.' + ident)
                for k in range(len(parts), 0, -1):
                    cands.append('.'.join(parts[:k]) + '.' + o + '.' + ident)
            hits = []
            for c in dict.fromkeys(cands):
                hits += by_user.get(c, [])
            # prefer exact matches of the most specific candidate
            cls = 'LOCAL_OR_UNRESOLVED'; info = None
            if hits:
                # own private names
                defs = [h for h in hits if h[1] in ('def', 'opaque')]
                thms = [h for h in hits if h[1] not in ('def', 'opaque')]
                h = (defs or thms)[0]; info = h
                if h[1] not in ('def', 'opaque'): cls = 'THEOREM_OR_OTHER'
                elif h[3] == mod: cls = 'OWN_DEF'
                elif h[3].startswith('TCSlib'): cls = 'FOREIGN_TCS_DEF'
                else: cls = 'CORE_MATHLIB_DEF'
                if len({x[0] for x in hits}) > 1: cls += '?AMBIGUOUS'
            res['items'].append({'file': f, 'line': iln + 1, 'decl': decl_at[iln], 'tactic': kw, 'ident': ident,
                                 'class': cls, 'resolved': info[0] if info else None, 'home': info[3] if info else None,
                                 'status': info[2] if info else None, 'flags': info[4] if info else None,
                                 'all_hits': sorted({x[0] for x in hits})})
c = collections.Counter(i['class'] for i in res['items'])
res['summary'] = dict(c)
json.dump(res, open(out, 'w'), indent=1, ensure_ascii=False)
print(dict(c))
