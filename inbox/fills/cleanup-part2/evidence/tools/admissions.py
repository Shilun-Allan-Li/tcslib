#!/usr/bin/env python3
"""Lexical admissions census by occurrence and declaration (cleanup-part2).
python3 -I admissions.py <rev> <out.json> [--compare inputs/lexical-admission-occurrences.json]
Tokens `sorry`, `admit`, `sorryAx`, `axiom` in code (nested comments, line comments, strings, char
literals and «quoted» names excluded) of every TCSlib/*.lean, TCSlib.lean and audits/*.lean file
at <rev>; each occurrence is attributed to its enclosing column-0 declaration (the declaration
keyword line at or above it)."""
import sys, re, json, subprocess, collections
rev, out = sys.argv[1], sys.argv[2]
F = '/workspace/cp2/src'
files = [p for p in subprocess.check_output(['git', '-C', F, 'ls-tree', '-r', '--name-only', rev], text=True).split()
         if p.endswith('.lean') and (p.startswith('TCSlib/') or p == 'TCSlib.lean' or p.startswith('audits/'))]
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*(theorem|lemma|def|instance|structure|inductive|abbrev|class|example|opaque|axiom)\b\s*([^\s(:{\[]*)")
def code_tokens(src):
    res = []; i = 0; n = len(src); depth = 0; line = 1; col = 0
    tok = re.compile(r'[A-Za-z_][\w.\'!?]*')
    while i < n:
        c = src[i]
        if src.startswith('/-', i): depth += 1; i += 2; continue
        if depth:
            if src.startswith('-/', i): depth -= 1; i += 2
            else: i += 1
            continue
        if src.startswith('--', i):
            j = src.find('\n', i); i = n if j < 0 else j; continue
        if c == '"':
            j = i + 1
            while j < n and src[j] != '"': j += 2 if src[j] == '\\' else 1
            i = j + 1; continue
        if c == "'" and i + 2 < n and src[i + 2] == "'": i += 3; continue
        if c == '«':
            j = src.find('»', i); i = n if j < 0 else j + 1; continue
        m = tok.match(src, i)
        if m and (i == 0 or not (src[i - 1].isalnum() or src[i - 1] in "_.'")):
            w = m.group(0)
            if w in ('sorry', 'admit', 'sorryAx', 'axiom'): res.append((w, i))
            i = m.end(); continue
        i += 1
    return res
occ = []
for p in files:
    src = subprocess.check_output(['git', '-C', F, 'show', f'{rev}:{p}'], text=True)
    lines = src.split('\n'); offs = [0]
    for l in lines: offs.append(offs[-1] + len(l) + 1)
    import bisect
    starts = [(i, m.group(2) or f'<anonymous {m.group(1)}>') for i, l in enumerate(lines) if (m := DECL.match(l))]
    for w, pos in code_tokens(src):
        ln = bisect.bisect_right(offs, pos) - 1
        d = max((s for s in starts if s[0] <= ln), default=(None, None))
        occ.append({'path': p, 'line': ln + 1, 'column': pos - offs[ln] + 1, 'token': w, 'decl': d[1], 'decl_line': (d[0] + 1) if d[0] is not None else None})
tot = collections.Counter(o['token'] for o in occ)
bydecl = collections.Counter((o['path'], o['decl'], o['token']) for o in occ)
res = {'rev': rev, 'files': len(files), 'totals': dict(tot), 'occurrences': occ,
       'by_declaration': [{'path': a, 'decl': b, 'token': c, 'count': n} for (a, b, c), n in sorted(bydecl.items(), key=str)]}
if len(sys.argv) > 4 and sys.argv[3] == '--compare':
    base = json.load(open(sys.argv[4]))
    bk = collections.Counter((b['path'], b['line'], b['column'], b['token']) for b in base)
    mk = collections.Counter((o['path'], o['line'], o['column'], o['token']) for o in occ)
    res['compare_with_inputs'] = {'inputs_occurrences': sum(bk.values()), 'ours': sum(mk.values()),
        'only_inputs': [list(k) for k in (bk - mk)], 'only_ours': [list(k) for k in (mk - bk)]}
json.dump(res, open(out, 'w'), indent=1)
print(rev[:10], dict(tot), res.get('compare_with_inputs', {}).get('only_inputs', [])[:5], res.get('compare_with_inputs', {}).get('only_ours', [])[:5])
