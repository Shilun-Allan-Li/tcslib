"""touched.py <repo> <base-rev> <head-rev> <out.json> <file>...
Declaration-level text comparison (private declarations included). Each top-level declaration
command is cut from its doc comment/attributes to the next top-level command; it is keyed by its
full name (namespace-qualified; `_root_.` removed). A declaration is TOUCHED when it is new or its
text (doc comment, attributes, statement and body; trailing whitespace ignored) differs from the
base file at the same path. New files: every declaration is touched. Prints a TSV summary."""
import sys, re, subprocess, json
repo, base, head, out = sys.argv[1:5]
files = sys.argv[5:]
KW = r'(theorem|lemma|def|abbrev|structure|inductive|instance|class|opaque|axiom)'
DECL = re.compile(r'^(@\[[^\]]*\]\s*)*((?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*' + KW + r'\b\s*([^\s(:{\[]*)')
TOP = re.compile(r'^(namespace|end|section|open|variable|universe|set_option|attribute|noncomputable section|mutual|#|example|import|/-!)')
def show(rev, f):
    r = subprocess.run(['git', '-C', repo, 'show', f'{rev}:{f}'], capture_output=True)
    return r.stdout.decode('utf-8') if r.returncode == 0 else None
def mask(src):
    # blank comments other than doc comments' positions are kept; we only need line structure
    return src
def decls(src):
    lines = src.split('\n')
    # find comment/doc spans to avoid matching keywords inside block comments
    incomment = [False] * len(lines); depth = 0
    for i, l in enumerate(lines):
        incomment[i] = depth > 0
        j = 0
        while j < len(l):
            if l.startswith('/-', j): depth += 1; j += 2
            elif l.startswith('-/', j) and depth: depth -= 1; j += 2
            elif l.startswith('--', j) and depth == 0: break
            else: j += 1
    ns, res, starts = [], [], []
    anon = 0
    for i, l in enumerate(lines):
        if incomment[i]: continue
        m = re.match(r'^namespace\s+(\S+)', l)
        if m: ns.append(m.group(1)); starts.append((i, None)); continue
        m = re.match(r'^end(\s+(\S+))?\s*$', l)
        if m:
            if m.group(2) and ns and ns[-1] == m.group(2): ns.pop()
            elif m.group(2) and ns and ns[-1].endswith('.' + m.group(2)): ns.pop()
            elif m.group(2) and ns and m.group(2) in ns[-1]: ns.pop()
            starts.append((i, None)); continue
        m = DECL.match(l)
        if m:
            kind, name = m.group(3), m.group(4)
            priv = bool(re.search(r'\bprivate\b', l[:m.start(3)]))
            if kind == 'instance' and (not name or name.startswith(':') or name.startswith('[')):
                anon += 1; name = f'<anonymous instance #{anon}>'
            full = name[7:] if name.startswith('_root_.') else '.'.join(ns + [name])
            # include preceding doc comment / attribute lines
            s = i
            k = i - 1
            if k >= 0 and lines[k].rstrip().endswith('-/'):
                while k >= 0 and not lines[k].lstrip().startswith('/--'): k -= 1
                if k >= 0: s = k
            starts.append((s, (full, kind, priv, i)))
            continue
        if TOP.match(l) or (l and not l[0].isspace() and not l.startswith('/-') and not l.startswith('--') and not l.startswith('|') and not l.startswith(')') and not incomment[i]):
            starts.append((i, None))
    # doc-comment starts for module docs etc. end previous decls as well
    for i, l in enumerate(lines):
        if not incomment[i] and (l.startswith('/-!') or l.startswith('/--')): starts.append((i, None))
    starts.sort(key=lambda t: (t[0], t[1] is None))
    # dedupe: a decl start supersedes a None at same line
    seen = {}
    for s, v in starts:
        if s not in seen or (v is not None): seen[s] = v
    pts = sorted(seen.items())
    for idx, (s, v) in enumerate(pts):
        if v is None: continue
        e = pts[idx + 1][0] if idx + 1 < len(pts) else len(lines)
        full, kind, priv, kwline = v
        text = '\n'.join(x.rstrip() for x in lines[s:e]).strip('\n')
        res.append(dict(name=full, kind=kind, private=priv, start=s + 1, decl_line=kwline + 1, end=e, text=text))
    return res
report = {'base': base, 'head': head, 'files': {}}
for f in files:
    old, new = show(base, f), show(head, f)
    a = {d['name']: d for d in decls(old)} if old else {}
    b = decls(new)
    rows = []
    for d in b:
        st = 'NEW_FILE' if old is None else ('ADDED' if d['name'] not in a else ('CHANGED' if a[d['name']]['text'] != d['text'] else 'UNCHANGED'))
        rows.append({k: d[k] for k in ('name', 'kind', 'private', 'start', 'decl_line', 'end')} | {'status': st, 'touched': st != 'UNCHANGED'})
        print(f"{st}\t{f}:{d['start']}-{d['end']}\t{d['name']}\t{d['kind']}{' private' if d['private'] else ''}")
    removed = sorted(set(a) - {d['name'] for d in b})
    for n in removed: print(f"REMOVED\t{f}\t{n}")
    report['files'][f] = {'new_file': old is None, 'declarations': rows, 'removed': removed,
                          'base_count': len(a), 'head_count': len(b)}
json.dump(report, open(out, 'w'), indent=1)
