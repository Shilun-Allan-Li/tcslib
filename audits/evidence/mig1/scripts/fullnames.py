import re, sys, glob, json
# Namespace-aware declaration index of all TCSlib .lean files (approximate: tracks namespace/section/end).
root = sys.argv[1]
KW = r'(theorem|lemma|def|abbrev|structure|inductive|instance|class|opaque|axiom)'
dpat = re.compile(r'^(?:@\[[^\]]*\]\s*)?((?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*' + KW + r'\s+([^\s:({\[]+)')
def strip(src):
    out = []; i = 0; depth = 0; n = len(src)
    while i < n:
        if src.startswith('/-', i): depth += 1; i += 2; continue
        if depth and src.startswith('-/', i): depth -= 1; i += 2; continue
        if depth:
            out.append('\n' if src[i] == '\n' else ' '); i += 1; continue
        if src.startswith('--', i):
            j = src.find('\n', i); j = n if j < 0 else j; out.append(' ' * (j - i)); i = j; continue
        out.append(src[i]); i += 1
    return ''.join(out)
idx = []
for f in sorted(glob.glob(root + '/TCSlib/**/*.lean', recursive=True)):
    rel = f[len(root) + 1:]
    stack = []  # list of (kind, name)
    for ln, l in enumerate(strip(open(f, encoding='utf-8').read()).split('\n'), 1):
        m = re.match(r'^namespace\s+(\S+)', l)
        if m: stack.append(('ns', m.group(1))); continue
        m = re.match(r'^section\b\s*(\S*)', l)
        if m: stack.append(('sec', m.group(1))); continue
        m = re.match(r'^end\b\s*(\S*)', l)
        if m:
            if stack: stack.pop()
            continue
        m = dpat.match(l)
        if m:
            name = m.group(3)
            if m.group(2) == 'instance' and (name.startswith('[') or name.startswith(':')): continue
            ns = '.'.join(n for k, n in stack if k == 'ns')
            full = name[len('_root_.'):] if name.startswith('_root_.') else (ns + '.' + name if ns else name)
            idx.append(dict(file=rel, line=ln, full=full, short=full.split('.')[-1], private='private' in (m.group(1) or ''), kind=m.group(2)))
json.dump(idx, open('fullnames.json', 'w'))
print(len(idx))
