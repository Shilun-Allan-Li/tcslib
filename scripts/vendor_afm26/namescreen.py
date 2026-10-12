import os, re, sys
# usage: namescreen.py <repo root> <out dir>
# Comment-aware, namespace-qualified public declaration names of TCSlib/Programs/ against those of every
# other TCSlib file outside TCSlib/Complexity/ (the Complexity library is covered exactly by the joint
# elaboration of the shipped files with all fifteen Complexity facades). Writes both inventories and the
# intersection; standard library only, starts no process.
root, out = sys.argv[1], sys.argv[2]
KW = r'(theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom)'
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)*((?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*' + KW +
                  r'\s+([^\s(:{\[]+)')

def strip_comments(src):
    out, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith('/-', i):
            depth += 1; i += 2; continue
        if src.startswith('-/', i) and depth > 0:
            depth -= 1; i += 2; continue
        if depth == 0:
            out.append(src[i])
        elif src[i] == '\n':
            out.append('\n')
        i += 1
    return '\n'.join(l.split('--')[0] for l in ''.join(out).split('\n'))

def names(path):
    ns, res = [], []
    for l in strip_comments(open(path, encoding='utf-8').read()).split('\n'):
        m = re.match(r'^namespace\s+(\S+)', l)
        if m: ns.append(m.group(1)); continue
        m = re.match(r'^end\s+(\S+)\s*$', l)
        if m and ns and ns[-1] == m.group(1): ns.pop(); continue
        m = DECL.match(l)
        if m and 'private' not in (m.group(1) or ''):
            n = m.group(3)
            if m.group(2) == 'instance' and (n.startswith('[') or n.startswith(':')): continue
            res.append(n[7:] if n.startswith('_root_.') else '.'.join(ns + [n]))
    return res

def tree(sub, skip):
    for d, _, fs in os.walk(os.path.join(root, sub)):
        rel = os.path.relpath(d, root)
        if any(rel == s or rel.startswith(s + os.sep) for s in skip): continue
        for f in fs:
            if f.endswith('.lean'): yield os.path.join(d, f)

prog = sorted({n for p in tree('TCSlib/Programs', []) for n in names(p)} |
              set(names(os.path.join(root, 'TCSlib/Programs.lean'))))
others = sorted({n for p in tree('TCSlib', ['TCSlib/Complexity', 'TCSlib/Programs']) for n in names(p)})
common = sorted(set(prog) & set(others))
os.makedirs(out, exist_ok=True)
open(os.path.join(out, 'names-programs.txt'), 'w').write('\n'.join(prog) + '\n')
open(os.path.join(out, 'names-others.txt'), 'w').write('\n'.join(others) + '\n')
print(f'Programs public names (comment-aware, namespace-qualified): {len(prog)}')
print(f'other TCSlib public names outside Complexity and Programs: {len(others)}')
print(f'intersection: {len(common)}' + (': ' + ', '.join(common) if common else ''))
