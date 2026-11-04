"""namescan.py <root> <changed-files list>: static full-name scan of public declarations. Tracks
namespace/section/end; reports a full name declared in two files where at least one is in the
changed list (python3 -I)."""
import sys, re, os
root, chg = sys.argv[1:3]
changed = set(l.strip() for l in open(chg) if l.strip())
decl = re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+|protected\s+|nonrec\s+|unsafe\s+|partial\s+)*'
                  r'(theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom)\s+([^\s:({\[]+)')
names = {}
for dp, dn, fn in os.walk(os.path.join(root, 'TCSlib')):
    for f in fn:
        if not f.endswith('.lean'): continue
        p = os.path.relpath(os.path.join(dp, f), root)
        stack = []
        s = open(os.path.join(root, p), encoding='utf-8').read()
        s = re.sub(r'/-.*?-/', '', s, flags=re.S)
        for line in s.split('\n'):
            m = re.match(r'^namespace\s+(\S+)', line)
            if m: stack.append(('ns', m.group(1))); continue
            m = re.match(r'^(?:noncomputable\s+)?section\b\s*(\S*)', line)
            if m: stack.append(('sec', m.group(1))); continue
            if re.match(r'^end\b', line):
                if stack: stack.pop()
                continue
            if line.startswith('private ') or line.startswith('@[') and 'private' in line.split(']')[-1][:12]: continue
            m = decl.match(line)
            if not m or m.group(1) == 'instance': continue
            n = m.group(2)
            if n.startswith('_root_.'): full = n[7:]
            else:
                ns = '.'.join(x[1] for x in stack if x[0] == 'ns')
                full = (ns + '.' + n) if ns else n
            names.setdefault(full, set()).add(p)
hits = [(n, sorted(fs)) for n, fs in names.items() if len(fs) > 1 and any(f in changed for f in fs)]
for n, fs in sorted(hits): print(n, '|', ' '.join(fs))
print(f'# names {len(names)}, clashes touching changed files: {len(hits)}', file=sys.stderr)
