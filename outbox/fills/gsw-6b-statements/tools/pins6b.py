"""pins6b.py (gsw-6b-statements staging, issued-6b-r1): where the TCSlib names that plan section r3's 6b sections
(§H2 hooks, §H3.1-H3.2, §H3.7-H3.8, §H3.11-H3.12, §H5.9-H5.16, §H6) cite are declared at the base, from git objects
only.  r3's own line numbers are at the 6a issue base f6f295a6 and many have moved (phase-5 fills merged since).
Usage: pins6b.py <repo> <rev> <namesfile>.  Each names line is `<group> <name>`; `<name>` may carry namespace
prefixes (`Encrypts.mul`, `LWE.Family`).  Output per name: every `theorem/lemma/def/abbrev/structure/class/
instance/inductive` header under TCSlib/ whose full name (namespaces resolved from `namespace`/`end` lines, the
leading `_root_.` dropped) is the name or ends with `.` followed by it, as `path:line`, or NOT FOUND.  Several hits mean several declarations with that suffix; the worker resolves them (brief, check 11)."""
import re, subprocess, sys
repo, rev, nf = sys.argv[1:4]
ls = subprocess.run(['git', '-C', repo, 'ls-tree', '-r', '--name-only', rev, '--', 'TCSlib'], capture_output=True,
                    text=True, check=True).stdout.split()
files = [f for f in ls if f.endswith('.lean')]
p = subprocess.Popen(['git', '-C', repo, 'cat-file', '--batch'], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
decls = []
H = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*'
               r'(?:theorem|lemma|def|abbrev|structure|class|instance|inductive)\s+([^\s(:{\[]+)')
for f in files:
    p.stdin.write(f'{rev}:{f}\n'.encode()); p.stdin.flush()
    hdr = p.stdout.readline().split(); n = int(hdr[2]); data = p.stdout.read(n); p.stdout.read(1)
    ns = []
    for i, l in enumerate(data.decode('utf-8').split('\n'), 1):
        m = re.match(r'^namespace\s+(\S+)', l)
        if m: ns.append(m.group(1)); continue
        m = re.match(r'^end\s+(\S+)\s*$', l)
        if m and ns and ns[-1] == m.group(1): ns.pop(); continue
        m = H.match(l)
        if m:
            d = m.group(1)
            full = d.removeprefix('_root_.') if d.startswith('_root_.') else '.'.join(ns + [d])
            decls.append((full, f, i, l.startswith('private')))
p.stdin.close(); p.wait()
for line in open(nf):
    line = line.strip()
    if not line or line.startswith('#'): continue
    grp, name = line.split()
    hits = [f'{f}:{i}' + (' (private)' if pr else '') for d, f, i, pr in decls
            if d == name or d.endswith('.' + name)]
    print(f'{grp}\t{name}\t{" ".join(hits) if hits else "NOT FOUND"}')
