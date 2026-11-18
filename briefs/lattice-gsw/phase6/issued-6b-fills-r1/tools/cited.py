"""cited.py <repo> <rev> <mathlibdir> <file>...: every backticked Lean-name-like token in the docstrings of the
given files at <rev>, resolved against (1) TCSlib declarations at <rev> (full names via namespace tracking; a
cited name resolves if some full name ends with it at a dot boundary), (2) Mathlib/Batteries/core-like names in
<mathlibdir> (declaration keyword followed by the last component, with the qualifier's last segment present as a
namespace or prefix in the same file). Output: token<TAB>status<TAB>where (first hit path:line)."""
import sys, re, subprocess, os
repo, rev, mld, files = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4:]
KW = r'(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)'
ls = subprocess.run(['git','-C',repo,'ls-tree','-r','--name-only',rev,'--','TCSlib'],capture_output=True,text=True).stdout.split()
idx = {}
for p in ls:
    if not p.endswith('.lean'): continue
    t = subprocess.run(['git','-C',repo,'show',f'{rev}:{p}'],capture_output=True,text=True).stdout
    ns = []
    for i,l in enumerate(t.split('\n'),1):
        m = re.match(r'^namespace\s+(\S+)', l)
        if m: ns.append(m.group(1)); continue
        m = re.match(r'^end\s+(\S+)\s*$', l)
        if m and ns and ns[-1]==m.group(1): ns.pop(); continue
        m = re.match(r'^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*'+KW+r'\s+([^\s(:{\[]+)', l)
        if m:
            nm = m.group(1)
            full = nm[7:] if nm.startswith('_root_.') else '.'.join(ns+[nm])
            idx.setdefault(full, f'{p}:{i}')
        m = re.search(r'@\[simps[^\]]*\]', l)
names = list(idx)
def tc(tok):
    for f in names:
        if f == tok or f.endswith('.'+tok): return idx[f]
    return None
mlcache = {}
def ml(tok):
    last = tok.split('.')[-1]
    if last in mlcache: hits = mlcache[last]
    else:
        r = subprocess.run(['grep','-rnE','--include=*.lean',r'^\s*(@\[[^]]*\]\s*)?((private|protected|noncomputable|nonrec)\s+)*'+KW+r'\s+([A-Za-z_.]*\.)?'+re.escape(last)+r'\b',
                            mld],capture_output=True,text=True).stdout.splitlines()
        mlcache[last] = hits = r
    q = tok.split('.')[:-1]
    for h in hits:
        if not q: return h.split(':')[0].replace(mld+'/','')+':'+h.split(':')[1]
        path = h.split(':')[0]
        if q[-1] in h or q[-1] in open(path,errors='ignore').read(): return path.replace(mld+'/','')+':'+h.split(':')[1]
    return None
seen = {}
for p in files:
    t = subprocess.run(['git','-C',repo,'show',f'{rev}:{p}'],capture_output=True,text=True).stdout
    for d in re.findall(r'/--(.*?)-/', t, flags=re.S):
        for tok in re.findall(r'`([^`\s]+)`', d):
            if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.₀-₉]*", tok) or tok.count('.')>4: continue
            if tok in seen: continue
            w = tc(tok)
            seen[tok] = ('TCSlib', w) if w else (('Mathlib/core', ml(tok)) if ml(tok) else ('UNRESOLVED', '-'))
for tok,(s,w) in sorted(seen.items(), key=lambda x:(x[1][0],x[0])):
    print(f'{tok}\t{s}\t{w}')
