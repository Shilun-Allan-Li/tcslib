"""shadow6b.py <repo> <rev> <closures.txt> <new-names.tsv> (gsw-6b-statements, sub-agent probe; new; check 11 (c)).
For every DOWN module of closures.txt (the modules downstream of a changed module: O2's BitEncoding and the two
facades), at <rev>: (1) its direct imports; (2) whether it imports, directly or through the in-repo import graph
at <rev>, any of the 9 new modules (so which new names are in scope there: O2's names reach every DOWN module
through BitEncoding; the new GSW/Ratio names only through the facades); (3) every identifier token of the file
(comments and strings stripped) that equals a new short name or ends with `.<new short name>`. A token hit is
the only way an unqualified (or namespace-relative) use can change its resolution: Lean resolves an identifier
by its own components, so a module none of whose tokens names a new declaration resolves every identifier as
before. A hit counts only when the new name is in scope in that module.
Also prints whether each facade body has anything besides imports, comments and docstrings."""
import re, subprocess, sys
repo, rev, clos, newf = sys.argv[1:5]
def show(p):
    r = subprocess.run(['git', '-C', repo, 'show', f'{rev}:{p}'], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None
down = [l.split('\t')[2].strip() for l in open(clos) if l.startswith('DOWN\t')]
new = [l.rstrip('\n').split('\t') for l in open(newf) if not l.startswith('#') and l.strip()]
newmods = sorted({m for _, _, m in new if not m.endswith('BitEncoding')})
shorts = {n.split('.')[-1] for n, _, _ in new}
def strip(src):
    src = re.sub(r'/-.*?-/', ' ', src, flags=re.S)          # block and doc comments (non-nested suffices here)
    src = re.sub(r'--[^\n]*', ' ', src)
    src = re.sub(r'"(?:\\.|[^"\\])*"', ' ', src)
    return src
def imports(src): return re.findall(r'^import\s+(\S+)', src or '', flags=re.M)
graph = {}
def closure(mod, seen):
    if mod in seen: return
    seen.add(mod)
    src = show(mod.replace('.', '/') + '.lean')
    if src is None: return
    for i in imports(src):
        if i.startswith('TCSlib'): closure(i, seen)
print(f'# rev {rev}; {len(down)} DOWN modules; new modules: {", ".join(newmods)}')
bad = 0
for d in down:
    mod = d.replace('/', '.')
    src = show(d + '.lean')
    seen = set(); closure(mod, seen)
    reach = sorted(m for m in newmods if m in seen)
    toks = re.findall(r"[A-Za-z_Ͱ-Ͽἀ-῿][\w'.Ͱ-Ͽ₀-ₜ!?]*", strip(src))
    hits = sorted({t for t in toks if t.split('.')[-1] in shorts})
    body = strip(src)
    body = re.sub(r'^\s*(import\s+\S+|set_option\s+\S+\s+\S+)\s*$', '', body, flags=re.M).strip()
    facade = 'facade (imports, set_option, comments only)' if not body else \
        f'code ({len([x for x in body.splitlines() if x.strip()])} lines)'
    o2in = 'TCSlib.Cryptography.LWE.BitEncoding' in seen
    scope = {n.split('.')[-1] for n, _, m in new
             if (m.endswith('BitEncoding') and o2in) or m in reach}
    hits_scope = sorted({t for t in hits if t.split('.')[-1] in scope})
    print(f'{d}\t{facade}\treaches_new={len(reach)}\tO2_in_scope={o2in}\ttoken_hits={hits if hits else "none"}'
          f'\thits_on_names_in_scope={hits_scope if hits_scope else "none"}')
    if reach: print(f'\t\tnew modules in scope: {", ".join(x.split(".")[-1] for x in reach)}')
    if hits_scope and not d.endswith('BitEncoding'): bad += 1
print(f'RESULT down={len(down)} modules_with_hits_on_in_scope_new_names (BitEncoding, the defining file, '
      f'excluded)={bad}')
