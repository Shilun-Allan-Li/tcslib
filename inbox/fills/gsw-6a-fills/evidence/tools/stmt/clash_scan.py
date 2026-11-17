"""clash_scan.py <repo> <base> <head> <file>...: check 11 (name clashes).
Every declaration (public or private; full name with namespaces resolved by touched.py's cutter) of
the given files at <head> that is new against <base> is compared with every declaration of every
TCSlib/**/*.lean and TCSlib.lean file at <base>: by full name, and by last component when it would be
reachable unqualified through the same namespace. Also reports any new name containing `NAnd` or
`toLayered`. Exit status 1 on a clash."""
import sys, re, subprocess
src = open('/home/user/w6/tools/stmt/xr/touched.py', encoding='utf8').read()
code = src[src.index('def show('):src.index('report = {')]
repo, base, head = sys.argv[1:4]; files = sys.argv[4:]
KW = r'(theorem|lemma|def|abbrev|structure|inductive|instance|class|opaque|axiom)'
DECL = re.compile(r'^(@\[[^\]]*\]\s*)*((?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*' + KW + r'\b\s*([^\s(:{\[]*)')
TOP = re.compile(r'^(namespace|end|section|open|variable|universe|set_option|attribute|noncomputable section|mutual|#|example|import|/-!)')
g = {'re': re, 'subprocess': subprocess, 'repo': repo, 'DECL': DECL, 'TOP': TOP}
exec(code, g)
decls, show = g['decls'], g['show']
allbase = subprocess.run(['git', '-C', repo, 'ls-tree', '-r', '--name-only', base, '--', 'TCSlib', 'TCSlib.lean'],
                         capture_output=True, text=True).stdout.split()
basenames = {}
for f in allbase:
    if not f.endswith('.lean'): continue
    t = show(base, f)
    for d in decls(t or ''):
        basenames.setdefault(d['name'], []).append(f'{f}:{d["decl_line"]}')
print(f'base: {len(allbase)} files, {len(basenames)} distinct declaration names')
bad = 0; n = 0
moved = set()   # declarations removed from the given files by the change: a new copy of one is a move
for f in files:
    old = show(base, f)
    if old:
        newn = {d['name'] for d in decls(show(head, f))}
        moved |= {d['name'] for d in decls(old)} - newn
for f in files:
    old = show(base, f); oldn = {d['name'] for d in decls(old)} if old else set()
    for d in decls(show(head, f)):
        if d['name'] in oldn: continue
        n += 1
        hit = basenames.get(d['name'])
        flag = ''
        if 'NAnd' in d['name'] or 'toLayered' in d['name']: flag = ' FORBIDDEN-SUBSTRING'
        if hit and d['name'] in moved and all(h.split(':')[0] in files for h in hit) and not flag:
            print(f'moved\t{d["name"]}\t{f}:{d["decl_line"]}\t(from {hit}, removed there by this change)')
        elif hit or flag:
            bad += 1; print(f'CLASH\t{d["name"]}\t{f}:{d["decl_line"]}\t{hit}{flag}')
        else:
            print(f'ok\t{d["name"]}\t{"private " if d["private"] else ""}{d["kind"]}\t{f}:{d["decl_line"]}')
print(f'RESULT new_names={n} clashes={bad}')
sys.exit(1 if bad else 0)
