"""c10clash.py <repo> <newdecls.tsv> <rev>=<label>...: for every new full name (decls2 output,
column 3), report any declaration of the same full name in TCSlib/ or audits/ at each revision
(decls2's namespace-aware extractor), and every new short name (last component) declared elsewhere
under any namespace."""
import subprocess, sys, os, importlib.util
repo, newf = sys.argv[1], sys.argv[2]
revs = [a.split('=') for a in sys.argv[3:]]
spec = importlib.util.spec_from_file_location('d2', '/home/user/work/tools/decls2_lib.py')
d2 = importlib.util.module_from_spec(spec); spec.loader.exec_module(d2)
new = [l.split('\t')[2] for l in open(newf, encoding='utf-8') if l.startswith('ADDED')]
mine = {'TCSlib/Cryptography/LWE/Efficient.lean', 'TCSlib/Cryptography/SIS/Efficient.lean'}
short = {}
for n in new: short.setdefault(n.split('.')[-1], []).append(n)
for rev, label in revs:
    files = subprocess.run(['git', '-C', repo, 'ls-tree', '-r', '--name-only', rev, '--', 'TCSlib', 'audits'],
                           capture_output=True, text=True).stdout.split()
    files = [f for f in files if f.endswith('.lean') and f not in mine]
    full_hits, short_hits = [], []
    for f in files:
        src = subprocess.run(['git', '-C', repo, 'show', f'{rev}:{f}'], capture_output=True, text=True).stdout
        try: ds = d2.decls(src)
        except Exception as ex: print('PARSE-SKIP', f, ex); continue
        for full in ds:
            if full in new: full_hits.append((full, f))
            s = full.split('.')[-1]
            if s in short: short_hits.append((s, full, f))
    print(f'== {label} {rev}: {len(files)} files; full-name clashes: {len(full_hits)}')
    for h in full_hits: print('CLASH', *h, sep='\t')
    for s in sorted(set(x[0] for x in short_hits)):
        print('SHORT', s, sorted(set(x[1] for x in short_hits if x[0] == s)), sep='\t')
