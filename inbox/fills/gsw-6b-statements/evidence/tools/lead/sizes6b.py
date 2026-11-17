"""sizes6b.py <repo> <rev>... (gsw-6b-statements, new): lines and maximum width (Python len of each
line, i.e. characters) of every new or changed Lean file at each revision, with r3 §H7's fill
estimates per unit (the projected size is lines + the upper fill estimate; must stay < 1000)."""
import sys, subprocess
repo, revs = sys.argv[1], sys.argv[2:]
G = 'TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW'
EST = {f'{G}/Branching.lean': ('U12', 150, 250), f'{G}/DecryptFormula.lean': ('U13', 200, 330),
       f'{G}/Bootstrap.lean': ('U14', 280, 440), f'{G}/Circular.lean': ('U15', 60, 120),
       f'{G}/Leveled.lean': ('U16', 180, 300), f'{G}/LeveledSecurity.lean': ('U17', 230, 370),
       f'{G}/PolyRatio.lean': ('U18', 140, 220), 'TCSlib/Cryptography/LWE/Ratio.lean': ('U18', 0, 0),
       f'{G}/Asymptotic.lean': ('U19', 150, 280), 'TCSlib/Cryptography/LWE/BitEncoding.lean': ('O2', 0, 0),
       f'{G}.lean': ('facade', 0, 0), 'TCSlib/Cryptography/LWE.lean': ('facade', 0, 0)}
base = '3e51b5f28900db6190f1eb2e6d207d27ee15d541'
for rev in revs:
    files = subprocess.run(['git', '-C', repo, 'diff', '--name-only', base, rev, '--', '*.lean'],
                           capture_output=True, text=True, check=True).stdout.split()
    print(f'== {rev}')
    print('file\tunit\tlines\tmax_width\tover100\tfill_est\tprojected_max\tok')
    for f in files:
        t = subprocess.run(['git', '-C', repo, 'show', f'{rev}:{f}'], capture_output=True, check=True).stdout.decode('utf-8')
        L = t.split('\n')
        if L and L[-1] == '': L = L[:-1]
        w = max((len(l) for l in L), default=0); over = sum(len(l) > 100 for l in L)
        u, lo, hi = EST.get(f, ('?', 0, 0))
        print(f'{f}\t{u}\t{len(L)}\t{w}\t{over}\t{lo}-{hi}\t{len(L) + hi}\t{"OK" if w <= 100 and len(L) + hi < 1000 else "CHECK"}')
