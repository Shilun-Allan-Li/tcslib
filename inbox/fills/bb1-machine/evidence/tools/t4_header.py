"""t4_header.py <repo> <rev>... (fill bb1-machine, Claude lead): T4's header (from `theorem
exists_bb1_distinguisher` to `:= by`) and its docstring's statement prose (from `/--` to
`**Proof sketch.**`) at each <rev> and in the working tree, compared byte for byte with the first rev.
touched.py reports T4 as TOUCHED (its body and sketch change, as permitted); this isolates the header."""
import sys, subprocess, hashlib
repo, revs = sys.argv[1], sys.argv[2:]
F = 'TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean'
def parts(s):
    t = s.index('theorem exists_bb1_distinguisher'); h = s[t:s.index(':= by\n', t) + 5]
    d = s.rfind('/--', 0, t); p = s[d:s.index('**Proof sketch.**', d)]
    return h, p
srcs = [(r, subprocess.run(['git', '-C', repo, 'show', f'{r}:{F}'], capture_output=True, text=True,
         check=True).stdout) for r in revs] + [('worktree', open(f'{repo}/{F}', encoding='utf-8').read())]
h0, p0 = parts(srcs[0][1]); ok = True
for r, s in srcs:
    h, p = parts(s); e = (h == h0, p == p0); ok &= all(e)
    print(r, 'header', hashlib.sha256(h.encode()).hexdigest()[:16], 'UNCHANGED' if e[0] else 'CHANGED',
          '| prose', hashlib.sha256(p.encode()).hexdigest()[:16], 'UNCHANGED' if e[1] else 'CHANGED')
print('T4 header and statement prose', 'UNCHANGED' if ok else 'CHANGED')
sys.exit(0 if ok else 1)
