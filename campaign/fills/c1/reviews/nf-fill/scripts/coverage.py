"""Coverage of the direct externals (the audit walk) by the import probes' #check names (python3 -I).
usage: python3 -I coverage.py <audit .out> <brief probe> <worker probe>"""
import re, sys
T = open(sys.argv[1], encoding='utf-8').read().split('\n')
def section(head):
    i = next(k for k, l in enumerate(T) if l.startswith(head))
    out = []
    for l in T[i + 1:]:
        m = re.match(r'^(\S+) \| ', l)
        if not m: break
        out.append(m.group(1))
    return out
tcs = section('DIRECT-TCSLIB'); core = section('DIRECT-CORE/MATHLIB')
def checks(p):
    s = set()
    for l in open(p, encoding='utf-8'):
        m = re.match(r'#check\s+@?(\S+)', l.strip())
        if m: s.add(m.group(1).lstrip('@').lstrip('_root_.'))
    return s
B = checks(sys.argv[2]); W = checks(sys.argv[3])
def norm(n): return n[len('Turing.'):] if n.startswith('Turing.') else n
def covered(n, S): return n in S or norm(n) in S or ('Turing.' + n) in S
aux = lambda n: bool(re.search(r'\._proof_|\.match_|\._simp_|\._unary|\._sunfold|\.eq_\d|\._eq_', n))
print('direct TCSlib externals', len(tcs), '; core/Mathlib', len(core))
print('TCSlib not covered by the brief probe (149 checks):', [n for n in tcs if not covered(n, B)])
print('TCSlib not covered by the worker probe:', [n for n in tcs if not covered(n, W)])
nc = [n for n in core if not covered(n, W) and not aux(n)]
print('core/Mathlib (non-auxiliary) not covered by the worker probe:', len(nc), nc[:40])
