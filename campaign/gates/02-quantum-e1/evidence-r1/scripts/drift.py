"""Drift attestation between two commits for the quantum-phase1 files, revised after the E1 epoch
audit (finding 7). Comments are stripped and whitespace normalized, then each file is split into
commands. Three checks:

1. Named declarations, compared by name: signature (text up to the top-level `:=`, or the whole
   declaration for structures) and full body.
2. Order: for each file, the sequence of declarations present at both commits must be the same.
3. Anonymous commands (`example`, unnamed `instance`) are command boundaries, so they are never
   absorbed into the preceding declaration's body, and are inventoried separately per file.

Usage: python3 -I drift.py <old-commit> <new-commit>"""
import re, subprocess, sys
FILES = ["TCSlib/Quantum/Basic/Register.lean", "TCSlib/Quantum/Basic/Gates.lean",
         "TCSlib/Quantum/Basic/ApplyOn.lean", "TCSlib/Quantum/Basic/Measure.lean",
         "TCSlib/Quantum/Basic/Protocols.lean", "TCSlib/Complexity/Promise/Basic.lean",
         "TCSlib/Complexity/Counting/PP.lean", "TCSlib/Complexity/Counting/GapP.lean",
         "TCSlib/Complexity/Counting/PolyTime.lean", "TCSlib/Complexity/Counting/Inclusions.lean"]
KW = r'(?:theorem|lemma|def|abbrev|structure|instance|inductive|class|example)'
MOD = r'(?:@\[[^\]]*\]\s*)?(?:noncomputable |private |protected )*'
def strip(s):
    s = re.sub(r'/-.*?-/', '', s, flags=re.S)
    return re.sub(r'--[^\n]*', '', s)
def commands(commit, f):
    """Ordered list of (key, signature, body) for named declarations, and of anonymous commands."""
    src = strip(subprocess.run(['git', 'show', f'{commit}:{f}'], capture_output=True,
                               text=True).stdout)
    named, anon = [], []
    for p in re.split(r'(?m)^(?=' + MOD + KW + r'\b)', src)[1:]:
        m = re.match(MOD + r'(' + KW + r')\b\s*([^\s(:{\[]*)', p)
        if not m: continue
        kind, name = m.group(1), m.group(2)
        body = re.split(r'(?m)^(?:end |namespace |section |open |variable )', p)[0]
        norm = ' '.join(body.split())
        if kind == 'example' or (kind == 'instance' and not name):
            anon.append(norm)
            continue
        sig = norm if kind == 'structure' else ' '.join(body.split(':=')[0].split())
        named.append((f'{f}::{name}', sig, norm))
    return named, anon
old, new = sys.argv[1], sys.argv[2]
A, B, order_bad, anon = {}, {}, [], {}
for f in FILES:
    na, aa = commands(old, f); nb, ab = commands(new, f)
    A.update({k: (s, b) for k, s, b in na}); B.update({k: (s, b) for k, s, b in nb})
    ka = [k for k, _, _ in na if k in {k2 for k2, _, _ in nb}]
    kb = [k for k, _, _ in nb if k in {k2 for k2, _, _ in na}]
    if ka != kb: order_bad.append(f)
    if aa or ab: anon[f] = (aa, ab)
print(f'old {old}: {len(A)} named declarations; new {new}: {len(B)} named declarations')
print('REMOVED:'); [print('  ', k) for k in sorted(set(A) - set(B))]
print('ADDED:'); [print('  ', k) for k in sorted(set(B) - set(A))]
common = sorted(set(A) & set(B))
sig = [k for k in common if A[k][0] != B[k][0]]
body = [k for k in common if A[k][0] == B[k][0] and A[k][1] != B[k][1]]
print('CHANGED SIGNATURE:')
for k in sig: print('  ', k, '\n     old:', A[k][0], '\n     new:', B[k][0])
print('CHANGED BODY ONLY (same signature):'); [print('  ', k) for k in body]
print(f'UNCHANGED (signature and body): {len(common) - len(sig) - len(body)}')
print('ORDER of carried-over declarations:',
      'same in every file' if not order_bad else 'DIFFERS in ' + ', '.join(order_bad))
print('ANONYMOUS COMMANDS (example, unnamed instance), old -> new:')
for f in FILES:
    aa, ab = anon.get(f, ([], []))
    print(f'   {f}: {len(aa)} -> {len(ab)}')
    for t in ab: print('      new:', t[:160])
    for t in aa:
        if t not in ab: print('      removed:', t[:160])
