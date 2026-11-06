"""Drift attestation between two commits for the quantum-phase1 files: strip comments, split into
declarations, and compare each declaration's signature (text up to its top-level `:=`, or the whole
declaration for structures) by name. Prints declarations removed, added, and changed.
Usage: python3 -I drift.py <old-commit> <new-commit>"""
import re, subprocess, sys
FILES = ["TCSlib/Quantum/Basic/Register.lean", "TCSlib/Quantum/Basic/Gates.lean",
         "TCSlib/Quantum/Basic/ApplyOn.lean", "TCSlib/Quantum/Basic/Measure.lean",
         "TCSlib/Quantum/Basic/Protocols.lean", "TCSlib/Complexity/Promise/Basic.lean",
         "TCSlib/Complexity/Counting/PP.lean", "TCSlib/Complexity/Counting/GapP.lean",
         "TCSlib/Complexity/Counting/PolyTime.lean", "TCSlib/Complexity/Counting/Inclusions.lean"]
KW = r'(?:theorem|lemma|def|abbrev|structure|instance|inductive|class)'
def strip(s):
    s = re.sub(r'/-.*?-/', '', s, flags=re.S)
    return re.sub(r'--[^\n]*', '', s)
def decls(commit, f):
    src = strip(subprocess.run(['git', 'show', f'{commit}:{f}'], capture_output=True, text=True).stdout)
    out = {}
    parts = re.split(r'(?m)^(?=(?:@\[[^\]]*\]\s*)?(?:noncomputable |private |protected )*' + KW + r'\b)', src)
    for p in parts[1:]:
        m = re.match(r'(?:@\[[^\]]*\]\s*)?(?:noncomputable |private |protected )*(' + KW + r')\s+([^\s(:{\[]*)', p)
        if not m: continue
        kind, name = m.group(1), m.group(2) or '<anonymous instance>'
        body = p.split('\nend ')[0]
        sig = body if kind == 'structure' else body.split(':=')[0]
        out[f'{f}::{name}'] = ' '.join(sig.split())
    return out
old, new = sys.argv[1], sys.argv[2]
A, B = {}, {}
for f in FILES: A.update(decls(old, f)); B.update(decls(new, f))
print(f'old {old}: {len(A)} declarations; new {new}: {len(B)} declarations')
print('REMOVED:'); [print('  ', k) for k in sorted(set(A) - set(B))] or None
print('ADDED:'); [print('  ', k) for k in sorted(set(B) - set(A))]
ch = [k for k in sorted(set(A) & set(B)) if A[k] != B[k]]
print('CHANGED SIGNATURE:'); [print('  ', k, '\n     old:', A[k], '\n     new:', B[k]) for k in ch]
print(f'UNCHANGED: {len(set(A) & set(B)) - len(ch)}')
