"""Drift attestation between two commits for the quantum-phase1 files: strip comments, split into
declarations, and compare each declaration by name twice: its signature (text up to its top-level
`:=`, or the whole declaration for structures) and its full comment-stripped body, so that a
changed definition body or proof is reported too (round-2 audit, answer 3). Whitespace is
normalized. Prints declarations removed, added, and changed.
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
        out[f'{f}::{name}'] = (' '.join(sig.split()), ' '.join(body.split()))
    return out
old, new = sys.argv[1], sys.argv[2]
A, B = {}, {}
for f in FILES: A.update(decls(old, f)); B.update(decls(new, f))
print(f'old {old}: {len(A)} declarations; new {new}: {len(B)} declarations')
print('REMOVED:'); [print('  ', k) for k in sorted(set(A) - set(B))] or None
print('ADDED:'); [print('  ', k) for k in sorted(set(B) - set(A))]
common = sorted(set(A) & set(B))
sig = [k for k in common if A[k][0] != B[k][0]]
body = [k for k in common if A[k][0] == B[k][0] and A[k][1] != B[k][1]]
print('CHANGED SIGNATURE:'); [print('  ', k, '\n     old:', A[k][0], '\n     new:', B[k][0]) for k in sig]
print('CHANGED BODY ONLY (same signature):'); [print('  ', k) for k in body]
print(f'UNCHANGED (signature and body): {len(common) - len(sig) - len(body)}')
