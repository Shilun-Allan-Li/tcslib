"""frozen_controls_bb1m.py <base-file> <head-file> <checker> <outdir> (fill-bb1-machine): frozen_controls.py's harness with
mutations of BonehBoyenMachine.lean. Each control applies one single-occurrence edit to the head file and must make the
checker FAIL; the unmutated head must PASS."""
import sys, subprocess, os
base, head, chk, out = sys.argv[1:5]; os.makedirs(out, exist_ok=True)
H = open(head, encoding='utf-8').read()
C = [('C1-T4-header', '(q : PolyExpr) :\n    ∃ D : Bool → NUPPT', '(q : PolyExpr) (hq : 0 < q.eval 0) :\n    ∃ D : Bool → NUPPT'),
     ('C2-T4-statement', '≤ σ κ := by', '< σ κ := by'),
     ('C3-T4-prose', 'negligible `σ` with', 'negligible `σ` such that'),
     ('C4-module-doc', 'This step is its own module so that', 'This step is a module of its own so that'),
     ('C5-foreign-import', 'import TCSlib.Cryptography.Pairing.Operations\n',
      'import TCSlib.Cryptography.Pairing.Operations\nimport TCSlib.Cryptography.Games.Hopping\n'),
     ('C6-helper-import-misplaced', 'import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine.Words\n',
      'import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine.Words2\n'),
     ('C7-added-decl', '\nend TCSlib.Cryptography.AdvancedEncryption.IdentityBased\n',
      '\ntheorem extra : True := trivial\n\nend TCSlib.Cryptography.AdvancedEncryption.IdentityBased\n'),
     ('C8-main-results', '* `exists_bb1_distinguisher` — the simulation', '* `exists_bb1_distinguisher` — this simulation')]
ok = True
r = subprocess.run(['python3', '-I', chk, base, head], capture_output=True, text=True)
print('HEAD', 'PASS' if r.returncode == 0 else 'FAIL', '|', r.stdout.strip().splitlines()[0][:200]); ok &= r.returncode == 0
for name, a, b in C:
    assert H.count(a) == 1, (name, H.count(a))
    p = os.path.join(out, name + '.lean'); open(p, 'w', encoding='utf-8').write(H.replace(a, b))
    r = subprocess.run(['python3', '-I', chk, base, p], capture_output=True, text=True)
    res = 'FAIL(expected)' if r.returncode != 0 else 'PASS(UNEXPECTED)'; ok &= r.returncode != 0
    print(name, res, '|', (r.stdout.strip() or r.stderr.strip()).splitlines()[-1][:200])
print('ALL_CONTROLS_OK', ok)
