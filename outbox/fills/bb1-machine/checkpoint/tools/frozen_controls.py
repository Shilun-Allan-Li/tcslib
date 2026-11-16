"""frozen_controls.py <base-file> <head-file> <checker> <outdir> (fill-pair-bdh): mutation controls for frozen_check.py.
Each control applies one single-occurrence edit to the head file and must make the checker FAIL; the unmutated head must PASS."""
import sys, subprocess, os
base, head, chk, out = sys.argv[1:5]; os.makedirs(out, exist_ok=True)
H = open(head, encoding='utf-8').read()
C = [('C1-T1-header', '(hN : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.OrderAtLeastExcept (fun κ => 2 ^ κ) δ)',
      '(hN : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.OrderAtLeastExcept (fun κ => 2 ^ (κ + 1)) δ)'),
     ('C2-other-docstring', '`|Pr[D(P_BDH) = 1] − Pr[D(R_BDH) = 1]|`', '`|Pr[D(P_BDH) = 0] − Pr[D(R_BDH) = 1]|`'),
     ('C3-public-helper', 'private theorem prob_eq_encT_le', 'theorem prob_eq_encT_le'),
     ('C4-T1-prose', '/-- **Decision BDH implies BDH** when the group order', '/-- **Decision BDH implies BDH** whenever the group order'),
     ('C5-extra-import', 'import TCSlib.Cryptography.OneWayFunctions.Basic\n',
      'import TCSlib.Cryptography.OneWayFunctions.Basic\nimport TCSlib.Cryptography.Foundations.Experiments\n'),
     ('C6-other-body', 'theorem bdhAssumption_iff :\n    G.BDHAssumption ↔ ∀ A : NUPPT, Negligible fun κ => accept (G.bdhGame A κ) := Iff.rfl',
      'theorem bdhAssumption_iff :\n    G.BDHAssumption ↔ ∀ A : NUPPT, Negligible fun κ => accept (G.bdhGame A κ) := by rfl')]
ok = True
r = subprocess.run(['python3', '-I', chk, base, head], capture_output=True, text=True)
print('HEAD', 'PASS' if r.returncode == 0 else 'FAIL', '|', r.stdout.strip().splitlines()[0][:160]); ok &= r.returncode == 0
for name, a, b in C:
    assert H.count(a) == 1, (name, H.count(a))
    p = os.path.join(out, name + '.lean'); open(p, 'w', encoding='utf-8').write(H.replace(a, b))
    r = subprocess.run(['python3', '-I', chk, base, p], capture_output=True, text=True)
    res = 'FAIL(expected)' if r.returncode != 0 else 'PASS(UNEXPECTED)'; ok &= r.returncode != 0
    print(name, res, '|', (r.stdout.strip() or r.stderr.strip()).splitlines()[-1][:160])
print('ALL_CONTROLS_OK', ok)
