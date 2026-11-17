r"""frozen_controls.py <base-Rel> <head-Rel> <base-Sec> <head-Sec> <checker> <outdir> (bb1-sim, Claude lead): mutation
controls of frozen_check.py. Each mutation is a single-occurrence edit of a head file; the checker runs on the
mutated heads against the unchanged bases. Expected: C0 unchanged heads PASS; every other control FAIL with the
named item failing:
  C1 an edit that spills from T2's sketch into its statement prose (H2 bb1_sim_real)
  C2 a one-character change in expect_sample_rel's header (H1)
  C3 an unpermitted import added after the helper imports (H4 Security)
  C4 an edit to bb1_sidSecure's proof (H3)
  C5 a module-docstring change outside the `## Contents` section (H4 Security)
  C6 an edit to prob_simulate_rel's proof (H3)
Prints one line per control and `ALL_CONTROLS_OK True|False` (exit 0/1)."""
import sys, os, subprocess
bR, hR, bS, hS, chk, out = sys.argv[1:7]
R0, S0 = open(hR, encoding='utf-8').read(), open(hS, encoding='utf-8').read()
def rep(s, a, b):
    assert s.count(a) == 1, (a[:60], s.count(a)); return s.replace(a, b)
C = [
 ('C0-unchanged', R0, S0, None),
 ('C1-sketch-spills-into-prose', R0, rep(S0, 'where distinct identities may collide\nin `Z_p`.\n\n**Proof sketch.**',
   'where distinct identities may collide\nin `Z_p`, and more.\n\n**Proof sketch.**'), 'H2 prose bb1_sim_real'),
 ('C2-header-char', rep(R0, '(R : σ → τ → Prop) (e : U ≃ V) (f₀ : U → β × σ) (f₁ : V → β × τ)',
   '(R : σ → τ → Prop) (e : U ≃ V) (f₀ : U → β × σ) (f₁ : V → β × σ)'), S0, 'H1 header expect_sample_rel'),
 ('C3-unpermitted-import', R0, rep(S0, 'import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Chain\n',
   'import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Chain\nimport TCSlib.Cryptography.Games.Hopping\n'),
   'H4 rest of Security'),
 ('C4-bb1_sidSecure-edited', R0, rep(S0, '  have := hc M1T S1\n  linarith', '  have := hc M1T S1\n  nlinarith'),
   'H3 whole bb1_sidSecure'),
 ('C5-docstring-outside-contents', R0, rep(S0, '* `bb1_sidSecure` — [BB04, Theorem 4.1] at depth 1.',
   '* `bb1_sidSecure` — [BB04, Theorem 4.1] at depth one.'), 'H4 rest of Security'),
 ('C6-prob_simulate_rel-edited', rep(R0, '  rw [prob_eq_expect, prob_eq_expect]', '  rw [prob_eq_expect]\n  rw [prob_eq_expect]'),
   S0, 'H3 whole prob_simulate_rel'),
]
allok = True
for name, r, s, item in C:
    d = os.path.join(out, name); os.makedirs(d, exist_ok=True)
    pr, ps = os.path.join(d, 'Relational.lean'), os.path.join(d, 'BonehBoyenSecurity.lean')
    open(pr, 'w', encoding='utf-8').write(r); open(ps, 'w', encoding='utf-8').write(s)
    p = subprocess.run([sys.executable, '-I', chk, bR, pr, bS, ps], capture_output=True, text=True)
    open(os.path.join(d, 'check.out'), 'w').write(p.stdout + p.stderr)
    fails = [l[7:].split(':')[0] for l in p.stdout.splitlines() if l.startswith('[FAIL]')]
    if item is None: ok = p.returncode == 0 and not fails
    else: ok = p.returncode == 1 and item in fails
    allok &= ok
    print(f'{name}: {"OK" if ok else "UNEXPECTED"} | rc={p.returncode} failing={fails}')
print('ALL_CONTROLS_OK', allok); sys.exit(0 if allok else 1)
