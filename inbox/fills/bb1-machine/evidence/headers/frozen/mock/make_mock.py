"""make_mock.py <issue-base-BonehBoyenMachine.lean> <out-mock.lean>

Builds a MOCK head of BonehBoyenMachine.lean for developing the adapted frozen check (fill
bb1-machine). THIS IS A MOCK, NOT THE FILL'S FILE: it is never checked by Lean. From the issue-base
(7c0a55e0) file it
  - adds the Oracles import between the `.Handler` and `.Reduction` imports,
  - adds the Oracles `## Contents` bullet right after the `BonehBoyenMachine.Reduction` bullet,
  - replaces T4's `**Proof sketch.**` paragraph by a placeholder paragraph marked MOCK,
  - replaces T4's `sorry` by an indented multi-line placeholder body marked MOCK.
Run as `python3 -I make_mock.py <in> <out>`.

written by tools-agent (sub-agent), fill bb1-machine
"""
import sys

HP = 'import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine.'
RED = ('* `BonehBoyenMachine.Reduction`: the acceptance of the T1 machine and the comparison of the'
       ' drawn\n  with the ideal exponents.\n')
BUL = ('* `BonehBoyenMachine.Oracles`: the simulator\'s oracles as `drawStep` with fresh exponents,'
       ' call by\n  call, and the comparison of the simulation with the machine on one Decision'
       ' BDH tuple.\n')
SKETCH = ('**Proof sketch.** MOCK sketch paragraph (placeholder text, not the fill\'s): the\n'
          'distinguisher runs the simulator with drawn exponents; each draw is close to uniform,\n'
          'and a hybrid over the `q(κ) + 1` draws bounds the difference by `σ(κ)`. ')
BODY = ('  -- MOCK body (placeholder, never elaborated)\n'
        '  obtain ⟨D, hD⟩ := mock_machine G ℓ H O A q\n'
        '  refine ⟨D, fun κ => ((q.eval κ : ℝ) + 1) * (1 / 2) ^ κ, mock_negl q, ?_⟩\n'
        '  intro b real κ\n'
        '  calc _ ≤ _ := hD b real κ\n'
        '    _ ≤ _ := le_rfl\n')


def main(argv):
    with open(argv[1], 'rb') as fh:
        s = fh.read().decode('utf-8')

    def rep(a, b):
        nonlocal s
        assert s.count(a) == 1, a[:60]
        s = s.replace(a, b)
    rep(HP + 'Handler\n', HP + 'Handler\n' + HP + 'Oracles\n')
    rep(RED, RED + BUL)
    ps = s.index('**Proof sketch.**')
    pe = s.index('-/\ntheorem exists_bb1_distinguisher', ps)
    s = s[:ps] + SKETCH + s[pe:]
    rep('≤ σ κ := by\n  sorry\n', '≤ σ κ := by\n' + BODY)
    with open(argv[2], 'wb') as fh:
        fh.write(s.encode('utf-8'))


if __name__ == '__main__':
    main(sys.argv)
