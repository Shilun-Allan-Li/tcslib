from pathlib import Path
root = Path('/Users/seyoonr/.codex/worktrees/derand-proof/tcslib-exchange')
path = root / 'TCSlib/Cryptography/Randomness/Derandomization/RootSchedule.lean'
text = path.read_text().replace('''[PS10, §8.2, Theorem 180.1] -/
theorem ceilRoot_le_real''',
'''[PS10, §8.2, Theorem 180.1]

**Proof sketch.** Handle zero separately. At a positive input the floor root
of `n-1` has `d`th power at most `n`. Cast this bound to the reals, apply
the monotonic inverse-power comparison, and add one on both sides. -/
theorem ceilRoot_le_real''')
text = text.replace('* `TCSlib.Cryptography.Randomness.Derand.ceilRoot_le_iff`: its least-root property.',
'''* `TCSlib.Cryptography.Randomness.Derand.ceilRoot_le_iff`: its least-root property.
* `TCSlib.Cryptography.Randomness.Derand.ceilRoot_le_real`: the real-root upper bound.
* `TCSlib.Cryptography.Randomness.Derand.polyTimeComputable_ceilRoot`: its FP unary word.''')
path.write_text(text)
path = root / 'TCSlib/Cryptography/Randomness/Derandomization/AdviceGap.lean'
text = path.read_text().replace('''[PS10, §8.2, Theorem 180.1] -/
theorem eff_mapCoins''',
'''[PS10, §8.2, Theorem 180.1]

**Proof sketch.** Extract the verifier's two `P` languages with the published
efficiency reader. Take their preimages under `z ↦ ⟨fst z,C z⟩`, which is FP
by pairing. The Boolean-verifier and pair-projection readers identify the
resulting true and false events on every encoded pair. -/
theorem eff_mapCoins''')
path.write_text(text)
