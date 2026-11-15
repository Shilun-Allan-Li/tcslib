from pathlib import Path
root = Path('/Users/seyoonr/.codex/worktrees/derand-proof/tcslib-exchange')
path = root / 'TCSlib/Cryptography/Randomness/Derandomization/TimeBound.lean'
text = path.read_text().replace('''    exact (hsmall.trans (by dsimp only [C]; omega)).trans
      (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left C hb)''',
'''    have hsmallC : f n ≤ C := by
      dsimp only [C]
      omega
    exact hsmallC.trans
      (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left C hb)''')
path.write_text(text)
