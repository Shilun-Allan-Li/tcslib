from pathlib import Path
root = Path('/Users/seyoonr/.codex/worktrees/derand-proof/tcslib-exchange')
path = root / 'TCSlib/Cryptography/Randomness/Derandomization/RootSchedule.lean'
text = path.read_text().replace('    rw [ceilRoot_zero]\n    positivity',
'''    rw [ceilRoot_zero]
    simpa only [Nat.cast_zero] using
      add_nonneg (Real.rpow_nonneg (show (0 : ℝ) ≤ 0 from le_rfl) (1 / (d : ℝ)))
        zero_le_one''')
path.write_text(text)
