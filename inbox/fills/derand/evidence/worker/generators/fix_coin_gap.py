from pathlib import Path
root = Path('/Users/seyoonr/.codex/worktrees/derand-proof/tcslib-exchange')
path = root / 'TCSlib/Cryptography/Randomness/Derandomization/CoinGap.lean'
text = path.read_text().replace('    rw [← randProb_eq_uprob]\n',
'''    rw [← randProb_eq_uprob (G.stretch.eval (ceilRoot d x.length))
      (fun r => M' x r = true)]
''')
path.write_text(text)
