from pathlib import Path
root = Path('/Users/seyoonr/.codex/worktrees/derand-proof/tcslib-exchange')
path = root / 'TCSlib/Cryptography/Randomness/Derandomization/Majority.lean'
text = path.read_text().replace('  rw [← Randomized.half_lt_randProb_iff]',
'''  rw [← Randomized.half_lt_randProb_iff (w x.length) (fun u => pairEncode x u ∈ V)]''')
path.write_text(text)
