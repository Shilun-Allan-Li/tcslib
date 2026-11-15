from pathlib import Path
root = Path('/Users/seyoonr/.codex/worktrees/derand-proof/tcslib-exchange')
path = root / 'TCSlib/Cryptography/Randomness/Derandomization/Majority.lean'
text = path.read_text().replace('''  have hp := Randomized.randProb_congr
    (m := w x.length) (fun u => hVeq x (List.ofFn u))''',
'''  have hp := Randomized.randProb_congr (m := w x.length)
    (A := fun u => M' x u = true) (B := fun u => pairEncode x u ∈ V)
    (fun u => hVeq x (List.ofFn u))''')
path.write_text(text)
