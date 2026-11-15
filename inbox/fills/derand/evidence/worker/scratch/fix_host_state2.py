from pathlib import Path
root = Path('/Users/seyoonr/.codex/worktrees/derand-proof/tcslib-exchange')
path = root / 'TCSlib/Complexity/Randomized/SeedMajority/State.lean'
text = path.read_text().replace('if_neg h, ↓reduceIte, BinArith.add_pairEncode, Nat.add_zero',
                               'if_neg h, Bool.false_eq_true, ↓reduceIte, BinArith.add_pairEncode, Nat.add_zero')
path.write_text(text)
