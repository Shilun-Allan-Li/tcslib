from pathlib import Path
root = Path('/Users/seyoonr/.codex/worktrees/derand-proof/tcslib-exchange')
path = root / 'TCSlib/Complexity/Randomized/SeedMajority/State.lean'
text = path.read_text()
for equation in ['advance_eq', 'finished_eq', 'payload_eq']:
    text = text.replace('  funext z\n  simp only [' + equation + ', Function.comp_apply]\n', '')
text = text.replace('  by_cases h : pairEncode x (word (w x.length) i) ∈ V <;> simp [h]',
'''  by_cases h : pairEncode x (word (w x.length) i) ∈ V
  · simp only [if_pos h, ↓reduceIte, BinArith.add_pairEncode]
  · simp only [if_neg h, ↓reduceIte, BinArith.add_pairEncode, Nat.add_zero]''')
path.write_text(text)
