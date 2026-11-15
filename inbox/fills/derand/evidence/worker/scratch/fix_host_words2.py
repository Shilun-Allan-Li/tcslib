from pathlib import Path
root = Path('/Users/seyoonr/.codex/worktrees/derand-proof/tcslib-exchange')
path = root / 'TCSlib/Complexity/Randomized/SeedMajority/Words.lean'
text = path.read_text().replace('    · rw [hiFin, Equiv.symm_apply_apply]',
'''    · exact (congrArg (Randomized.bitsEquiv m).symm hiFin).trans
        ((Randomized.bitsEquiv m).symm_apply_apply u)''')
path.write_text(text)
