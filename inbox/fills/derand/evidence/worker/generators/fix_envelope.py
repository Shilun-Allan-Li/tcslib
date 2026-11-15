from pathlib import Path
root = Path('/Users/seyoonr/.codex/worktrees/derand-proof/tcslib-exchange')
path = root / 'TCSlib/Complexity/Randomized/SeedMajority/Envelope.lean'
text = path.read_text().replace('    exact abs_le.mpr ⟨by omega, by omega⟩',
                               '    rw [MultiTapeTM.initCfg_eq]\n    exact abs_le.mpr ⟨by omega, by omega⟩')
path.write_text(text)
