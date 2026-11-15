from pathlib import Path
root = Path('/Users/seyoonr/.codex/worktrees/derand-proof/tcslib-exchange')
path = root / 'TCSlib/Complexity/Randomized/Build/IterateFind.lean'
text = path.read_text()
assert text.count('  exact ⟨L, c, A, D, hL⟩') == 1
text = text.replace('  exact ⟨L, c, A, D, hL⟩',
                    '  exact ⟨L, c, A, D, by simpa only [T, pow] using hL⟩')
path.write_text(text)
