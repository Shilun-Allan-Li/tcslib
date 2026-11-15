from pathlib import Path
root = Path('/Users/seyoonr/.codex/worktrees/derand-proof/tcslib-exchange')
path = root / 'TCSlib/Complexity/Randomized/Build/IterateFind.lean'
text = path.read_text()
old = '  exact ⟨L, c, A, D, by simpa only [T, pow] using hL⟩'
new = '''  refine ⟨L, c, A, D, (FinTM.computesFunInTime_iff _ _ _).mpr fun x => ?_⟩
  have hx := (FinTM.computesFunInTime_iff _ _ _).mp hL x
  simpa only [T, pow] using hx'''
assert old in text
text = text.replace(old, new)
path.write_text(text)
