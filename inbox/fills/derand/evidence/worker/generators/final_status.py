from pathlib import Path
root = Path('/Users/seyoonr/.codex/worktrees/derand-proof/tcslib-exchange')
path = root / 'TCSlib/Cryptography/Randomness/Derandomization.lean'
text = path.read_text()
text = text.replace('''* `Randomness.bpp_subset_dtime_subexp` (Thm 180.1), proved modulo the shared
  seed-majority machine contract through its DTIME corollary.''',
'''* `Randomness.bpp_subset_dtime_subexp` (Thm 180.1), proved through the shared
  seed-majority machine contract and its DTIME corollary.''')
text = text.replace('''**Status.** Proved modulo `Complexity.exists_seedMajorityTM`, through
`Complexity.seedMajority_mem_DTIME`; the helpers introduce no admissions.''',
'''**Status.** Proved through `Complexity.exists_seedMajorityTM` and
`Complexity.seedMajority_mem_DTIME`; the helpers introduce no admissions.''')
path.write_text(text)
