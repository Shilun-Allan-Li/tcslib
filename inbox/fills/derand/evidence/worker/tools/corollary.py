"""Prove the frozen DTIME corollary only through the published membership reader."""
from pathlib import Path

path = Path('TCSlib/Complexity/Randomized/SeedMajority.lean')
src = path.read_text()
start = src.index('theorem seedMajority_mem_DTIME')
assert src.count('  sorry', start) == 1
src = src[:start] + src[start:].replace('  sorry', '''  obtain ⟨M, c, e, hM, _⟩ := exists_seedMajorityTM hV w hw
  exact ⟨e, mem_DTIME_iff.mpr ⟨c, M, hM⟩⟩''', 1)
old = '''**Status.** Admitted (a `sorry`). It follows from `exists_seedMajorityTM` through the reader
`Complexity.mem_DTIME_iff`, which the `derand` fill adds beside `DTIME` (`ClassP/DTIME.lean`)
under its pre-approval (Seyoon, 2026-11-15). The `derand` fill proves both the contract and
this corollary. Until the reader exists, a proof would read `Turing.FinTM.DecidesInTime`,
`Turing.FinTM.DecidesInTimeVia` and `DTIME` by their definitions, which Rule 10 forbids.'''
new = '''**Status.** Proved modulo `exists_seedMajorityTM`. The proof reads the machine contract
through `Complexity.mem_DTIME_iff`, added beside `DTIME` under the pre-approval of
2026-11-15. It uses no definitional reading of either `DTIME` or `DecidesInTime`.'''
assert old in src
src = src.replace(old, new, 1)
old = '''* `Complexity.seedMajority_mem_DTIME` — the decision-class corollary
  `∃ e, {x | 2^{w(|x|)} < 2 · count} ∈ DTIME (n ↦ 2^{w(n)} · (n+1)^e)` (stated; a `sorry`
  until the `derand` fill adds `mem_DTIME_iff`, then read off the contract).'''
new = '''* `Complexity.seedMajority_mem_DTIME` — the decision-class corollary
  `∃ e, {x | 2^{w(|x|)} < 2 · count} ∈ DTIME (n ↦ 2^{w(n)} · (n+1)^e)`, proved from
  the host contract through `mem_DTIME_iff`.'''
assert old in src
path.write_text(src.replace(old, new, 1))
