from pathlib import Path
root = Path('/Users/seyoonr/.codex/worktrees/derand-proof/tcslib-exchange')
path = root / 'TCSlib/Complexity/Randomized/SeedMajority.lean'
text = path.read_text()
text = text.replace('import TCSlib.Complexity.Randomized.Classes',
'''import TCSlib.Complexity.Randomized.Classes
import TCSlib.Complexity.Randomized.SeedMajority.Words
import TCSlib.Complexity.Randomized.SeedMajority.State
import TCSlib.Complexity.Randomized.SeedMajority.Enumeration
import TCSlib.Complexity.Randomized.SeedMajority.Envelope''')
text = text.replace('# Deterministic majority over all seeds (statement phase)',
                    '# Deterministic majority over all seeds')
text = text.replace('## Main results',
'''## Contents

* `Complexity.Randomized.SeedMajority.Words`: binary seed words and prefix counts.
* `Complexity.Randomized.SeedMajority.State`: the FP counting round and terminal tests.
* `Complexity.Randomized.SeedMajority.Enumeration`: the finite binary-fuel machine.
* `Complexity.Randomized.SeedMajority.Envelope`: the all-times work-head bound.

## Main results''', 1)
text = text.replace('  head envelope of one machine (stated; a `sorry` under the route below, for the `derand` fill).',
                    '  head envelope of one machine, proved through the generic binary-fuel harvest.')
text = text.replace('**Proof sketch** (the route of the module docstring; the `derand` fill).',
'''**Status.** Proved through `SeedMajority.exists_countingTM` and
`SeedMajority.envelope_of_computesInTime`, using only the published decision and
computation readers.

**Proof sketch** (the route of the module docstring; implemented in the helpers).''')
text = text.replace('**Status.** Proved modulo `exists_seedMajorityTM`. The proof reads the machine contract',
                    '**Status.** Proved from `exists_seedMajorityTM`. The proof reads the machine contract')
old = '''            ((c * (2 ^ w x.length * (x.length + 1) ^ e) : ℕ) : ℤ) := by
  sorry'''
new = '''            ((c * (2 ^ w x.length * (x.length + 1) ^ e) : ℕ) : ℤ) := by
  obtain ⟨M, c, e, hM⟩ := SeedMajority.exists_countingTM hV w hw
  refine ⟨M, c, e, ?_, ?_⟩
  · apply (FinTM.decidesInTime_iff _ _ _).mpr
    intro x
    have hx := (FinTM.computesFunInTime_iff _ _ _).mp hM x
    rw [MultiTapeTM.indicator_def]
    change M.ComputesInTime x
      [if 2 ^ w x.length <
        2 * (Finset.univ.filter fun u : Fin (w x.length) → Bool =>
          pairEncode x (List.ofFn u) ∈ V).card then true else false]
      (c * (2 ^ w x.length * (x.length + 1) ^ e))
    by_cases h : 2 ^ w x.length <
        2 * (Finset.univ.filter fun u : Fin (w x.length) → Bool =>
          pairEncode x (List.ofFn u) ∈ V).card
    · simpa only [if_pos h, decide_eq_true h] using hx
    · simpa only [if_neg h, decide_eq_false h] using hx
  · intro x v j
    exact SeedMajority.envelope_of_computesInTime
      ((FinTM.computesFunInTime_iff _ _ _).mp hM x) v j'''
assert old in text
text = text.replace(old, new)
path.write_text(text)
