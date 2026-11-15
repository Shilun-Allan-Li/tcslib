from pathlib import Path
root = Path('/Users/seyoonr/.codex/worktrees/derand-proof/tcslib-exchange')
path = root / 'TCSlib/Cryptography/Randomness/Derandomization.lean'
text = path.read_text()
text = text.replace('import TCSlib.Cryptography.Randomness.Derandomization.RootSchedule',
'''import TCSlib.Cryptography.Randomness.Derandomization.RootSchedule
import TCSlib.Cryptography.Randomness.Derandomization.AdviceGap
import TCSlib.Cryptography.Randomness.Derandomization.Expanded
import TCSlib.Cryptography.Randomness.Derandomization.CoinGap
import TCSlib.Cryptography.Randomness.Derandomization.Majority
import TCSlib.Cryptography.Randomness.Derandomization.TimeBound
import TCSlib.Complexity.Randomized.QuasiPolyHierarchy''')
text = text.replace('# Derandomization from pseudorandom generators (statement phase)',
                    '# Derandomization from pseudorandom generators')
text = text.replace('* `Randomness.Derandomization.RootSchedule`: the integer-root seed schedule.',
'''* `Randomness.Derandomization.RootSchedule`: the integer-root seed schedule.
* `Randomness.Derandomization.AdviceGap`: the non-uniform advice gap bound.
* `Randomness.Derandomization.Expanded`: the secure polynomial output envelope.
* `Randomness.Derandomization.CoinGap`: the uniform prefix probability identification.
* `Randomness.Derandomization.Majority`: the piecewise verifier and strict majority.
* `Randomness.Derandomization.TimeBound`: the asymptotic estimate and finite exceptions.''')
text = text.replace('* `Randomness.bpp_subset_dtime_subexp` (Thm 180.1, stated; a `sorry` under the source\'s sketch).',
'''* `Randomness.bpp_subset_dtime_subexp` (Thm 180.1), proved modulo the shared
  seed-majority machine contract through its DTIME corollary.''')
start = text.index('**Proof sketch** (the source\'s,')
end = text.index(' -/\ntheorem bpp_subset_dtime_subexp', start)
sketch = '''**Status.** Proved modulo `Complexity.exists_seedMajorityTM`, through
`Complexity.seedMajority_mem_DTIME`; the helpers introduce no admissions.

**Proof sketch** ([PS10, Theorem 180.1], with an explicit piecewise test).
1. Choose an integer `d ≥ 2` with `1/d < min(ε,1)`. The least natural root
   `ℓ(n) = min{t | n ≤ t^d}` has an FP unary word and satisfies
   `n ≤ ℓ(n)^d` and `ℓ(n) ≤ n^(1/d)+1`, including at zero.
2. Expand a secure generator to `a(s^d+1)^k+s+1` and extract its FP evaluator.
   Apply the verifier bridge to one bad input at each bad seed length, with
   advice bound `s^d`. The published probability bridge and prefix projection
   identify its PRG advantage with the verifier gap. Negligibility's inverse-linear
   bound rules out every gap above `1/12` beyond a seed threshold, hence beyond
   some input threshold `n₀`.
3. Below `n₀`, use the original verifier with its true polynomial coin width;
   from `n₀` on, use the generated prefix and width `ℓ(n)`. Both this paired
   test and its unary width are polynomial-time. Acceptance is above `1/2`
   exactly on members, with margins at least `7/12` and at most `5/12` in the
   generated case. `half_lt_randProb_iff` identifies `L` with the strict seed
   majority, including ties and zero widths. No exceptional-input table is used.
4. Apply `seedMajority_mem_DTIME`. The logarithm of `2^w(n)(n+1)^e`, divided
   by `n^ε`, tends to zero because `1/d < ε`; thus the time is eventually at
   most `2^(n^ε)`. A natural constant absorbs all earlier lengths, since the
   rounded bound is positive. Finish through `DTIME.mono` and
   `Randomized.DTIME_const_mul_subset`.'''
text = text[:start] + sketch + text[end:]
old = '''    {L | Randomized.InBPP Randomized.polyTimeModel L} ⊆ DTIME (subexpBound ε) := by
  sorry'''
new = '''    {L | Randomized.InBPP Randomized.polyTimeModel L} ⊆ DTIME (subexpBound ε) := by
  intro L hL
  obtain ⟨d, hd, hdε, _⟩ := Derand.exists_root_degree hε
  have hdpos : 0 < d := by omega
  obtain ⟨V, w, n₀, hV, hw, hevent, hmajority⟩ :=
    Derand.exists_seed_majority hPRG hL d hdpos
  obtain ⟨e, htime⟩ := seedMajority_mem_DTIME hV w hw
  rw [← hmajority] at htime
  obtain ⟨C, hbound⟩ := Derand.seed_time_le_subexp hdpos hε hdε w n₀ hevent e
  apply Randomized.DTIME_const_mul_subset C (subexpBound ε)
  apply DTIME.mono (fun n => ?_) htime
  simpa only [subexpBound_eq] using hbound n'''
assert old in text
text = text.replace(old, new)
path.write_text(text)
