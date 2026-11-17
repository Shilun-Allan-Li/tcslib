<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierTailAsymptotics.lean :: FABL.fourierWeightAbove_boolean_eq_one_sub_sum_range -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean Fourier weight above a level

**Claim.** For a Boolean function and $k\le n$, its Fourier weight on subsets of size greater than $k$ equals one minus the sum of its Fourier weights at levels $0$ through $k$.

**Proof.** Parseval's identity gives total Fourier weight one for the real-valued version of the Boolean function (`sum_sq_fourierCoeff_eq_one`). The sum of the weights by levels from $0$ through $n$ is this total weight (`sum_fourierWeightAtLevel_range`), so it too equals one. The weight above level $k$ is the sum of the level weights from $k+1$ through $n$ (`fourierWeightAbove_eq_sum_levels`). The levels from $0$ through $k$ and from $k+1$ through $n$ partition the full range of levels. Subtracting the first block's sum from the total one yields the asserted identity.

**Key facts.** `FABL.sum_fourierWeightAtLevel_range`, `FABL.sum_sq_fourierCoeff_eq_one`, `FABL.fourierWeightAbove_eq_sum_levels`.
