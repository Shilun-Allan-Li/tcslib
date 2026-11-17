<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityNoiseStability.lean :: FABL.fourierWeightAtLevel_majority_next_odd_le_of_lt_top -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity across odd dimensions

**Claim.** If $k<2m+3$, then majority's level-$k$ Fourier weight in dimension $2m+3$ is at most its level-$k$ Fourier weight in dimension $2m+1$.

**Proof.** Split according to whether $k$ is even or odd. If $k$ is even, both level weights vanish by the even-level vanishing result for odd-dimensional majority (`fourierWeightAtLevel_majority_odd_eq_zero_of_even`), so the inequality holds with equality. If $k$ is odd, write $k=2j+1$. The bound $k<2m+3$ implies $j\le m$. The strict comparison between successive odd dimensions at level $2j+1$ (`fourierWeightAtLevel_majority_next_odd_lt`) applies, and its strict inequality implies the required weak inequality.

**Key facts.** `FABL.fourierWeightAtLevel_majority_odd_eq_zero_of_even`, `FABL.fourierWeightAtLevel_majority_next_odd_lt`.
