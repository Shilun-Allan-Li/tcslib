<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ImprovedFKN.lean :: FABL.indexedLevelOneWeight_le_of_abs_mean_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Level-one weight bound for indexed cubes

**Claim.** If a sign-valued function on a finite indexed cube has mean with absolute value at least $1-\delta$, and $1-\delta\ge 0$, then the sum of the squares of its singleton indexed Fourier coefficients is at most $4\delta^2\log_2(2/\delta)$.

**Proof.** Transport the index set $\iota$ to the finite coordinate set of size $|\iota|$ using an equivalence with a finite type. This identifies the indexed cube with the finite sign cube. Define the corresponding Boolean function by pulling the given function back along this cube equivalence. Since the equivalence is a bijection, uniform averaging is preserved, so the two functions have the same mean. The same change of variables identifies the indexed coefficient at each $i\in\iota$ with the finite-cube Fourier coefficient at the corresponding coordinate. Apply the level-one Fourier-weight bound for a Boolean function whose mean has absolute value at least $1-\delta$ (`fourierWeightAtLevel_one_le_of_abs_mean_ge`). The level-one weight is the sum of squared singleton Fourier coefficients (`fourierWeightAtLevel_one_eq_sum_singleton`). Finally, reindex that sum through the coordinate equivalence; it is exactly the sum of the squared indexed coefficients, yielding the claimed bound.

**Key facts.** `FABL.fourierWeightAtLevel_one_le_of_abs_mean_ge`, `FABL.fourierWeightAtLevel_one_eq_sum_singleton`.
