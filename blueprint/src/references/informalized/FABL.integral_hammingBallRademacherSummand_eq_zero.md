<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/HammingBallLimit.lean :: FABL.integral_hammingBallRademacherSummand_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of a Normalized Sign Summand

**Claim.** For a coordinate $i<n$, the mean of the coordinate value $x_i$ multiplied by $1/\sqrt n$ under the uniform distribution on sign vectors is zero.

**Proof.** The summand is the constant normalization factor $1/\sqrt n$ times the sign coordinate. By the preceding coordinate-mean identity (\(\texttt{integral\_hammingBallSignCoordinate\_eq\_zero}\)), that coordinate has mean zero under the uniform sign-vector measure. Pulling the constant factor out of the integral therefore leaves the normalization factor times zero, which is zero.

**Key facts.** `FABL.integral_hammingBallSignCoordinate_eq_zero`.
