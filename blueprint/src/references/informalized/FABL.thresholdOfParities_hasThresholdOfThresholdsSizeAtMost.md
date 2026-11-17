<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.thresholdOfParities_hasThresholdOfThresholdsSizeAtMost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sparse thresholds as threshold compositions

**Claim.** If a Boolean function is the sign threshold of a polynomial with Fourier support of size at most $s$, then it is a threshold of at most $2ns$ linear threshold functions.

**Proof.** Choose a polynomial $p$ witnessing the threshold representation and the sparsity bound. The polynomial-threshold composition theorem (`polynomialThresholdRepresentation_hasThresholdOfThresholdsSizeAtMost`) supplies a representation as a threshold of some $t$ linear threshold functions, with $t\le 2n\,\mathrm{polynomialSparsity}(p)$. Since the sparsity of $p$ is at most $s$, multiplying that inequality by the nonnegative integer $2n$ gives $t\le 2ns$. The supplied composition therefore witnesses the claimed size bound.

**Key facts.** `FABL.polynomialThresholdRepresentation_hasThresholdOfThresholdsSizeAtMost`.
