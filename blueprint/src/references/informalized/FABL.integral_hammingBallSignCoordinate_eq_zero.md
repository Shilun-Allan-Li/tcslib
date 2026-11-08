<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/HammingBallLimit.lean :: FABL.integral_hammingBallSignCoordinate_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of a Uniform Sign Coordinate

**Claim.** For each coordinate $i<n$, the mean of $x_i$ under the uniform distribution on sign vectors in $\{-1,1\}^n$ is zero.

**Proof.** First identify integration under the uniform sign-vector measure with expectation under the uniform distribution (\(\texttt{integral\_uniformPMF\_eq\_expect}\)). The coordinate function $x\mapsto x_i$ is the monomial associated with the singleton set $\{i\}$. The expectation of a monomial is $1$ for the empty set and $0$ otherwise (\(\texttt{expect\_monomial}\)); since $\{i\}$ is nonempty, its expectation, and hence the desired integral, is zero.

**Key facts.** `FABL.integral_uniformPMF_eq_expect`, `FABL.expect_monomial`.
