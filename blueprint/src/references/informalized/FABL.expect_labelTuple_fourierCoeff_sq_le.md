<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.expect_labelTuple_fourierCoeff_sq_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficient Bound for Random Tuples

**Claim.** If a real-valued function on the $n$-dimensional sign cube has Fourier coefficients supported at level $k$, then the expected squared Fourier coefficient indexed by the image of a uniformly chosen map from a $k$-element set to an $n$-element set is at most $k!/n^k$ times its total Fourier weight at level $k$.

**Proof.** The sum over all such maps of the squared coefficient indexed by the image is at most $k!$ times the level-$k$ Fourier weight (\texttt{sum_labelTuple_fourierCoeff_sq_le}). Uniform expectation over maps is this sum divided by the number of maps, which is $n^k$. Divide the sum bound by $n^k$, which is nonnegative, and rearrange the resulting factor to obtain the claimed bound.

**Key facts.** `FABL.sum_labelTuple_fourierCoeff_sq_le`.
