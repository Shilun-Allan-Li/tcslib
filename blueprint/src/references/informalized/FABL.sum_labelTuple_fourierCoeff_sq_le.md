<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.sum_labelTuple_fourierCoeff_sq_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Weight over Label Tuples

**Claim.** For a function whose nonzero Fourier coefficients are supported on subsets of size $k$, the sum over all maps from $[k]$ to $[n]$ of the squared Fourier coefficient indexed by the image is at most $k!$ times its total Fourier weight at level $k$.

**Proof.** Any noninjective map has an image of size less than $k$. If its Fourier coefficient were nonzero, homogeneity would force that image to have size $k$, a contradiction. Thus all noninjective maps contribute zero, and the sum can be restricted to injective label tuples. Apply the injection-counting bound (\texttt{FABL.sum_injectiveLabelTuple_le_factorial_mul}) to the nonnegative weight given by the squared Fourier coefficient. Its right-hand side sums this weight over subsets of size $k$, which is exactly the level-$k$ Fourier weight. This proves the desired inequality.

**Key facts.** `FABL.sum_injectiveLabelTuple_le_factorial_mul`.
