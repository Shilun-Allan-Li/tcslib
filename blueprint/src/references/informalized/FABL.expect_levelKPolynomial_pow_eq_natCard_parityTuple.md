<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.expect_levelKPolynomial_pow_eq_natCard_parityTuple -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Moment Counts Parity Tuples

**Claim.** For natural numbers $n,k,q$, the uniform expectation of the $q$th power of the level-$k$ polynomial equals the number of ordered $q$-tuples of subsets of $\{0,\ldots,n-1\}$ whose symmetric difference is empty and each of which has size $k$.

**Proof.** First express the expectation of a $q$th power as a sum, over $q$-tuples of subsets with empty symmetric difference, of products of the corresponding Fourier coefficients (\texttt{expect_pow_eq_sum_fourierCoeff_of_tupleSymmDiff_empty}). Each Fourier coefficient of the level-$k$ polynomial is $1$ when its indexing set has size $k$ and $0$ otherwise (\texttt{fourierCoeff_levelKPolynomial}). Consequently, each tuple contributes $1$ precisely when all its sets have size $k$, and contributes $0$ otherwise. The remaining sum therefore counts exactly the tuples satisfying both conditions. This count is the cardinality of the subtype defining the parity tuples, as required.

**Key facts.** `FABL.expect_pow_eq_sum_fourierCoeff_of_tupleSymmDiff_empty`, `FABL.fourierCoeff_levelKPolynomial`.
