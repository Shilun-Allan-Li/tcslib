<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityComplementaryWeights.lean :: FABL.fourierCoeff_majority_complementary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complementary majority coefficients

**Claim.** For odd $n$ and coordinate sets $S,T$ satisfying $|S|+|T|=n+1$, the majority Fourier coefficients obey $\widehat{\mathrm{Maj}_n}(S)=(-1)^{(n-1)/2}\widehat{\mathrm{Maj}_n}(T)$.

**Proof.** Write $n=2m+1$. If $|S|$ is even, the cardinality condition forces $|T|$ even as well. Majority has zero Fourier coefficient at every even-sized set in odd dimension (`FABL.fourierCoeff_majority_eq_zero_of_odd_arity_of_even_card`), so the claimed equality holds. If $|S|=2j+1$, then the cardinality condition gives $|T|=2(m-j)+1$. Apply the explicit odd-cardinality formula for majority coefficients to both sets (`FABL.fourierCoeff_majority_two_mul_add_one`). The binomial factors agree by the symmetry $\binom{m}{m-j}=\binom{m}{j}$ and the symmetry of the denominator binomial coefficients. The remaining signs satisfy $(-1)^j=(-1)^m(-1)^{m-j}$, since their exponents differ by an even integer. Substitution yields the stated relation.

**Key facts.** `FABL.fourierCoeff_majority_eq_zero_of_odd_arity_of_even_card`, `FABL.fourierCoeff_majority_two_mul_add_one`.
