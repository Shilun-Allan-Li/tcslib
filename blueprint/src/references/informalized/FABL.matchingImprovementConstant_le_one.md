<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.matchingImprovementConstant_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Improvement constant is at most one

**Claim.** For natural numbers $r,k$ with $r>0$, the improvement constant is at most $1$.

**Proof.** The denominator in the factorial ratio is positive, so the factorial bound $(rk)!\le (k!)^r r^{rk}$ implies that the ratio lies between $0$ and $1$. Its exponent $1/(2r)$ is positive; raising a number in this interval to that power gives a value at most $1$. This value is the improvement constant.

**Key facts.** `FABL.factorial_mul_le_factorial_pow_mul_pow`.
