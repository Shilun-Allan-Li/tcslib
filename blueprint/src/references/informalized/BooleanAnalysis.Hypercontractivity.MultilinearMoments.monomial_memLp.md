<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Moments.lean :: BooleanAnalysis.Hypercontractivity.MultilinearMoments.monomial_memLp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth integrability of monomials

**Claim.** If the variables are independent and each belongs to $L^4$, then the monomial indexed by any subset of coordinates belongs to $L^4$.

**Proof.** Use the finite-integrability result for monomials (`MultilinearMoments.monomial_memLp_nat`) with exponent $p=4$. The exponent is positive, and the hypotheses of independence and $L^4$ integrability are exactly those required by that result. Its conclusion is the asserted $L^4$ membership.

**Key facts.** `BooleanAnalysis.Hypercontractivity.MultilinearMoments.monomial_memLp_nat`.
