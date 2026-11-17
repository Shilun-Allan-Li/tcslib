<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.expect_restrictedFourierWeightAtLeast_eq_sum_intersectionTail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected Restricted Fourier Tail

**Claim.** The expected restricted Fourier weight on degrees at least $k$ equals the sum over frequencies $U$ of their squared Fourier coefficients weighted by the random-subset contribution from subsets of $U$ having size at least $k$.

**Proof.** First exchange the finite sum over restricted frequencies $S$ with the expectation over the random restriction. For each fixed $S$, if $|S|<k$ its contribution is zero. Otherwise apply the identity for the expected square of a restricted Fourier coefficient: summing over restrictions and fixed coordinates gives, for each ambient frequency $U$, the squared coefficient $\widehat f(U)^2$ multiplied by $\delta^{|S|}(1-\delta)^{|U\setminus S|}$ when $S\subseteq U$, and zero otherwise. Next interchange the finite sums over $S$ and $U$ and collect the terms multiplying each squared coefficient. The resulting inner sum over $S\subseteq U$ with $|S|\ge k$ is exactly the random-intersection-tail weight, by its defining sum identity (FABL.deltaRandomIntersectionTail_eq_sum). This yields the claimed formula.

**Key facts.** `FABL.sum_expectRandomRestriction`, `FABL.expect_sq_fourierCoeff_randomRestriction`, `FABL.deltaRandomIntersectionTail_eq_sum`.
