<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Moments.lean :: BooleanAnalysis.Hypercontractivity.MultilinearMoments.monomial_memLp_nat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite integrability of monomials

**Claim.** For independent random variables in $L^p$ with positive integer exponent $p$, every monomial indexed by a subset of coordinates belongs to $L^p$.

**Proof.** Choose the multilinear polynomial whose coefficient is $1$ at the specified subset $S$ and $0$ at every other subset. The polynomial-evaluation integrability result (`evalMultilinearRV_memLp_nat`) shows that its evaluation belongs to $L^p$. Since this evaluation is exactly the monomial indexed by $S$, the desired membership follows.

**Key facts.** `BooleanAnalysis.Hypercontractivity.evalMultilinearRV_memLp_nat`.
