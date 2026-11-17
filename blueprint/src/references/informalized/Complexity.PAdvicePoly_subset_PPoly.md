<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PAdviceSubsetPPoly.lean :: Complexity.PAdvicePoly_subset_PPoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Advice to Circuit Size

**Claim.** Every binary language decidable in polynomial time with advice of polynomial length has a polynomial-size family of Boolean circuits with fan-in at most two.

**Proof.** Choose natural numbers $c,C,d$ and an advice function witnessing that the language belongs to the stated polynomial-advice class. Apply the result that polynomial-time decision with advice bounded by $C(n+1)^d$ yields polynomial-size circuits (`Complexity.mem_PPoly_of_mem_DTIMEAdvice`). The advice bound required there is exactly the chosen length $C(n+1)^d$, so it holds with equality for every input length. The resulting circuit family has the required polynomial size and fan-in conditions.

**Key facts.** `Complexity.mem_PPoly_of_mem_DTIMEAdvice`.
