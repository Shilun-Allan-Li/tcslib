<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.expect_triple_mul_separate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Factorization of a Product Average

**Claim.** For functions on three finite sets, the uniform average of their product over the product set is the product of their individual uniform averages.

**Proof.** Regroup the integrand as $f(a)(g(b)h(c))$. The average over $A\times(B\times C)$ factors into the average of $f$ over $A$ times the average of $(b,c)\mapsto g(b)h(c)$ over $B\times C$, by the pair-product factorization fact (`expect_pair_mul_separate`). Apply that same fact to the latter average to factor it into the averages of $g$ and $h$. Associativity of multiplication gives the claimed expression.

**Key facts.** `FABL.expect_pair_mul_separate`.
