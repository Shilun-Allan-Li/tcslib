<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/Basic.lean :: ProbabilityTheory.indepFun_of_measureReal_inter_preimage_singleton_eq_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Independence from fiber probabilities

**Claim.** For measurable maps into finite measurable spaces, if every joint fiber has measure equal to the product of its two marginal fiber measures, then the maps are independent.

**Proof.** Because the target spaces are finite, it suffices to compare the joint distribution and the product of the marginal distributions on singleton pairs. For each $(x,y)$, the inverse image of the singleton pair is $X^{-1}\{x\}\cap Y^{-1}\{y\}$. Its measure, by hypothesis, is the product of the measures of the two individual fibers. The product measure assigns that same value to $\{x\}\times\{y\}$, by the product formula for measurable rectangles. Thus the joint distribution and the product of the marginals agree on every singleton pair, and hence agree as measures. This is precisely independence.
