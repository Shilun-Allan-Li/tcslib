<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/RectangleSwitching.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.conditionalSpecialPairLaw_eq_prod_of_singleton_factorization -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product Law from Singleton Factorization

**Claim.** If, for every pair of bits, the conditional law of the special-bit pair assigns its singleton mass as the product of the corresponding marginal singleton masses, then the pair law is the product of its marginal laws.

**Proof.** Two finite measures on the Boolean-pair space are equal once their real masses agree on every singleton. Fix a pair $(b_X,b_Y)$. By hypothesis, the conditional pair law’s mass at this singleton is the product of the marginal masses at $b_X$ and $b_Y$. The singleton $\{(b_X,b_Y)\}$ is the rectangle $\{b_X\}\times\{b_Y\}$, and the product measure of a rectangle is the product of the two factor measures there. Thus the product law has the same singleton mass, and the singleton criterion gives equality of the measures.
