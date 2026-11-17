<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/ZFiberMeasure.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformBoolPair_eq_prod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product Structure of the Uniform Bit-Pair Law

**Claim.** The uniform law on ordered pairs of Boolean values equals the product of two copies of the uniform law on a single Boolean value.

**Proof.** It suffices to compare the two measures on each singleton bit-pair. Fix $(b_x,b_y)$. The uniform pair law assigns this singleton mass $1/4$ ( `uniformBoolPair_singleton` ). The singleton is the product of the singleton events for $b_x$ and $b_y$, so the product-measure formula gives its mass under the product law as the product of the two individual singleton masses. Each individual mass is $1/2$ ( `uniformBool_singleton` ), and their product is $1/4$. Thus the two measures agree on every singleton, and hence are equal.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformBoolPair_singleton`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformBool_singleton`.
