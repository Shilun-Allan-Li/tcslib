<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/RectangleSwitching.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.conditionalSpecialPairLaw_eq_prod_of_zFiberMeasure_factorization -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product law from fiber factorization

**Claim.** If, on each achievable summary fiber, the mass of every special-bit pair factors as the product of the masses of its two individual bits, then the conditional law of the pair is the product of the two conditional marginal laws.

**Proof.** Fix a pair of bits $b=(b_1,b_2)$. The singleton-mass identities for the pair law and the two marginal laws express their masses at $\{b\}$, $\{b_1\}$, and $\{b_2\}$ as the corresponding fiber-event masses. The assumed factorization therefore gives the required factorization of singleton masses for the conditional laws. The singleton-factorization criterion for product measures, which identifies measures on this finite pair space from these masses, then gives the claimed equality of measures (conditionalSpecialPairLaw_eq_prod_of_singleton_factorization).

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.conditionalSpecialPairLaw_eq_prod_of_singleton_factorization`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.conditionalSpecialPairLaw_singleton`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.conditionalSpecialXLaw_singleton`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.conditionalSpecialYLaw_singleton`.
