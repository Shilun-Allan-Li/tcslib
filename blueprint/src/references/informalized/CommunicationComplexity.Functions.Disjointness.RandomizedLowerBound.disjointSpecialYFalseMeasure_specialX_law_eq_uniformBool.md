<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/ZFiberMeasure.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointSpecialYFalseMeasure_specialX_law_eq_uniformBool -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Special-Bit Distribution

**Claim.** Under the law conditioned on disjointness and on Bob’s special bit being false, the distribution of Alice’s special bit is the uniform law on the two Boolean values.

**Proof.** Both measures in the asserted equality are probability measures: the conditioned hard law is one (\texttt{disjointSpecialYFalseMeasure_isProbabilityMeasure}), and its image under the special-bit map is therefore also a probability measure. Measures on the finite Boolean space agree once they agree on each singleton. For either Boolean value $b$, the singleton mass under the image law is the mass of the event $X_T=b$ under the conditioned law, which is $1/2$ (\texttt{disjointSpecialYFalseMeasure_measureReal_specialX_singleton}). This equals the singleton mass under the uniform Boolean law (\texttt{uniformBool_singleton}), so the two laws coincide.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointSpecialYFalseMeasure_isProbabilityMeasure`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointSpecialYFalseMeasure_measureReal_specialX_singleton`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformBool_singleton`.
