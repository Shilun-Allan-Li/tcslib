<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/ZFiberMeasure.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.two_mul_xDistance_sq_le_toReal_klDiv_uniformBool -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Total Variation Bound by Relative Entropy

**Claim.** For the conditional special-bit law and the uniform bit law, twice the square of their total variation distance is at most the real-valued Kullback–Leibler divergence between them.

**Proof.** Apply the finite-space Pinsker inequality: for probability measures whose relative entropy is finite, twice the square of their total variation distance is at most the real-valued relative entropy ( `two_mul_tvDistance_sq_le_toReal_klDiv` ). Its finiteness hypothesis holds here because every outcome has positive mass under the uniform bit law: `uniformBool_toPMF_ne_zero` supplies this positivity, and `klDiv_ne_top_of_forall_toPMF_ne_zero` then shows that the relative entropy is not infinite. Finally, unfold the definition of the conditional total variation distance to obtain the stated inequality.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformBool_toPMF_ne_zero`, `CommunicationComplexity.FiniteMeasureSpace.klDiv_ne_top_of_forall_toPMF_ne_zero`, `CommunicationComplexity.two_mul_tvDistance_sq_le_toReal_klDiv`.
