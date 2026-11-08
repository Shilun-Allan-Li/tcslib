<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformBool_real -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Measure of a Boolean Subset

**Claim.** For every subset $S$ of the Booleans, its real measure under the uniform Boolean law is the number of Boolean values in $S$ divided by two.

**Proof.** The uniform-measure cardinality formula says that the real measure of a subset of a finite uniform space is the cardinality of that subset divided by the cardinality of the whole space ( `uniformOn_univ_measureReal_eq_card_subtype` ). Here the subset is represented by the Boolean values satisfying membership in $S$, and the whole Boolean space has cardinality two. Substitution gives the stated formula.

**Key facts.** `CommunicationComplexity.uniformOn_univ_measureReal_eq_card_subtype`.
