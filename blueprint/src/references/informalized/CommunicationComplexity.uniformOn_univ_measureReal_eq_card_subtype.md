<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean :: CommunicationComplexity.uniformOn_univ_measureReal_eq_card_subtype -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Measure and Subtype Cardinality

**Claim.** For a nonempty finite discrete space with its uniform probability measure, the real measure of a set is the number of its elements divided by the cardinality of the whole space.

**Proof.** The uniform-measure formula expresses the real measure as the cardinality of the finite set of points satisfying membership in the given set, divided by the cardinality of the whole space ($\texttt{uniformOn\_univ\_measureReal\_eq\_card\_filter}$). The elements of that filtered set correspond exactly to the elements of the subtype consisting of points in the set, so its cardinality is the subtype's cardinality. Substituting this equality proves the formula.

**Key facts.** `CommunicationComplexity.uniformOn_univ_measureReal_eq_card_filter`.
