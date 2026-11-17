<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean :: CommunicationComplexity.uniformOn_univ_measureReal_eq_card_filter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Measure and Filtered Cardinality

**Claim.** For a nonempty finite discrete space with its uniform probability measure, the real measure of a set is the cardinality of its elements divided by the cardinality of the whole space.

**Proof.** The uniform measure on the whole space assigns a set its counting measure divided by the cardinality of the space. In a discrete measurable space every set is measurable, and counting measure of the set is its cardinality. Converting the resulting cardinality ratio from extended reals to reals gives the stated quotient, with the numerator represented by the filtered finite set.
