<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/ZVariable.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.volume_zFiber_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Volume of Achievable Fibers

**Claim.** Every achievable value of the statistic has a fiber of nonzero volume under the uniform measure on the hard-sample space.

**Proof.** Because $z$ is achievable, choose a sample $\omega$ whose raw statistic equals the raw value underlying $z$ (`ZType.achievable`). The subtype-valued statistic at $\omega$ is therefore $z$, so the fiber over $z$ is nonempty. For a uniform measure on a finite nonempty space, the measure of a set is the cardinality of that set divided by the cardinality of the whole space (`uniformOn_univ_measureReal_eq_card_subtype`). Both cardinalities are positive, so the fiber has positive real measure, equivalently its measure is nonzero.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.ZType.achievable`, `CommunicationComplexity.uniformOn_univ_measureReal_eq_card_subtype`.
