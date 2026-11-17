<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.one_div_card_le_uniformProbability_of_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mass of a Nonempty Event

**Claim.** If a predicate holds at some element of a finite nonempty set, its uniform probability is at least the reciprocal of the set's cardinality.

**Proof.** Express the uniform probability as the sum over all elements of the indicator of the predicate, divided by the cardinality of the set. The indicator equals $1$ at the specified sample. Since every indicator in the sum is nonnegative, the whole sum is at least that sample's contribution, namely $1$. The set is nonempty, so its cardinality is positive; dividing by it proves the bound.
