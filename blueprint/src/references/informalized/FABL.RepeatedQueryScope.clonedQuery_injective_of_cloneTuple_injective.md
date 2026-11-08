<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RepeatedQueryScope.clonedQuery_injective_of_cloneTuple_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the Cloned Query Map

**Claim.** If the assignment of clone labels to positions is injective, then the map sending each position to its original query together with its clone label is injective.

**Proof.** Suppose two positions have the same image under the cloned query map. Equality of ordered pairs implies equality of their clone labels. Injectivity of the clone assignment then gives equality of the positions, as required.
