<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.FiniteUniqueGame.propagatedLabel_eq_of_fullySatisfied -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Propagation Recovers a Satisfying Labeling

**Claim.** If a labeling satisfies every constraint, then propagating the labels at component roots along the chosen paths recovers that labeling at every vertex.

**Proof.** Fix a vertex and consider its chosen path from the root of its component. The fact that the original labeling satisfies every constraint implies that the label at the endpoint of any walk is the transport of the label at its starting point (`Walk.label_eq_transport`). Apply this to the chosen path: the original label at the vertex is the transport of the original label at the component root. This is exactly the value assigned there by propagation. Since the two labelings agree at every vertex, they are equal.

**Key facts.** `FABL.FiniteUniqueGame.Walk.label_eq_transport`.
