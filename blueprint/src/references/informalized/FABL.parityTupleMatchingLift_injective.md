<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.parityTupleMatchingLift_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the matching lift

**Claim.** The map from a parity tuple together with its position reorderings to the lifted matching and compatible vertex labeling is injective.

**Proof.** Suppose two inputs have the same lifted output. Equality of the underlying data gives equality of their vertex-labeling functions. For each part, the set of labels appearing on its vertices recovers the original subset: the fact that the label set of an assigned labeling equals the tuple's subset is \(FABL.LevelKParityTuple.matchingLabelSet_assignedVertexLabel\). Equality of the labeling functions therefore implies equality of every subset, hence equality of the two parity tuples. With the tuple fixed, equality of the labeling functions also says that the two enumerations send each reordered position to the same element of the subset. The enumeration is a bijection, so it is injective; consequently the two reorderings agree at every part and position. Both components of the inputs are equal, proving injectivity.

**Key facts.** `FABL.LevelKParityTuple.matchingLabelSet_assignedVertexLabel`.
