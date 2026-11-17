<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.LevelKParityTuple.matchingLabelSet_assignedVertexLabel -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Labels in each part

**Claim.** For every part, the set of labels assigned to its positions is exactly the set belonging to that part.

**Proof.** To prove one inclusion, take a label in the image of the positions. It is the underlying element of an enumerated subtype point, so it belongs to the part’s set. Conversely, take any element of that set and regard it as a subtype point. Apply the inverse enumeration to obtain its position, then undo the part’s permutation. The resulting position is labeled by the original element, so that element lies in the image.
