<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/Program.lean :: FABL.LearningProgram.outerEventProbability_map_cons_exists -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prepending a good item preserves bad-event probability

**Claim.** If the fixed head item is not bad, then mapping a list-output program by prepending that item leaves unchanged the outer probability that its output list contains any bad item.

**Proof.** The law after mapping the program by prepending the fixed head is the image of the original outcome law under the map that prepends to the output and leaves the cost unchanged (\texttt{runWithCost\_map}). The outer measure of this image law on the event in question is the measure of the event’s preimage. A list with the good head prepended contains a bad item exactly when its tail list contains a bad item: the head itself is not bad, and all other entries are precisely the tail entries. Hence the preimage is the original bad-list event, so the two outer probabilities are equal.

**Key facts.** `FABL.LearningProgram.runWithCost_map`.
