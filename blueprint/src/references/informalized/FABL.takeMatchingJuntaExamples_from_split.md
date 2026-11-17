<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.takeMatchingJuntaExamples_from_split -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Matched examples from a split sample

**Claim.** If at least $M$ fixed assignments in the split sample equal $z$, selecting the first $M$ matching samples and extracting their free assignments and labels yields exactly the batch obtained by applying the restriction of the target function to those free assignments.

**Proof.** First, each split sample is formed using its given fixed assignment, so taking the fixed part of its input recovers that assignment. Consequently its matching count is the cardinality of the matching indices for the supplied fixed assignments, and the assumed bound ensures that the option-valued selection is defined.

The embedding used to select matching indices is therefore the same as the embedding that selects the first $M$ entries of the ordered set of matching indices. Each selected index belongs to that set, so its fixed assignment equals $z"). At such an index, the sample input is obtained by combining $z$ with its free assignment. Extracting the free part recovers that free assignment, by the fact that the free part of a combined assignment is the original free assignment (juntaFreePart_combineJuntaAssignment).

It remains to identify the output label. The label of the selected sample is the target function applied to the combined input. Since its fixed assignment is $z$, this is exactly the target function with $z$ fixed and the selected free assignment supplied; that is the restriction label. Thus both coordinates of every selected pair agree with the corresponding entry of the stated batch, proving equality of the batches.

**Key facts.** `FABL.juntaFreePart_combineJuntaAssignment`.
