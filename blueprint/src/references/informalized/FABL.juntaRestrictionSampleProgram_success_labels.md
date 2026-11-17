<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.juntaRestrictionSampleProgram_success_labels -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Labels on matched examples

**Claim.** Whenever the program produces a batch of matched examples, each example's label agrees with the value of the restriction at its free-coordinate part.

**Proof.** By the characterization of outcomes of this program (`runWithCost_juntaRestrictionSampleProgram`), membership in the run's support gives a batch of sampled inputs whose corresponding output is the given outcome. Since the outcome's first component is the specified batch, the matching procedure applied to those sampled inputs returns that batch. For each index, the selected sample therefore has label equal to the target at its input. The matched-example construction retains this sample, so its label is the target value at the sample's full input. The lemma that the label of a matched restriction example equals the restriction evaluated on its free part (`matchedJuntaRestrictionExample_label`) now gives the claimed equality.

**Key facts.** `FABL.runWithCost_juntaRestrictionSampleProgram`, `FABL.matchedJuntaRestrictionExample_label`.
