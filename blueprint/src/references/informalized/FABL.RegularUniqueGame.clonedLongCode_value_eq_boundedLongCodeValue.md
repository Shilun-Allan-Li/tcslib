<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.clonedLongCode_value_eq_boundedLongCodeValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cloned and bounded values agree

**Claim.** The value of the cloned long-code experiment equals the average, over vertices, of the tester’s acceptance probability on the bounded functions obtained by averaging each vertex-query sign over its clones.

**Proof.** First use the clone-value identity (`FABL.WeightedConstraintExperiment.clone_value_eq_randomizedCloneMean`): averaging over the clone choices in each constraint is equivalent to evaluating the predicate on independent signs whose means are the corresponding clone averages. For the long-code experiment, each such average is the clone mean at the vertex-query pair selected by that sample; these means lie in $[-1,1]$ (`FABL.WeightedConstraintExperiment.cloneMean_mem_Icc`), as required for the randomized predicate value. Now expand the experiment’s sampling law: it chooses a uniform vertex, then a tester seed, then independent uniform neighbors for the query positions. The expectation-of-a-bind identity (`FABL.pmfExpectation_bind`) separates these stages, and expectation under a uniform law is the finite average (`FABL.pmfExpectation_uniformPMF_eq_expect`). After fixing a vertex and seed, mapping each neighbor tuple to its selected queries gives the operational check value for the clone-mean table. By `FABL.RegularUniqueGame.boundedOperationalCheckValue_eq_randomizedValue`, this is the tester check’s randomized value on the vertex’s bounded averaged-neighbor function. Averaging over seeds is the tester’s acceptance probability, and then averaging over vertices gives exactly the bounded long-code value.

**Key facts.** `FABL.WeightedConstraintExperiment.clone_value_eq_randomizedCloneMean`, `FABL.WeightedConstraintExperiment.cloneMean_mem_Icc`, `FABL.pmfExpectation_bind`, `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.RegularUniqueGame.boundedOperationalCheckValue_eq_randomizedValue`.
