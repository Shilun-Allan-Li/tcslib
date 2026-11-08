<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.lowDegreeJuntaRelevantCoordinateProgram_root_failureProbability_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Root relevant-coordinate failure bound

**Claim.** For a nonconstant $k$-junta, the program started at the root outputs a relevant coordinate except with probability at most the prescribed failure parameter.

**Proof.** Choose a support set $J$ witnessing that the target is a $k$-junta: it has size at most $k$, and the target depends only on coordinates in $J$. Apply the node failure bound with the empty fixed set and its unique assignment. This bounds the probability that the root decision is bad in the node-decision sense. The empty-node implication states that whenever the root-finder bad event occurs, the root decision is bad in that sense; it uses nonconstancy to rule out an incorrect constant answer. Monotonicity of event probability then bounds the root-finder failure event by the node-decision failure event, giving the claimed bound.

**Key facts.** `FABL.lowDegreeJuntaRelevantCoordinateProgram_failureProbability_le`, `FABL.juntaNodeDecision_isBad_empty_of_rootFinderBad`, `FABL.LearningProgram.eventProbability_mono`.
