<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/Program.lean :: FABL.LearningProgram.eventProbability_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of event probability

**Claim.** If every outcome in one event also belongs to a second event, then the first event’s probability is at most the second event’s probability.

**Proof.** The inclusion of events implies the same inclusion of their sets of outcomes. By monotonicity of the outer measure of the program’s outcome law, the first outer probability is at most the second. The second outer probability is finite (\texttt{outerEventProbability\_ne\_top}), so taking real values preserves this inequality and gives the result.

**Key facts.** `FABL.LearningProgram.outerEventProbability_ne_top`.
