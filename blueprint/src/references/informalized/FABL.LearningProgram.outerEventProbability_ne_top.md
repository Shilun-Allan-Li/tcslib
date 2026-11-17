<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/Program.lean :: FABL.LearningProgram.outerEventProbability_ne_top -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite outer probability of an event

**Claim.** For every learning program, target Boolean function, and event on outcomes with costs, the event’s outer probability is not infinite.

**Proof.** The event is contained in the whole outcome space, so monotonicity of outer measure bounds its outer probability by the outer measure of the whole space. The outcome law is a probability mass function, whose associated outer measure assigns mass $1$ to the whole space. Since $1$ is finite, the event’s outer probability cannot be infinite.
