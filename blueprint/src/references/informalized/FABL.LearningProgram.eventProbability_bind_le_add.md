<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/Program.lean :: FABL.LearningProgram.eventProbability_bind_le_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sequential failure probability bound

**Claim.** If the first program’s output satisfies the first bad predicate with probability at most $\delta_1$, and every continuation from a first output that is not bad has final bad-event probability at most $\delta_2$, then binding the first program to the continuations has final bad-event probability at most $\delta_1+\delta_2$.

**Proof.** First pass from real probabilities to outer probabilities: since each event has finite outer probability, its outer probability is at most the corresponding nonnegative real bound viewed in the extended nonnegative reals. This follows from the conversion between an outer probability and its real value (\texttt{outerEventProbability\_toReal}), together with finiteness (\texttt{outerEventProbability\_ne\_top}). Apply the extended-real sequential bound: for a program bind, if the first-stage bad event has outer probability at most $\delta_1$ and, conditional on each nonbad first output, the continuation’s final bad event has outer probability at most $\delta_2$, then the bound for the combined program is at most $\delta_1+\delta_2$ (\texttt{outerEventProbability\_bind\_le\_add}). Finally, the extended-real sum of the two bounds is the real sum viewed as an extended real, because both bounds are nonnegative. Monotonicity of the map to real numbers then gives the stated real probability inequality.

**Key facts.** `FABL.LearningProgram.outerEventProbability_ne_top`, `FABL.LearningProgram.outerEventProbability_toReal`, `FABL.LearningProgram.outerEventProbability_bind_le_add`.
