<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/Program.lean :: FABL.LearningProgram.outerEventProbability_bind_le_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bad-event bound for sequential programs

**Claim.** If the first program’s bad-event outer probability is at most $\delta_1$, and every continuation from a nonbad first output has final bad-event outer probability at most $\delta_2$, then the bound-event outer probability for the combined program is at most $\delta_1+\delta_2$.

**Proof.** The law of running the bound program is the bind of the first program’s outcome law with the continuation law, where the first outcome’s accumulated cost is added to the continuation’s cost. This identity is \texttt{runWithCost\_bind}. Apply the outer-measure bound for a bind: the final bad-event probability is at most the first-stage bad-event probability plus a uniform bound on the continuation event outside the first-stage bad set (\texttt{PMF.toOuterMeasure\_bind\_le\_add}). Adding the first outcome’s cost changes only the cost coordinate, not the output, so the preimage of the final bad-output event under this cost adjustment is exactly the same final bad-output event. Thus the assumed continuation bound applies to every first outcome outside the first bad set, completing the estimate.

**Key facts.** `FABL.LearningProgram.runWithCost_bind`, `FABL.PMF.toOuterMeasure_bind_le_add`.
