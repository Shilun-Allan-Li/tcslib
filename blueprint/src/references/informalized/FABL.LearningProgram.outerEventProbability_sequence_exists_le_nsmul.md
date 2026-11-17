<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/Program.lean :: FABL.LearningProgram.outerEventProbability_sequence_exists_le_nsmul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Union Bound for Program Sequences

**Claim.** If every program in a finite list has outer probability at most $\delta$ of producing a bad output, then the outer probability that the sequence produces a list containing a bad output is at most the list length times $\delta$.

**Proof.** Proceed by induction on the list. For the empty list the sequence returns the empty list, so the event is empty and its outer probability is zero. For a list with first program $P$ and remaining list $R$, split according to whether the output of $P$ is bad. The outer probability of the final bad event is at most the sum of the probability that $P$ is bad and the probability of a bad tail when the head is not bad, by the bound for binding programs (`outerEventProbability_bind_le_add`). The first term is at most $\delta$ by hypothesis. If the head is not bad, placing it before the tail does not change whether the resulting list contains a bad item (`outerEventProbability_map_cons_exists`); the induction hypothesis bounds this tail event by $|R|\delta$, since every program in $R$ satisfies the original hypothesis. Adding these bounds gives $\delta+|R|\delta=(|R|+1)\delta$, the required bound.

**Key facts.** `FABL.LearningProgram.outerEventProbability_bind_le_add`, `FABL.LearningProgram.outerEventProbability_map_cons_exists`.
