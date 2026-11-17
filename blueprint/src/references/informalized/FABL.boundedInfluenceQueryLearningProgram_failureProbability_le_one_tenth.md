<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequences.lean :: FABL.boundedInfluenceQueryLearningProgram_failureProbability_le_one_tenth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Failure Probability for Query Learning

**Claim.** For any Boolean target whose total influence is at most $t$, the bounded-influence query-learning program has failure probability at most one tenth at accuracy $\epsilon$.

**Proof.** Use the target itself as the initial Fourier family and set the size budget to the family bound determined by $t$ and $\epsilon$. The total-influence hypothesis ensures that this target family has size at most the budget (`card_learningConsequencesTargetFamily_le`). The same hypothesis ensures that the target's Fourier spectrum is concentrated on this family at threshold $\epsilon/4$ (`learningConsequencesTargetFamily_spectrum_concentrated`). The Kushilevitz–Mansour guarantee says that when the initial family meets the size budget and this concentration condition, the program fails with probability at most $1/10$ (`kushilevitzMansourProgramForBound_failureProbability_le_one_tenth`). Since the bounded-influence program is exactly this program with the specified family bound, the result follows.

**Key facts.** `FABL.card_learningConsequencesTargetFamily_le`, `FABL.learningConsequencesTargetFamily_spectrum_concentrated`, `FABL.kushilevitzMansourProgramForBound_failureProbability_le_one_tenth`.
