<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearningAlgorithm.lean :: FABL.one_le_eventProbability_add_of_output_cover -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability bound from an output cover

**Claim.** If every possible output satisfies at least one of properties $A$ and $B$, then the probabilities of $A$ and $B$ for the program's output sum to at least one.

**Proof.** Let the program's output law be the probability mass function induced by its execution, and let $E_A,E_B$ be the events that the output satisfies $A,B$, respectively. The cover assumption says the whole outcome space is contained in $E_A\cup E_B$. The law assigns mass one to the whole space, so monotonicity and the union bound give $1\le\Pr(E_A\cup E_B)\le\Pr(E_A)+\Pr(E_B)$. The event masses are finite (`pmfToOuterMeasure_ne_top`), so converting the extended-real inequality to ordinary real probabilities preserves the inequality and gives the claim.

**Key facts.** `FABL.pmfToOuterMeasure_ne_top`.
