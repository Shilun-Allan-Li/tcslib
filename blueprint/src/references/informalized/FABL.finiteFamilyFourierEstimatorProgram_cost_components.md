<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/FiniteFamily.lean :: FABL.finiteFamilyFourierEstimatorProgram_cost_components -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Estimator program cost components

**Claim.** Every outcome in the estimator program's output-and-cost distribution has $|\mathcal{F}|M$ random examples, zero queries, and work $|\mathcal{F}|M+|\mathcal{F}|M(n+1)$, where $M$ is the prescribed sample count per coefficient.

**Proof.** The exact-cost result identifies the cost of every supported outcome as the triple $(|\mathcal{F}|M,0,|\mathcal{F}|M+|\mathcal{F}|M(n+1))$. Reading off the three coordinates gives the stated random-example count, query count, and work.

**Key facts.** `FABL.finiteFamilyFourierEstimatorProgram_cost_eq`.
