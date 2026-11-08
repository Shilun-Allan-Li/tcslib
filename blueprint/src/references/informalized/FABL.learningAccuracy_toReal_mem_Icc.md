<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/Program.lean :: FABL.learningAccuracy_toReal_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real interval for learning accuracy

**Claim.** If a rational learning accuracy lies in $[0,1/2]$, then its image in $[0,1/2]$ belongs to the same interval in $$.

**Proof.** The lower endpoint follows because casting a nonnegative rational to the reals preserves nonnegativity. The upper endpoint follows because the rational inequality $\varepsilon\le 1/2$ is preserved by the order-preserving rational-to-real map. Together these give membership in the real interval.
