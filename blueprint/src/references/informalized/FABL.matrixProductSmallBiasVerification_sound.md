<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixProductVerification.lean :: FABL.matrixProductSmallBiasVerification_sound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Soundness of seeded matrix verification

**Claim.** If $C'\ne AB$ and the input bias is at most $1/3$, then the seeded matrix-product verification accepts with probability at most $2/3$.

**Proof.** The seed distribution is biased with parameter $\varepsilon$ by (\texttt{FABL.matrixProductSmallBiasSeed_isBiased}). The soundness bound for a biased seed says that, when $C'\ne AB$, acceptance probability is at most $(1+\varepsilon)/2$ (\texttt{FABL.seededMatrixProductVerificationAcceptanceProbability_le}). Since $\varepsilon\le1/3$, this is at most $(1+1/3)/2=2/3$.

**Key facts.** `FABL.matrixProductSmallBiasSeed_isBiased`, `FABL.seededMatrixProductVerificationAcceptanceProbability_le`.
