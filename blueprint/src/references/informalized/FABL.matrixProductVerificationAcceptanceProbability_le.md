<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixProductVerification.lean :: FABL.matrixProductVerificationAcceptanceProbability_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance bound for biased verification

**Claim.** For a nonzero matrix discrepancy $C'\ne AB$, verification under an $\varepsilon$-biased input distribution accepts with probability at most $(1+\varepsilon)/2$.

**Proof.** Because $C'\ne AB$, some row of the difference matrix $C'-AB$ is nonzero (\texttt{FABL.exists_matrixProductDifferenceRow_ne_zero}); fix such a row. Whenever verification accepts, the dot product of this row with the sampled vector must be zero (\texttt{FABL.matrixProductVerificationPredicate_imp_row_dot_eq_zero}). Thus the acceptance indicator is bounded pointwise by the indicator that this nonzero row has zero dot product. Multiplying by the nonnegative density preserves the inequality, and averaging over vectors bounds acceptance probability by the probability that the row dot product vanishes. The Fourier-bias estimate for a nonzero row bounds that probability by $(1+\varepsilon)/2$ (\texttt{FABL.ProbabilityDensity.IsBiased.rowZeroProbability_le}).

**Key facts.** `FABL.exists_matrixProductDifferenceRow_ne_zero`, `FABL.matrixProductVerificationPredicate_imp_row_dot_eq_zero`, `FABL.ProbabilityDensity.IsBiased.rowZeroProbability_le`.
