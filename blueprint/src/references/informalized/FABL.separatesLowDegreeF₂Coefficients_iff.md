<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.separatesLowDegreeF₂Coefficients_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Separation by Nonzero Evaluations

**Claim.** Evaluation on the chosen inputs is injective on low-degree coefficient arrays exactly when every nonzero such array evaluates nontrivially on at least one chosen input.

**Proof.** For the forward implication, suppose evaluation is injective and take a nonzero coefficient array. If it evaluated to zero on every chosen input, its evaluations would agree everywhere with those of the zero array. Injectivity would then force the array itself to be zero, a contradiction. Conversely, assume every nonzero array has a nonzero evaluation somewhere, and suppose two arrays have equal evaluations on every chosen input. Their sum is nonzero if they are distinct: over $\mathbb F_2$, adding the sum of the two arrays to either one recovers the other. By linearity of evaluation in the coefficients (\texttt{lowDegreeF₂Eval\_add}), the sum evaluates to zero on every chosen input, contradicting the assumed property. Thus the arrays are equal, proving injectivity.

**Key facts.** `FABL.lowDegreeF₂Eval_add`.
