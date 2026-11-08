<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/HammingBallLimit.lean :: FABL.expect_normalizedRademacherSum_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of the Normalized Sign Sum

**Claim.** For every $n$, the uniform average of the normalized coordinate sum on the sign cube is zero.

**Proof.** Negation preserves the uniform average, so the average of $R_n(-x)$ equals the average of $R_n(x)$. But $R_n(-x)=-R_n(x)$ (\texttt{FABL.normalizedRademacherSum\_neg}). Thus the mean equals its own negative, and therefore is zero.

**Key facts.** `FABL.normalizedRademacherSum_neg`.
