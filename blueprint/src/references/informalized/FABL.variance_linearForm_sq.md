<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/FKN.lean :: FABL.variance_linearForm_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance of a Squared Linear Form

**Claim.** For a linear form with coefficients $a_i$ on the sign cube, its square has variance equal to twice the difference between $(\sum_i a_i^2)^2$ and $\sum_i a_i^4$.

**Proof.** Write $A=\sum_i a_i^2$. The expected square of the linear form is $A$ (`expect_linearForm_sq`), so its mean is $A$. Expanding the squared deviation from this mean gives $L^4-2AL^2+A^2$, where $L$ denotes the linear form. Taking expectations and using the fourth-moment identity, $\mathbb E[L^4]=3A^2-2\sum_i a_i^4$ (`expect_linearForm_fourth`), together with $\mathbb E[L^2]=A$, gives variance $2A^2-2\sum_i a_i^4$. Dividing by two yields the claimed identity.

**Key facts.** `FABL.expect_linearForm_sq`, `FABL.expect_linearForm_fourth`.
