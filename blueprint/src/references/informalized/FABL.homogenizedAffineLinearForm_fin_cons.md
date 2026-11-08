<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdLevelOne.lean :: FABL.homogenizedAffineLinearForm_fin_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Homogenized form on a cons vector

**Claim.** Evaluating the homogenized affine form on the vector obtained by adjoining $b$ before $x$ gives $a_0b$ plus the linear form with coefficients $a$ evaluated at $x$.

**Proof.** Apply the cons formula for a linear form (FABL.linearForm_fin_cons) to the coefficient vector obtained by adjoining $a_0$ before $a$. Its first coefficient is $a_0$, and its successive coefficients are exactly those of $a$. Thus the first-coordinate contribution is $a_0$ times the sign value of $b$, while the remaining contribution is the linear form with coefficients $a$ evaluated at $x$.

**Key facts.** `FABL.linearForm_fin_cons`.
