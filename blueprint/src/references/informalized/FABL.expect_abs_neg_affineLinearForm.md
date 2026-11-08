<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdLevelOne.lean :: FABL.expect_abs_neg_affineLinearForm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry of affine sign-form moments

**Claim.** For a uniform sign vector, the expected absolute value of $-a_0+L(X)$ equals that of $a_0+L(X)$.

**Proof.** Negation is a bijection of the sign cube, so changing variables $X\mapsto -X$ preserves its uniform expectation. Under this change, the linear form changes sign (`linearForm_neg_input`), and the resulting expression $a_0-L(X)$ equals $-(-a_0+L(X))$. Absolute value is unchanged by an overall minus sign, giving the desired equality.

**Key facts.** `FABL.linearForm_neg_input`.
