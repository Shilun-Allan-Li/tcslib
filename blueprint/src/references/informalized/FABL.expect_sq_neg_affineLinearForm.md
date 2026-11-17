<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdLevelOne.lean :: FABL.expect_sq_neg_affineLinearForm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second moment under sign reversal

**Claim.** The uniform expectation of $(-a_0+L(x))^2$ equals that of $(a_0+L(x))^2$ on the sign cube.

**Proof.** Negation is a bijection of the sign cube, so changing variables by $x\mapsto -x$ preserves its uniform expectation. At each point, the linear form changes sign: $L(-x)=-L(x)$ (by `FABL.linearForm_neg_input`). Thus the transformed integrand is $(-a_0+L(-x))^2=(-a_0-L(x))^2=(a_0+L(x))^2$, as required.

**Key facts.** `FABL.linearForm_neg_input`.
