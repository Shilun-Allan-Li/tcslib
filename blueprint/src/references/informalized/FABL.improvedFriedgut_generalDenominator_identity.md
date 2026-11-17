<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedFriedgut.lean :: FABL.improvedFriedgut_generalDenominator_identity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# General denominator identity

**Claim.** For positive total influence, the total influence divided by the improved threshold equals the general junta size term.

**Proof.** Set $I=I(f)$, $\rho=\eta/(2+\eta)$, and $a=1+\eta$. Positivity of $I$ and of $\rho$ (from `improvedFriedgutRho_pos`) ensures that the relevant powers and denominators are positive. The general constant power identity (`improvedFriedgutGeneralConstant_pow`) expresses its $k$th power as $((\rho^{-1})^k)^a$. Since $(\rho^{-1})^k\rho^k=1$, the constant power cancels $(\rho^k)^a$. Also $I^{2+\eta}=I\,I^a$, because $2+\eta=1+a$. Expanding the threshold $(\epsilon/I\cdot\rho^k)^a$ by the real-power product and quotient laws, these two identities reduce the claimed equality to ordinary cancellation of the positive factors.

**Key facts.** `FABL.improvedFriedgutRho_pos`, `FABL.improvedFriedgutGeneralConstant_pow`.
