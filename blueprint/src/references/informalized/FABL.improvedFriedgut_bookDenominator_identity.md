<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedFriedgut.lean :: FABL.improvedFriedgut_bookDenominator_identity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Junta size denominator identity

**Claim.** For positive total influence, the quotient of the influence by $(\epsilon/I(f))^{1+\eta}(\rho^k)^2$ equals the stated junta size term.

**Proof.** Set $I=I(f)$, $\rho=\eta/(2+\eta)$, and $a=1+\eta$. Both $I$ and $\rho$ are positive, the latter by `improvedFriedgutRho_pos`. Hence the powers needed below are nonzero, and the denominator $(\epsilon/I)^a(\rho^k)^2$ is positive. First, since $a+1=2+\eta$, the addition law for real powers gives $I^{2+\eta}=I\,I^a$. Next, the constant identity `improvedFriedgutConstant_eq_inv_rho_sq` says that the constant is $\rho^{-2}$; thus its $k$th power cancels $(\rho^k)^2$, since $(\rho^{-2})^k(\rho^k)^2=1$. Finally, expand $(\epsilon/I)^a$ using the quotient law for real powers and substitute $I^{2+\eta}=I I^a$. Clearing the positive denominator reduces the desired equality to the cancellation just established, yielding the junta size term.

**Key facts.** `FABL.improvedFriedgutRho_pos`, `FABL.improvedFriedgutConstant_eq_inv_rho_sq`.
