<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedFriedgut.lean :: FABL.improvedFriedgutThreshold_lower -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower Bound for the Threshold

**Claim.** Under the stated hypotheses, $(\epsilon/T(f))^{1+\eta}(\rho(\eta)^k)^2\le\Theta(f,\epsilon,\eta,k)$.

**Proof.** Write $x=\rho(\eta)^k$. Positivity of $\rho(\eta)$ (`improvedFriedgutRho_pos`) gives $x>0$, and the bound $\rho(\eta)\le1$ (`improvedFriedgutRho_le_one`) gives $x\le1$. Since $\eta\le1$, we have $1+\eta\le2$. For a positive base at most one, increasing the exponent can only decrease its real power; hence $x^2\le x^{1+\eta}$. The natural square agrees with the real power of exponent $2$. By the product law for real powers, the threshold is $(\epsilon/T(f))^{1+\eta}x^{1+\eta}$. Its first factor is nonnegative, since $\epsilon>0$ and $T(f)>0$. Multiplying the power inequality by this factor preserves the inequality and gives the claim.

**Key facts.** `FABL.improvedFriedgutRho_le_one`, `FABL.improvedFriedgutRho_pos`.
