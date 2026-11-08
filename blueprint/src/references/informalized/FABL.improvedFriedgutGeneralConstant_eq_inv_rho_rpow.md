<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedFriedgut.lean :: FABL.improvedFriedgutGeneralConstant_eq_inv_rho_rpow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# General Constant and Rho

**Claim.** For every real number $\eta>0$, with $\rho(\eta)=\eta/(2+\eta)$ and $C(\eta)=(2/\eta+1)^{1+\eta}$, one has $C(\eta)=\rho(\eta)^{-(1+\eta)}$.

**Proof.** The reciprocal identity $2/\eta+1=\rho(\eta)^{-1}$ holds for $\eta>0$ (the theorem `two_div_eta_add_one_eq_inv_improvedFriedgutRho`). Raising both equal positive bases to the real exponent $1+\eta$ gives the desired equality by the definitions of $C$ and $\rho$.

**Key facts.** `FABL.two_div_eta_add_one_eq_inv_improvedFriedgutRho`.
