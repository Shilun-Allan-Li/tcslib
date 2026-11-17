<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedFriedgut.lean :: FABL.improvedFriedgutConstant_eq_inv_rho_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Friedgut Constant and Rho

**Claim.** For every real number $\eta>0$, with $\rho(\eta)=\eta/(2+\eta)$ and $C(\eta)=(2/\eta+1)^2$, one has $C(\eta)=\rho(\eta)^{-2}$.

**Proof.** Since $\eta>0$, both $\eta$ and $2+\eta$ are nonzero. The definitions reduce the claim to the algebraic identity $(2/\eta+1)^2=((\eta/(2+\eta))^{-1})^2$. Clearing the nonzero denominators verifies this identity.
