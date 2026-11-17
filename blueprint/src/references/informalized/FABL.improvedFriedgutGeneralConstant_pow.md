<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedFriedgut.lean :: FABL.improvedFriedgutGeneralConstant_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Powers of the General Constant

**Claim.** For every real number $\eta>0$ and natural number $k$, if $\rho(\eta)=\eta/(2+\eta)$ and $C(\eta)=(2/\eta+1)^{1+\eta}$, then $C(\eta)^k=(\rho(\eta)^{-k})^{1+\eta}$.

**Proof.** Set $\rho=\rho(\eta)$ and $a=1+\eta$. By the identity expressing the general constant as a power of the reciprocal of rho (`improvedFriedgutGeneralConstant_eq_inv_rho_rpow`), the left side becomes $(\rho^{-a})^k$. Positivity of $\rho$ (`improvedFriedgutRho_pos`) ensures $\rho^{-1}\ge 0$, so the laws for real powers convert the natural power on the left to exponent multiplication, and convert $\rho^{-k}$ on the right likewise. The resulting exponents are $ak$ and $ka$, which agree, proving the equality.

**Key facts.** `FABL.improvedFriedgutRho_pos`, `FABL.improvedFriedgutGeneralConstant_eq_inv_rho_rpow`.
