<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryMonicCoefficient_eq_coeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monic Polynomial Coefficient Formula

**Claim.** For every coefficient vector $m\in\mathbb{F}_2^\ell$ and every degree $d$, the coefficient of degree $d$ in its associated monic polynomial equals the specified binary monic coefficient.

**Proof.** Split into the three possibilities for $d$. If $d<\ell$, then $d\ne\ell$, so the specified coefficient is $m_d$. The low polynomial has coefficient $m_d$ in degree $d$, while $X^\ell$ contributes zero; thus the polynomial coefficient is also $m_d$. If $d=\ell$, the low polynomial contributes zero and $X^\ell$ contributes one, matching the specified coefficient. If $d>\ell$, both contributions are zero, again matching the specified coefficient. In each case the coefficient formula for the low polynomial (`coeff_binaryLowPolynomial`) gives the needed coefficient.

**Key facts.** `FABL.coeff_binaryLowPolynomial`.
