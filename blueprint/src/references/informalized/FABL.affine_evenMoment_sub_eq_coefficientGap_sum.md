<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveMomentSharpness.lean :: FABL.affine_evenMoment_sub_eq_coefficientGap_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine even-moment coefficient expansion

**Claim.** When the odd moments through order $2r-1$ vanish, the difference between the affine even moment with scale $\sigma_r$ and $(1+t^2)^r$ equals the sum of the coefficient gaps weighted by $t^{2l}$.

**Proof.** The affine expansion under vanishing odd moments ($\texttt{pmfExpectation_affine_evenMoment_of_oddMoments}$) expresses the first expectation as the sum, for $0\le l\le r$, of $\binom{2r}{2l}\sigma_r^{2l}t^{2l}\mathbb E[X^{2l}]$. The binomial theorem likewise writes $(1+t^2)^r$ as the sum of $\binom rl t^{2l}$. Subtract the sums term by term and factor out $t^{2l}$ in each summand. The remaining coefficient is precisely $\Delta_{r,l}(\mu,X)$, proving the identity.

**Key facts.** `FABL.pmfExpectation_affine_evenMoment_of_oddMoments`.
