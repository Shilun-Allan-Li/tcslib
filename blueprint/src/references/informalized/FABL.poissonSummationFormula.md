<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/Restrictions.lean :: FABL.poissonSummationFormula -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Poisson Summation on the Boolean Cube

**Claim.** For a function $f:\mathbb F_2^n\to\mathbb R$, a subspace $H\le\mathbb F_2^n$, and $z\in\mathbb F_2^n$, the average of $f(h+z)$ over $h\in H$ equals $\sum_{\gamma\in H^\perp}\chi_\gamma(z)\widehat f(\gamma)$.

**Proof.** Apply the affine-subspace restriction formula: the average over $H$ of the restriction of $f$ to the translate by $z$ equals the sum over the perpendicular subspace $H^\perp$ of the character value at $z$ times the corresponding Fourier coefficient ($\texttt{expect\_affineSubspaceRestriction\_eq\_sum}$). Here the affine restriction at $h\in H$ is exactly $f(h+z)$, so the formula gives the claimed identity.

**Key facts.** `FABL.expect_affineSubspaceRestriction_eq_sum`.
