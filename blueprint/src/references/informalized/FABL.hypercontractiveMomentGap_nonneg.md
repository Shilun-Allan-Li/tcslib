<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveNecessity.lean :: FABL.hypercontractiveMomentGap_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative hypercontractive moment gap

**Claim.** If $X$ is $(p,q,\rho)$-hypercontractive and both affine factors $1+tX$ and $1+\rho tX$ are positive everywhere, then the hypercontractive moment gap at $t$ is nonnegative.

**Proof.** Apply hypercontractivity with the affine parameters $a=1$ and $b=t$. The conversion from extended-norm notation identifies this with the inequality between the ordinary uniform norms of $1+\rho tX$ at exponent $q$ and $1+tX$ at exponent $p$ (`uniformLpNormENNReal_coe`). Raise both nonnegative sides to the positive power $pq$; monotonicity of real powers preserves the inequality. For each function, the identity expressing the $r$th power of its uniform $r$-norm as the average of its absolute values to the $r$th power (`uniformLpNorm_rpow`) then turns the powered inequality into a comparison of affine moments. Positivity of the affine factors lets us remove the absolute values, by the affine-moment/absolute-moment identity (`affineMoment_eq_absMoment`). The resulting comparison is exactly that the order-$q$ affine moment with coefficient $1$, raised to $p$, is at least the order-$p$ affine moment with coefficient $\rho$, raised to $q$. Rearranging gives the asserted nonnegativity.

**Key facts.** `FABL.uniformLpNormENNReal_coe`, `FABL.uniformLpNorm_rpow`, `FABL.affineMoment_eq_absMoment`.
