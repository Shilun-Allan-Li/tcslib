<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/FiniteNoiseDuality.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.finite_noise_duality -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duality for Finite Noise Bounds

**Claim.** A quadratic noise bound at the conjugate exponent implies the stated $q$-moment bound for the centered affine noise transform.

**Proof.** Fix $f$, let $z_i=\rho f_i+(1-\rho)\sum_jw_jf_j$, and define the signed-power witness $g_i=z_i|z_i|^{q-2}$. Write $H_i=\rho g_i+(1-\rho)\sum_jw_jg_j$, and put $M=\sum_iw_i|z_i|^q$ and $A=\sum_iw_if_i^2$. The signed-power identities say both $z_ig_i=|z_i|^q$ and $|g_i|^{q/(q-1)}=|z_i|^q$. The finite-noise identities then identify the pairing $\sum_iw_if_iH_i$ with $M$, and identify $\sum_iw_iH_i^2$ with the quadratic noise form of $g$. Applying the assumed bound to $g$ and using the second signed-power identity gives $\sum_iw_iH_i^2\leq M^{2/p}$, where $p=q/(q-1)$. Weighted Cauchy–Schwarz applied to the pairing yields $M^2\leq A\sum_iw_iH_i^2$, hence $M^2\leq A M^{2/p}$. If $M=0$, the desired conclusion is immediate from $A\geq0$. Otherwise $M>0$, and the conjugate-exponent identity $2/q+2/p=2$ allows division by the positive $M^{2/p}$, giving $M^{2/q}\leq A$. This is the claimed inequality.

**Key facts.** `BooleanAnalysis.Hypercontractivity.SharpDiscrete.finite_noise_identities`, `BooleanAnalysis.Hypercontractivity.SharpDiscrete.signed_power_dual`.
