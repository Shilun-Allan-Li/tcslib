<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/InvarianceTruncation.lean :: BooleanAnalysis.GaussianSpace.Invariance.invariance_cutoff_exp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential Cutoff Identity

**Claim.** For every real $\varepsilon>0$ and real $\delta$, the exponential involving $\log(1/\varepsilon)$ equals $\varepsilon^{\delta/3}$.

**Proof.** For positive $\varepsilon$, real powers satisfy $\varepsilon^u=\exp(u\log\varepsilon)$. Also, $\log(1/\varepsilon)=-\log\varepsilon$. Substituting these identities makes the exponent on the left $(-\delta)(-\log\varepsilon)/3=(\delta/3)\log\varepsilon$, which is exactly the exponent defining $\varepsilon^{\delta/3}$.
