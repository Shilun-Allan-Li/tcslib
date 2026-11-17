<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/AffineKhintchine.lean :: BooleanAnalysis.ThresholdFunctions.affine_influence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence Identity for Degree-One Polynomials

**Claim.** If a real coefficient family $p$ on subsets of $\{0,\ldots,n-1\}$ vanishes whenever $|S|>1$, then its Walsh polynomial satisfies $I[P]+p(\varnothing)^2=\sum_S p(S)^2$.

**Proof.** The total influence of a function equals the sum of its squared Fourier coefficients weighted by set size (BooleanAnalysis.totalInfluence_eq_sum_sq_deg). For the Walsh polynomial of $p$, this gives the sum of $|S|p(S)^2$ over all subsets. Add the constant coefficient squared, and combine the two sums term by term. If $S=\varnothing$, the added term contributes $p(S)^2$; if $|S|=1$, the influence weight already contributes $p(S)^2$; and if $|S|>1$, the degree assumption makes $p(S)=0$. Thus each term agrees with $p(S)^2$, proving the identity.

**Key facts.** `BooleanAnalysis.totalInfluence_eq_sum_sq_deg`.
