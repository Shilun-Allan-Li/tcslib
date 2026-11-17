<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenCorrect.lean :: Complexity.LogProg.ISGen.code_le_gKv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential Code Bound

**Claim.** If the machine's code bound is at most $E$, then $2^{\kappa(N)(s+\ell(|x|)+1)}\le 2^{2E v(|x|)+2Es}$.

**Proof.** The logarithmic-space estimate gives $\ell(|x|)\le v(|x|)$ (`logSpace_le_size_succ`). Consequently, $s+\ell(|x|)+1\le 2v(|x|)+2s$, by the definitions of $\ell$ and $v$ and elementary arithmetic. Combining this with $\kappa(N)\le E$ yields $\kappa(N)(s+\ell(|x|)+1)\le E(2v(|x|)+2s)=2E v(|x|)+2Es$. Since exponentiation with base $2$ is monotone in the natural-number exponent, the claimed inequality follows.

**Key facts.** `Complexity.LogProg.ISCount.logSpace_le_size_succ`.
