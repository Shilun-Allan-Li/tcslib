<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPoly.lean :: Randomized.PolyAmp.bigK_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower Bound for the Amplification Parameter

**Claim.** If $d+5\le F$, then $32(n+1)^d\le 2^{F\ell(n)}$, where $\ell(n)$ is one more than the length of the binary representation of $n$.

**Proof.** The binary-length bound $n<2^{|\mathrm{bits}(n)|}$ implies $n+1\le 2^{\ell(n)}$ (`lt_two_pow_bits`). Also $2\le 2^{\ell(n)}$, since $\ell(n)$ is at least one. Raising these inequalities to powers gives $(n+1)^d\le (2^{\ell(n)})^d$ and $32=2^5\le (2^{\ell(n)})^5$. Multiplying yields $32(n+1)^d\le (2^{\ell(n)})^{d+5}=2^{(d+5)\ell(n)}$. Finally, $d+5\le F$ implies $(d+5)\ell(n)\le F\ell(n)$; monotonicity of powers of $2$ gives the desired bound.

**Key facts.** `Randomized.PolyAmp.lt_two_pow_bits`.
