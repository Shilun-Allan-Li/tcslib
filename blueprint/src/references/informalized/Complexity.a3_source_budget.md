<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.a3_source_budget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Source bound from the split equation

**Claim.** If the exponential-split search with coefficient $1$, degree $c$, and length $m$ returns $n$, then $a\cdot 2^{n^c}\le a\cdot m$.

**Proof.** The split specification gives $n\le m$ and $n+2^{(n+1)^c}=m$ after simplifying the coefficient $1$ (Complexity.a3_split_spec). Since $n\le n+1$, monotonicity of natural-number powers, first in the base and then in the exponent, gives $2^{n^c}\le 2^{(n+1)^c}$. The split equation implies $2^{(n+1)^c}\le m$, hence $2^{n^c}\le m$. Multiplying this inequality by the nonnegative natural number $a$ yields the claim.

**Key facts.** `Complexity.a3_split_spec`.
