<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHard.lean :: Complexity.PathHard.two_pow_ell_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power Bound from Binary Length

**Claim.** For every natural number $m$, if $\ell(m)$ is the length of the binary expansion of $m+1$, then $2^{\ell(m)}\le 2(m+1)$.

**Proof.** The binary length of a positive integer equals its natural-number size, so replace $\ell(m)$ by $\operatorname{size}(m+1)$. This size is positive. By the defining lower-bound property of size, $m+1$ cannot be strictly less than $2^{\operatorname{size}(m+1)-1}$. Also, since the size is positive, $2^{\operatorname{size}(m+1)}=2\cdot 2^{\operatorname{size}(m+1)-1}$. Combining these facts gives $2^{\operatorname{size}(m+1)}\le 2(m+1)$, as required.

**Key facts.** `Complexity.PathHard.ell_eq_size`.
