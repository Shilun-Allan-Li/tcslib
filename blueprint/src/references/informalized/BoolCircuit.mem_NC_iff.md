<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/NCAC.lean :: BoolCircuit.mem_NC_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in NC

**Claim.** A Boolean language belongs to $\mathrm{NC}$ exactly when, for some integer $i\ge 1$, it has a fan-in-two circuit family of polynomial size and depth bounded by a polynomial in $\log n+1$ of degree $i$.

**Proof.** Unfolding the definition of $\mathrm{NC}$, membership means that the language lies in the union of the classes $\mathrm{NCLevel}(i)$ for indices $i$ in $\mathrm{Ici}(1)$, that is, for $i\ge 1$. Membership in the $i$th level is precisely the assertion that the language is in $\mathrm{InNC}(i)$. Thus membership in the union is equivalent to the existence of an $i$ with $1\le i$ and $L\in\mathrm{InNC}(i)$, as claimed.
