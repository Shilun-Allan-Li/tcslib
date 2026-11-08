<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clGroups_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the clause-group list

**Claim.** For all natural numbers $n,k,T$ and all choices of the clause-group generators, the group list has length $n+(k+3)T+k+2$.

**Proof.** Expand the group list into its concatenated parts. The ranges for the pinning, state, input, work, and acceptance groups have lengths $n$, $T$, $T+1$, and $k(T+1)$, and $T$, respectively; the initial group contributes one. Adding these gives $n+1+T+(T+1)+k(T+1)+T=n+(k+3)T+k+2$. This is the stated value of $\mathrm{clLastRound}(n,k,T)+1$.
