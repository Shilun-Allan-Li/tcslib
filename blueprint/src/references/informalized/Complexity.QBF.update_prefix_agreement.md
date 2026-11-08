<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/QBF.lean :: Complexity.QBF.update_prefix_agreement -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preserving Agreement by Updating

**Claim.** If two assignments agree below $i$, updating the first at index $i$ to the second's value there makes them agree below $i+1$.

**Proof.** Take any $v<i+1$. If $v=i$, the update assigns exactly $\tau(i)$. Otherwise, the update leaves the value at $v$ unchanged, and $v<i$ follows from $v<i+1$ together with $v\ne i$. The original agreement hypothesis then gives equality with $\tau(v)$.
