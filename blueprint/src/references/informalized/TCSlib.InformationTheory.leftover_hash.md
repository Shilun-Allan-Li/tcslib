<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/InformationTheory/LeftoverHash.lean :: TCSlib.InformationTheory.leftover_hash -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Leftover Hash Bound

**Claim.** For a universal family and an input distribution whose point probabilities are bounded by $2^{-k}$, the statistical distance between the hashed pair distribution and uniform on $S\times\beta$ is at most $\frac12\sqrt{|\beta|2^{-k}}$.

**Proof.** First, the statistical distance of any distribution $P$ from uniform is at most $\frac12\sqrt{|S\times\beta|\,\mathrm{collision}(P)-1}$ (the uniform-distance collision bound, `TCSlib.InformationTheory.statDist_uniform_le_sqrt`). Apply this to the hashed pair distribution. Universality bounds its collision probability by $|S|^{-1}(\mathrm{collision}(X)+|\beta|^{-1})$ (`TCSlib.InformationTheory.collision_hashPair_le`). Multiplying by $|S||\beta|$ and subtracting $1$ therefore bounds the expression under the square root by $|\beta|\mathrm{collision}(X)$. The min-entropy hypothesis gives $\mathrm{collision}(X)\le 2^{-k}$ (`TCSlib.InformationTheory.FinDist.collision_le_of_hasMinEntropy`). Substitution into the square-root bound yields the result.

**Key facts.** `TCSlib.InformationTheory.statDist_uniform_le_sqrt`, `TCSlib.InformationTheory.collision_hashPair_le`, `TCSlib.InformationTheory.FinDist.collision_le_of_hasMinEntropy`.
