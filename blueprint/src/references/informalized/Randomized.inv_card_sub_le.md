<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixing.lean :: Randomized.inv_card_sub_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower Bound from Uniform Excess

**Claim.** If $V$ is finite and nonempty and $p:V\to\mathbb{Q}$ has total sum $1$, then for every $v\in V$, $1/|V|-|V|\max_{u\in V}(p(u)-1/|V|)\le p(v)$.

**Proof.** Write $E$ for the uniform excess. Since the total mass is $1$, the sum over $V$ of $p(u)-1/|V|$ is zero (`Randomized.sum_sub_inv_card`). Separate the term at $v$ from this sum. For each remaining $w$, the definition of the maximum gives $p(w)-1/|V|\le E$ (`Randomized.le_uniformExcess`), so the sum over $V\setminus\{v\}$ is at most its cardinality times $E$. Since $E\ge0$ (`Randomized.uniformExcess_nonneg`), this is at most $|V|E$. Substituting into the zero-sum identity and rearranging yields $1/|V|-|V|E\le p(v)$.

**Key facts.** `Randomized.uniformExcess_nonneg`, `Randomized.sum_sub_inv_card`, `Randomized.le_uniformExcess`.
