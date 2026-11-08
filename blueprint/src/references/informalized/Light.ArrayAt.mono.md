<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/ArrayAt.lean :: Light.ArrayAt.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Array Bounds and Endpoint

**Claim.** If a list satisfies the array conditions with bound $U$ and endpoint $\mathrm{top}$, then for any $U'\ge U$ and $\mathrm{top}'\ge\mathrm{top}$ it satisfies them with bound $U'$ and endpoint $\mathrm{top}'$.

**Proof.** Keep the list length and segment conditions unchanged. For each entry, its absolute value is at most $U$, hence at most $U'$ by transitivity of the order. Likewise, $a+N\le\mathrm{top}\le\mathrm{top}'$. These are exactly the new bound and endpoint conditions.
