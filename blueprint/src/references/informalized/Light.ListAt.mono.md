<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/ArrayAt.lean :: Light.ListAt.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the Upper Bound

**Claim.** If a list records a segment starting at $a$ of length $N$ and its endpoint is at most $\mathrm{top}$, then it also satisfies the endpoint bound for every $\mathrm{top}'\ge\mathrm{top}$.

**Proof.** Retain the list length and the recorded segment. The endpoint inequality $a+N\le\mathrm{top}$, followed by $\mathrm{top}\le\mathrm{top}'$, gives $a+N\le\mathrm{top}'$.
