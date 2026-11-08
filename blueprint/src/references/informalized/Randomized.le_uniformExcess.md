<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixing.lean :: Randomized.le_uniformExcess -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Excess Bound

**Claim.** For a finite nonempty set $V$, a function $p:V\to\mathbb Q$, and any $i\in V$, the value $p(i)-1/|V|$ is at most the maximum of $p(v)-1/|V|$ over $v\in V$.

**Proof.** The value at $i$ is one of the values being maximized, since $i$ belongs to $V$. A maximum of a finite nonempty collection is at least each member of that collection, so $p(i)-1/|V|\le \max_{v\in V}(p(v)-1/|V|)$.
