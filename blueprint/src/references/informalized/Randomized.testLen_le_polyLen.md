<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Fingerprint.lean :: Randomized.testLen_le_polyLen -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial bound on testing length

**Claim.** For a finite algebraic circuit $c$ with $n$ input variables, encoded by a binary word of length $L$, and any natural number $m$, the testing length satisfies $n(m+4)+16(m+12)^2\le 2400(L+1)^2$.

**Proof.** Let $N$ be the encoding length. The circuit encoding bound gives $n+\mathrm{size}(c)<N$, so in particular $n\le N$ and $\mathrm{size}(c)\le N$. Apply the general estimate `testLen_le_polyLen_of_le` with these two bounds to obtain $\mathrm{testLen}(n,\mathrm{size}(c))\le 2400(N+1)^2$. Since $N$ is the length of the encoding, this is the asserted inequality.

**Key facts.** `Randomized.AlgCircuit.lt_length_encode`, `Randomized.testLen_le_polyLen_of_le`.
