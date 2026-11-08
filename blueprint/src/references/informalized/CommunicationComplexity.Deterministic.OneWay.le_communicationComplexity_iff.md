<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/OneWay.lean :: CommunicationComplexity.Deterministic.OneWay.le_communicationComplexity_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization by Protocol Costs

**Claim.** For a function $f$ and natural number $k$, $k$ is at most the one-way deterministic communication complexity of $f$ in $\mathbb{N}_\infty$ exactly when every one-way deterministic protocol computing $f$ has bit cost at least $k$.

**Proof.** The one-way complexity is the infimum, in $\mathbb{N}_\infty$, of the costs of all protocols that compute $f$. An element is below this infimum exactly when it is below every member of the indexed family. Applying this characterization to $k$ and the family of computing protocols says precisely that each such protocol has cost at least $k$; the natural-number cast preserves this inequality.
