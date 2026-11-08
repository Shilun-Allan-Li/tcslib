<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixing.lean :: Randomized.RegularMultigraph.uniform_isStationary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Stationarity

**Claim.** For a finite regular multigraph of positive degree, the uniform distribution on the vertices is stationary for the one-step random walk.

**Proof.** Evaluate the stationarity identity at an arbitrary vertex $v$. By the one-step transition formula (`transProb_one`), the resulting walk distribution is the sum over starting vertices $u$ of the uniform mass $1/|V|$ times the one-step transition probability, which is the multiplicity of the edge from $u$ to $v$ divided by $D$. The uniform stationarity identity for a regular multigraph (`uniform_stationary`) says this sum equals $1/|V|$. Since this holds at each vertex, the two distributions agree.

**Key facts.** `Randomized.RegularMultigraph.transProb_one`, `Randomized.RegularMultigraph.uniform_stationary`.
