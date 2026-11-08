<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixing.lean :: Randomized.RegularMultigraph.exists_uniformExcess_walkDist_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Excess Contraction

**Claim.** For a finite nonempty connected, nonbipartite regular multigraph of positive degree, some fixed walk length contracts the uniform excess of every probability distribution by the stated factor.

**Proof.** An auxiliary estimate ($\texttt{uniformExcess\_walkDist\_two\_mul\_le\_aux}$) gives a block length $2n$ and contraction factor $1-n\delta$, where $n=|V|$ and $\delta=D^{-2n}>0$. If $n=1$, the unique probability distribution is uniform, and taking length zero proves the claim. If $n>1$, the desired factor $1-n^{-10n}$ is positive, while $1-n\delta<1$. Choose $m$ large enough that $(1-n\delta)^m\le1-n^{-10n}$. Iterating the block estimate via ($\texttt{uniformExcess\_walkDist\_mul\_le}$) at length $m(2n)$ gives the bound with factor $(1-n\delta)^m$. Uniform excess is nonnegative for a probability distribution ($\texttt{uniformExcess\_nonneg}$), so replacing this factor by the larger target factor preserves the inequality.

**Key facts.** `Randomized.RegularMultigraph.uniformExcess_walkDist_two_mul_le_aux`, `Randomized.RegularMultigraph.uniformExcess_walkDist_mul_le`, `Randomized.RegularMultigraph.walkDist_zero`, `Randomized.uniformExcess_nonneg`.
