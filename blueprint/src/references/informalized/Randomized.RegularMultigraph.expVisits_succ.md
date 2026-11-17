<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixing.lean :: Randomized.RegularMultigraph.expVisits_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected Visit Recursion

**Claim.** For a regular multigraph of degree $D>0$, the expected number of visits to $v$ in $N+1$ steps starting at $u$ is the average over the $D$ possible first edge indices of the indicator that the first step reaches $v$ plus the expected number of visits in the remaining $N$ steps from the resulting neighbor.

**Proof.** Represent a sequence of $N+1$ neighbor indices by its first index $i$ and its remaining sequence $w$. For each such pair, the visits split into the indicator that the first move from $u$ reaches $v$, plus the visits along the remaining sequence starting at $G.nbr(u,i)$. This is the defining recursion for visits. Summing over all pairs therefore separates into a sum over first indices and a sum over remaining sequences. For each fixed first index, the sum of the indicators over all remaining sequences contributes $D^N$ copies of that indicator, while the remaining-visit sum, divided by $D^N$, is the expected number of visits from that neighbor. Dividing the full sum by $D^{N+1}$ thus gives the sum over first indices of these two quantities, divided by $D$, as claimed. The assumption $D>0$ ensures the rational denominator is nonzero.
