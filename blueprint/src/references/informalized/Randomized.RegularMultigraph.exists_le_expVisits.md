<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixing.lean :: Randomized.RegularMultigraph.exists_le_expVisits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Asymptotic Lower Bound on Expected Visits

**Claim.** For every pair of vertices, the expected number of visits to the target during a length-$N$ random walk from the starting vertex is eventually at least $N/(2|V|)$.

**Proof.** Write $n=|V|$ and start with the point mass $e$ at $u$. Its total mass is one and its uniform excess is at most one. The uniform-excess contraction result ($\texttt{exists\_uniformExcess\_walkDist\_le}$) supplies a block length $K$ that contracts excess by the factor $c=1-n^{-10n}<1$. Iterating this contraction, using mass preservation ($\texttt{sum\_walkDist}$), choose a number of blocks $m$ so that at time $M=mK$ the excess is at most $1/(4n^2)$. Additional steps cannot increase excess, by ($\texttt{uniformExcess\_walkDist\_le\_self}$) and the composition law ($\texttt{walkDist\_add}$). The pointwise lower bound in terms of excess ($\texttt{inv\_card\_sub\_le}$) then gives target probability at least $1/n-n\cdot1/(4n^2)=3/(4n)$ at every time at least $M$; the walk distribution from $e$ at time $j$ gives the transition probability from $u$ to $v$ ($\texttt{expVisits\_eq}$ identifies the visit expectation with the sum of these probabilities). Finally take $N\ge3M$ and split its first $M$ time steps from the remaining $d=N-M$. The first portion contributes nonnegatively, since transition probabilities are nonnegative ($\texttt{transProb\_nonneg}$); each of the remaining $d$ terms is at least $3/(4n)$. Since $d\ge2M$, this contribution is at least $N/(2n)$, as required.

**Key facts.** `Randomized.RegularMultigraph.exists_uniformExcess_walkDist_le`, `Randomized.RegularMultigraph.sum_walkDist`, `Randomized.RegularMultigraph.uniformExcess_walkDist_mul_le`, `Randomized.RegularMultigraph.uniformExcess_walkDist_le_self`, `Randomized.RegularMultigraph.walkDist_add`, `Randomized.inv_card_sub_le`, `Randomized.RegularMultigraph.expVisits_eq`, `Randomized.RegularMultigraph.transProb_nonneg`.
