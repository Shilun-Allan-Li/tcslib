<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalk.lean :: Randomized.RegularMultigraph.reflTransGen_of_hits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Hit Implies Reachability

**Claim.** If a finite sequence of neighbor indices followed from $s$ visits $t$, including a possible visit at the starting vertex, then there is a finite adjacency path from $s$ to $t$.

**Proof.** Induct on the sequence of neighbor indices. For the empty sequence, a hit means $s=t$, so the reflexive adjacency path suffices. For a nonempty sequence beginning with index $i$, a hit occurs either immediately, in which case again $s=t$ and reflexivity applies, or later along the walk starting at $G.nbr(s,i)$. In the latter case, the first step is an adjacency from $s$ to that neighbor, and the induction hypothesis supplies a finite adjacency path from there to $t$. Composing the first adjacency with that path gives the required finite path.
