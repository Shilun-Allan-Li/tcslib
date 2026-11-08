<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkCover.lean :: Randomized.RegularMultigraph.exists_even_word -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Short Even-Length Walk

**Claim.** In a finite connected regular multigraph that is not bipartite, any two vertices are joined by an even-length neighbor-slot walk of length strictly less than $2|V|$.

**Proof.** The lifted reachability result ($\texttt{cover\_reach}$) gives a path in the two-sheeted graph from $(u,\mathrm{false})$ to $(v,\mathrm{false})$. Regard the lifted relation as adjacency in its associated simple graph; each lifted edge has distinct endpoints because it flips the Boolean label. The resulting reachable pair has a simple path no longer than the number of vertices of the lift minus one, hence length strictly less than $2|V|$. Convert this path to a list of neighbor slots using the walk-to-word correspondence ($\texttt{word\_of\_walk}$). That correspondence also says the terminal Boolean label is the initial label flipped according to the parity of the path length. Since both labels are false, the path length, and therefore the word length, is even.

**Key facts.** `Randomized.RegularMultigraph.cover_reach`, `Randomized.RegularMultigraph.word_of_walk`.
