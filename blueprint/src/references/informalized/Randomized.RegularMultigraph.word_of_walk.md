<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkCover.lean :: Randomized.RegularMultigraph.word_of_walk -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Words Representing Walks

**Claim.** Every walk in the two-layer graph determines a word of neighbor indices whose length is the walk length, whose endpoint in the original multigraph is the first coordinate of the walk's endpoint, and whose endpoint bit is the starting bit toggled according to the parity of the length.

**Proof.** Proceed by induction on the walk. For a walk of length zero, take the empty word: it leaves the vertex and bit unchanged. For a walk beginning with an edge from $x$ to $z$, apply the induction hypothesis to the remaining walk from $z$ to the endpoint, obtaining a word $w$ of the appropriate length. The first edge gives a neighbor index $i$ from the first coordinate of $x$ to that of $z$. Indeed, the edge relation supplies this directly in one orientation; in the reverse orientation, symmetry of the two-layer adjacency relation (`Randomized.RegularMultigraph.coverAdj_symm`) supplies it. Prefix $i$ to $w$. The endpoint recursion shows that this word reaches the required first coordinate, and its length is one more than the remaining walk's length. Each edge flips the bit, so adding the initial edge changes the parity; the endpoint bit is therefore the starting bit toggled precisely when the full walk length is odd.

**Key facts.** `Randomized.RegularMultigraph.coverAdj_symm`.
