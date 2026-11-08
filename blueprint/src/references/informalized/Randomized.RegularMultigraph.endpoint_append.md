<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkCover.lean :: Randomized.RegularMultigraph.endpoint_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Endpoint of Concatenated Walks

**Claim.** Following a concatenation of two lists of neighbor-slot choices has the same endpoint as following the first list and then following the second from the resulting vertex.

**Proof.** Induct on the first list, allowing the starting vertex to vary. For the empty list, concatenation leaves the second list unchanged, so the claim is immediate. If the first list begins with a slot $i$ and remainder $w$, both sides first move from $v$ to its $i$th neighbor; the induction hypothesis applied at that neighbor identifies the endpoints after the remaining choices.
