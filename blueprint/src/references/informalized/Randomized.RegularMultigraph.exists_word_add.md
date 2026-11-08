<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkCover.lean :: Randomized.RegularMultigraph.exists_word_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lengthening a Walk by Even Steps

**Claim.** For a regular multigraph of positive degree, any walk between two vertices can be lengthened by $2m$ neighbor choices for every natural number $m$, without changing its endpoint.

**Proof.** Proceed by induction on $m$. For $m=0$, keep the original list. For the successor step, first use the induction hypothesis to obtain a list with the same endpoint and length increased by $2m$. Choose any neighbor slot, which exists because the degree is positive. By symmetry of adjacency ($\texttt{adj\_symm}$), there is a slot taking that neighbor back to the current endpoint. Append these two choices. The endpoint remains unchanged, and the length increases by two; the endpoint calculation uses the concatenation rule ($\texttt{endpoint\_append}$).

**Key facts.** `Randomized.RegularMultigraph.adj_symm`, `Randomized.RegularMultigraph.endpoint_append`.
