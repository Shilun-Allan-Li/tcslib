<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/KikuchiLDC/LDC/Decomposition.lean :: hypergraph_decomposition -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair-degree-bounded subhypergraphs

**Claim.** There are subhypergraphs of the given matchings that remain 3-uniform matchings and whose union has pair-degrees at most $d$.

**Proof.** Choose every subhypergraph to be empty. Each is contained in its corresponding matching. The empty hypergraph is 3-uniform vacuously, since it has no edges, and is a matching vacuously, since there are no pairs of distinct edges to check. Their union is empty, so every pair has degree zero, which is at most $d$.

**Caveat.** The proof source establishes the stated existential theorem using empty subhypergraphs. It does not carry out the greedy decomposition described in the informal statement.
