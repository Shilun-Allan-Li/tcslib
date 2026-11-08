<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/NPReductions/ThreeSATToClique.lean :: ThreeSATToClique.ThreeSAT_to_Clique_soundness -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Soundness of the reduction

**Claim.** If the conflict graph of a finite 3-CNF formula has a clique whose size is the number of clauses, then some truth assignment satisfies every clause.

**Proof.** Let $s$ be a clique with one vertex for each clause, as guaranteed by the one-vertex-per-clause result (ThreeSATToClique.clique_vertices_choose_one_per_clause). Define an assignment by declaring a variable true exactly when some vertex in $s$ selects its positive literal. A negative literal selected by a vertex in $s$ must then also evaluate to true: if that variable were assigned true, another vertex in $s$ would select its positive literal. This other vertex cannot be the same vertex, since a literal cannot be both positive and negative. The two distinct clique vertices would therefore be adjacent, contradicting that their literals conflict. Thus every literal selected by a vertex in $s$ evaluates to true. Now fix any clause. The one-vertex-per-clause result supplies a selected vertex from that clause, and its literal is one of the clause's three literals (ThreeSATToClique.getLitAt_mem_clause). Since that selected literal evaluates to true, the clause is satisfied. This holds for every clause.

**Key facts.** `ThreeSATToClique.clique_vertices_choose_one_per_clause`, `ThreeSATToClique.getLitAt_mem_clause`.
