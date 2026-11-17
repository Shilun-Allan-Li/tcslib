<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/NPReductions/ThreeSATToClique.lean :: ThreeSATToClique.ThreeSAT_to_Clique_completeness -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completeness of the reduction

**Claim.** If a 3-CNF formula $f$ is satisfiable, then its conflict graph has a clique with exactly as many vertices as $f$ has clauses.

**Proof.** Choose a satisfying assignment $\alpha$. Each clause has at least one true literal, so for every clause index $i$ choose a position $j_i$ at which its literal is true. Form a set consisting of the vertex $(i,j_i)$ for each clause index $i$. Distinct indices give distinct vertices, so this set has $m$ elements. Any two distinct vertices come from different clauses, and their literals are both true under $\alpha$. True literals cannot be opposite occurrences of the same variable, so the two vertices are adjacent in the conflict graph. Thus the set is a clique of size $m$.

**Key facts.** `ThreeSATToClique.no_conflict_of_true`.
