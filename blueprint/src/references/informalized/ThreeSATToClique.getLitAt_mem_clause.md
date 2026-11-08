<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/NPReductions/ThreeSATToClique.lean :: ThreeSATToClique.getLitAt_mem_clause -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vertex literal belongs to its clause

**Claim.** If a vertex has clause component $i$, then its selected literal is one of the three literals in clause $f[i]$.

**Proof.** Once the clause components are identified, inspect the vertex's position in the clause. The positions $0$, $1$, and $2$ select respectively the first, second, and third literal, each of which belongs to the clause's list of three literals. These are all possible positions, so the selected literal belongs to that list.
