<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.BooleanCircuit.toWidthThreeCNF_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width-three CNF size bound

**Claim.** For a Boolean circuit with $g$ gates, its width-three CNF encoding has at most $3g+1$ clauses.

**Proof.** For each gate, its associated clause block has at most three clauses (`gateClauses_length_le_three`). The encoding concatenates these blocks, one for each of the $g$ gates. A list of $g$ blocks each of length at most three has total length at most $3g$ (`length_flatten_le_mul`). The encoding adds one further clause, so its size is at most $3g+1$.

**Key facts.** `FABL.BooleanCircuit.gateClauses_length_le_three`, `FABL.length_flatten_le_mul`.
