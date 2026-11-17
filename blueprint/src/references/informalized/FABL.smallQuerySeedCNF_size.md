<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.smallQuerySeedCNF_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of the padded seed formula

**Claim.** For $r>0$, the padded seed CNF has exactly $r2^r$ clauses.

**Proof.** By definition, the padded formula's clause list is obtained by applying `List.ofFn` to the function assigning a clause to each index in `Fin (r2^r)`. The length of this list is the cardinality of that index type, namely $r2^r$. Since the size of a CNF formula is the length of its clause list, its size is exactly $r2^r$.
