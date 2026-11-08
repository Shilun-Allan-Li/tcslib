<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.padThreeCNF_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of the padded formula

**Claim.** If the original formula has at most $K$ clauses, the padded formula has exactly $K$ clauses.

**Proof.** The padded formula is formed by taking a list indexed by the $K$ elements of $\mathrm{Fin}(K)$, with each index producing either a lifted original clause or a filler clause. A list formed from a function on $\mathrm{Fin}(K)$ has length $K$. Since formula size is the length of its clause list, the padded formula has size exactly $K$.
