<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AC0ThresholdParitySeparation.lean :: FABL.length_blockMiddleLayer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the middle block layer

**Claim.** For every natural number $m$ with $7\le m$, the middle block layer contains exactly $2^{m-1}$ clauses.

**Proof.** The middle block layer is obtained by mapping the clause-to-node-set construction over the clauses of the parity CNF. Mapping preserves list length, so its length equals the number of parity-CNF clauses. The parity CNF has size $2^{m-1}$ whenever its dimension is positive (\texttt{size_parityCNF}); the hypothesis $m\ge 7$ ensures this condition. Hence the middle layer has length $2^{m-1}$.

**Key facts.** `FABL.size_parityCNF`.
