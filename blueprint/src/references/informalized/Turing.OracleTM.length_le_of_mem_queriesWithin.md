<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/OracleAgreement.lean :: Turing.OracleTM.length_le_of_mem_queriesWithin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Bound for Queries Within a Run

**Claim.** Every query recorded among the queries made during the first $t$ configurations of an oracle machine’s run has length at most $t$.

**Proof.** A query in the recorded list arises from some index $s<t$ at which the machine is in its query state. Its word is the query string in the configuration reached after $s$ steps. The query-length bound at time $s$ (`Turing.OracleTM.queryString_length_le`) says that this word has length at most $s$. The filtered-query length bound (`Turing.OracleTM.length_le_of_mem_filtered_queries`) therefore applies, and since $s<t$, the word has length at most $t$.

**Key facts.** `Turing.OracleTM.queryString_length_le`, `Turing.OracleTM.length_le_of_mem_filtered_queries`.
