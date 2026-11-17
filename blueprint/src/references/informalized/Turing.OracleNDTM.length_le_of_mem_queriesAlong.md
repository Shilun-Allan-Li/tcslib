<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/OracleAgreement.lean :: Turing.OracleNDTM.length_le_of_mem_queriesAlong -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a Query Along a Run

**Claim.** If $z$ occurs among the queries made along the run of $N$ with oracle $O$ on input $x$ under $w$, then $|z|\le |w|$.

**Proof.** Unfold the definition of the queries along the run. Membership in this filtered list supplies an index $s<|w|$ at which the machine is in its query state and the query word is $z$. The query word after running on the prefix $w.take(s)$ has length at most $|w.take(s)|$ by the run-length bound (`Turing.OracleNDTM.queryString_runWith_length_le`). Since a prefix has length at most its requested take length, $|w.take(s)|\le s$. Thus $|z|\le s<|w|$, which gives the result.

**Key facts.** `Turing.OracleNDTM.queryString_runWith_length_le`, `Turing.OracleTM.length_le_of_mem_filtered_queries`.
