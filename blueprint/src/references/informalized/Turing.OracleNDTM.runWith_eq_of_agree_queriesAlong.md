<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/OracleAgreement.lean :: Turing.OracleNDTM.runWith_eq_of_agree_queriesAlong -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement on Queries Along a Computation

**Claim.** If every query word encountered on the run with oracle $O$ has the same membership status in $O$ and $O'$, then the two runs on $w$ from the initial configuration on $x$ have equal final configurations.

**Proof.** Apply the prefix-agreement result (`Turing.OracleTM.runWith_take_eq_of_agree`). At any prefix length $s<|w|$ where the run with $O$ is in its query state, its query word occurs in the list of queries along the run: the index $s$ lies in the range of indices below $|w|$, and the query-state condition makes the filter retain precisely that query. The assumed agreement on all queries in this list therefore supplies the membership equivalence required by the prefix-agreement result. It follows that the configurations agree at every prefix length through $|w|$. At full length, the prefix is $w$, proving equality of the final configurations.

**Key facts.** `Turing.OracleTM.runWith_take_eq_of_agree`.
