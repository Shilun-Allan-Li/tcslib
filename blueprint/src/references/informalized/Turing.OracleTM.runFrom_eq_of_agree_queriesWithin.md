<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/OracleAgreement.lean :: Turing.OracleTM.runFrom_eq_of_agree_queriesWithin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement on Queries Made

**Claim.** If the two oracles agree on every query string submitted during the first $t$ steps of the run using $O$, then the configurations after $t$ steps using $O$ and $O'$ are equal.

**Proof.** Apply the result that the runs agree when membership answers match at every query encountered before time $t$. For any time $s<t$ at which the run using $O$ is in the query state, the query string at that time occurs in the list of queries made during the first $t$ steps: it is the entry contributed by index $s$ in the defining filtered list. The hypothesis therefore gives matching membership answers for this query. The required agreement holds at every encountered query, so the configurations after $t$ steps are equal.

**Key facts.** `Turing.OracleTM.runFrom_eq_of_query_agree`.
