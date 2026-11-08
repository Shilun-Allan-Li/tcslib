<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/OracleAgreement.lean :: Turing.OracleTM.runFrom_eq_of_agree_length_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement on Short Queries

**Claim.** If the two oracles agree on membership for every word of length less than $t$, then the configurations after $t$ steps from the initial configuration on $x$ are equal.

**Proof.** Use the result that runs agree provided the two oracles give the same membership answer to every query encountered before time $t$. At any such time $s<t$, the query-length bound gives a query string of length at most $s$. Since $s<t$, its length is strictly less than $t$, so the assumed agreement applies to that query. Thus all encountered queries receive matching answers, and the runs agree after $t$ steps.

**Key facts.** `Turing.OracleTM.runFrom_eq_of_query_agree`, `Turing.OracleTM.queryString_length_le`.
