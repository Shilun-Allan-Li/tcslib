<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/OracleAgreement.lean :: Turing.OracleTM.queriesWithin_length_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on the Number of Queries

**Claim.** The list of queries made during the first $t$ configurations of an oracle machine’s run has length at most $t$.

**Proof.** The query list is obtained by applying `filterMap` to the $t$ indices in the range $0,\ldots,t-1$, recording at most one query for each index. Consequently its length is at most the length of that range, which is $t$.
