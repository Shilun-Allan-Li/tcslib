<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Oracle.lean :: Turing.OracleTM.queryString_length_le_of_blank -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query Length Bound

**Claim.** If the query-tape cell at position $n$ is blank, then the query string has length at most $n$.

**Proof.** The blank cell at position $n$ witnesses that there is some nonnegative position containing no symbol. By the definition of the query string, its cutoff is the least such position, so that cutoff is at most $n$. The query string is obtained by filtering the positions below this cutoff, and filtering cannot produce more elements than the original list. Hence its length is at most the cutoff, and therefore at most $n$.
