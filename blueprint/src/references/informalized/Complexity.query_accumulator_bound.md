<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.query_accumulator_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on the Value of a Canonical Suffix

**Claim.** If a Boolean word $w$ is empty or ends in true and its length is at most the binary bit length of $n$, then the value represented by the suffix obtained by dropping its first $j$ bits is at most $2n$.

**Proof.** The value of a suffix cannot exceed the value of the whole word (the suffix-value bound, `Complexity.query_suffix_value_le`). Let $r$ be the value of $w$. Because $w$ is canonical, it is exactly the binary expansion of $r$ (`Complexity.LogProg.canon_eq_bits`), so the assumed length bound gives the binary expansion of $r$ length at most that of $n$. The binary-length bound then gives $r\le 2n$ (`Complexity.query_index_bound`). Combining these inequalities bounds the suffix value by $2n$.

**Key facts.** `Complexity.query_suffix_value_le`, `Complexity.LogProg.canon_eq_bits`, `Complexity.query_index_bound`.
