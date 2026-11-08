<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/OracleAgreement.lean :: Turing.OracleTM.length_le_of_mem_filtered_queries -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Bound for a Filtered Query

**Claim.** If each word $f(s)$ has length at most $s$ for $s<t$, then every word selected by $p$ among the values $f(s)$ for $s<t$ has length at most $t$.

**Proof.** Since $z$ occurs in the filtered list, it is the value $f(s)$ for some index $s$ that lies in the range from $0$ to $t-1$ and satisfies the selection predicate. The hypothesis gives $|f(s)|\le s$, and the range condition gives $s<t$, hence $s\le t$. Therefore $|z|=|f(s)|\le t$.
