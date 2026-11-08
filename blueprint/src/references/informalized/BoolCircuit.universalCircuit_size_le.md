<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Universal.lean :: BoolCircuit.universalCircuit_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Bound on Universal Circuit Size

**Claim.** For a Boolean function $f$ on assignments to $n$ variables, the universal circuit for $f$ has size at most $2^n(n+1)+1$.

**Proof.** By the universal-circuit size formula, its size is the number of assignments on which $f$ is true times $n+1$, plus one (`universalCircuit_size`). The number of such assignments is at most the number of all assignments. There are $2^n$ assignments to $n$ Boolean variables, so multiplying the cardinality bound by the nonnegative factor $n+1$ and adding one gives the result.

**Key facts.** `BoolCircuit.universalCircuit_size`.
