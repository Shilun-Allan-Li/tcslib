<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformScan.lean :: BoolCircuit.AdjScan.drop_add_of_drop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive list drops

**Claim.** If dropping the first $p$ bits of $E$ leaves $s$ followed by $r$, then dropping the first $p+|s|$ bits of $E$ leaves $r$.

**Proof.** Dropping $p+|s|$ entries is the same as first dropping $p$ entries and then dropping $|s|$ more. The first drop leaves $s$ concatenated with $r$; removing the length of $s$ from this concatenation removes exactly $s$, leaving $r$.
