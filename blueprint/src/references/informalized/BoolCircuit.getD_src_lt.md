<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyGadget.lean :: BoolCircuit.getD_src_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on source lookup

**Claim.** If a list has length $m$ and every entry is less than $L$, then default lookup at any index $v<m$ is less than $L$.

**Proof.** Since $v<m$ and the list has length $m$, the index is in range. Thus default lookup is the actual entry at $v$. That entry belongs to the list, so the assumed bound on every list entry applies.
