<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Adder.lean :: BoolCircuit.prefixVal_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix values determined by initial bits

**Claim.** If two Boolean sequences agree at every position below $i$, then their weighted prefix values on positions below $i$ are equal.

**Proof.** Induct on $i$. For $i=0$, both prefix values are zero. At the successor step, the prefix recurrence (`prefixVal_succ`) expresses each value below $i+1$ as the value below $i$ plus the contribution of bit $i$, weighted by $2^i$. The sequences agree below $i$, so the induction hypothesis identifies the earlier prefix values; they also agree at position $i$ by assumption. Thus the two successor prefix values are equal.

**Key facts.** `BoolCircuit.prefixVal_succ`.
