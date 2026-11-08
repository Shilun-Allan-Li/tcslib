<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Adder.lean :: BoolCircuit.prefixVal_inj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of binary prefix values

**Claim.** If two Boolean sequences have equal weighted prefix values below $i$, then they agree at every position below $i$.

**Proof.** Induct on $i$. For $i=0$ there are no positions to check. At the successor step, expand the equal prefix values using the recurrence (`prefixVal_succ`). The lower prefix value for either sequence is strictly less than $2^i$ (`prefixVal_lt`). Consequently, the contribution of the top bit, either $0$ or $2^i$, determines which of the two intervals $[0,2^i)$ or $[2^i,2^{i+1})$ contains the prefix value. Equality of the full values therefore forces the bits at position $i$ to agree. Subtracting their equal top-bit contributions leaves equality of the lower prefix values; the induction hypothesis then gives agreement at all positions below $i$. Together these establish agreement at every position below $i+1$.

**Key facts.** `BoolCircuit.prefixVal_succ`, `BoolCircuit.prefixVal_lt`.
