<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Adder.lean :: BoolCircuit.bitsVal_eq_prefixVal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean List Value as a Prefix Sum

**Claim.** For every finite Boolean list $l$, its base-two value is the sum of its entries, interpreted as $0$ or $1$, weighted by their positions.

**Proof.** Proceed by induction on $l$. The empty list has value zero, matching the empty prefix sum. For a list $b::l$, the prefix sum recurrence separates the position-$0$ contribution from the remaining positions: by the prefix recurrence ( `BoolCircuit.prefixVal_succ'`), it is $b+2$ times the prefix sum of the shifted tail entries. The base-two value of $b::l$ has the same decomposition: its first digit contributes $b$, and the tail digits contribute twice the tail's base-two value. The induction hypothesis identifies that tail value with the shifted prefix sum, giving the result.

**Key facts.** `BoolCircuit.prefixVal_succ'`.
