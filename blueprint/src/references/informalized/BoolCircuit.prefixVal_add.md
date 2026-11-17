<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Adder.lean :: BoolCircuit.prefixVal_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Addition of binary prefix values

**Claim.** For Boolean sequences $A,B$ and a natural number $i$, the sum of their weighted values below $i$ is the weighted value below $i$ of their bitwise sum, plus $2^i$ when the carry into position $i$ is true (and plus zero otherwise).

**Proof.** Proceed by induction on $i$. At $i=0$, all three prefix values are zero and the carry at position zero is false, so the identity holds. For the step from $i$ to $i+1$, the prefix recurrence (`prefixVal_succ`) adds the contribution of position $i$ to each prefix. At that position, the full-adder identity says that the two input bits together with the incoming carry equal the sum bit plus twice the outgoing carry. This identity follows by checking the possible Boolean values. Weight it by $2^i$; since $2\cdot2^i=2^{i+1}$, the added terms give exactly the contribution from the sum bit at position $i$ and the carry term at position $i+1$. Combining these with the induction hypothesis proves the result at $i+1$.

**Key facts.** `BoolCircuit.prefixVal_succ`.
