<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Adder.lean :: BoolCircuit.agree_and_noCarry_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix Addition and Absence of Carry

**Claim.** For Boolean sequences $A,B,C$ and a natural number $i$, the conjunction of the agreement indicator at $i$ with the negation of the carry bit at $i$ is true exactly when the value of the first $i$ bits of $C$ is the sum of the values of the first $i$ bits of $A$ and $B$.

**Proof.** Let $P_f(i)$ denote the value of the first $i$ bits of a sequence $f$. The prefix-addition identity (`BoolCircuit.prefixVal_add`) says that $P_A(i)+P_B(i)=P_{	ext{sumBit}}(i)+2^i\,	ext{carryBit}(i)$. If agreement holds throughout the first $i$ positions, the prefix values of $C$ and the sum-bit sequence are equal (`BoolCircuit.prefixVal_congr`). If also the carry at position $i$ is false, the identity reduces to $P_A(i)+P_B(i)=P_C(i)$, proving one implication. Conversely, suppose $P_C(i)=P_A(i)+P_B(i)$. The value of any $i$-bit prefix is strictly less than $2^i$ (`BoolCircuit.prefixVal_lt`). If the carry were true, the prefix-addition identity would make $P_A(i)+P_B(i)$ at least $2^i$, contradicting the assumed equality with $P_C(i)$. Thus the carry is false. The identity now gives equality of the prefix values of $C$ and the sum-bit sequence; equality of prefix values implies equality at every position below $i$ (`BoolCircuit.prefixVal_inj`). By the agreement characterization (`BoolCircuit.agreeBit_iff`), the agreement indicator is true as required.

**Key facts.** `BoolCircuit.prefixVal_add`, `BoolCircuit.prefixVal_congr`, `BoolCircuit.prefixVal_lt`, `BoolCircuit.agreeBit_iff`, `BoolCircuit.prefixVal_inj`.
