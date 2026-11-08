<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Adder.lean :: BoolCircuit.agreeBit_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement on an Initial Bit Segment

**Claim.** For Boolean sequences $A,B,C$ and a natural number $i$, the agreement indicator at $i$ is true exactly when $C_j$ equals the $j$th sum bit of $A$ and $B$ for every $j<i$.

**Proof.** Proceed by induction on $i$. At $i=0$, the agreement indicator is true by definition, and there are no indices $j<0$, so the universal condition also holds. For the step from $i$ to $i+1$, the indicator is the conjunction of the previous indicator and the condition that the $i$th sum bit agrees with $C_i$. For Boolean values, the latter condition is equivalent to equality of those bits. By the induction hypothesis, the conjunction therefore says that agreement holds for all indices below $i$ and also at $i$. These are precisely all indices below $i+1$. Conversely, agreement at every index below $i+1$ gives the previous-prefix condition and the equality at $i$, hence makes the new indicator true.
