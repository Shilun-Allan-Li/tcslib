<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LupanovGates.lean :: BoolCircuit.Lupanov.testBit_heapPath -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Heap Path Bits

**Claim.** For every $l$ and every $i<l$, the binary digit of $H(l)$ in position $l-1-i$ is $x(o+i)$.

**Proof.** Proceed by induction on $l$. When $l=0$, there is no index $i<l$. For the step from $l$ to $l+1$, split into $i<l$ and $i=l$. If $i<l$, write $l-i=(j+1)$, so the target position is $j+1$. The recursion gives $H(l+1)=2H(l)+x(o+l)$; shifting by one places the appended Boolean in position zero, while the digit in position $j+1$ is the digit of $H(l)$ in position $j$. The induction hypothesis identifies that digit with $x(o+i)$. If $i=l$, the target position is zero, and the same recursion makes its digit exactly the appended bit $x(o+l)$.
