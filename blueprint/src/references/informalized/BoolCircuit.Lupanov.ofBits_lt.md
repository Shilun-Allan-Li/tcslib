<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LupanovGates.lean :: BoolCircuit.Lupanov.ofBits_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary value of a bit list

**Claim.** For every finite list $l$ of Boolean bits, its binary value is strictly less than $2^{|l|}$.

**Proof.** Proceed by induction on the list. For the empty list, its value is zero and the bound is $0<1$. For a list with first bit $b$ and tail $l$, the value is twice the value of the tail plus $b$'s numeric value. By induction the tail value is less than $2^{|l|}$, and a Boolean bit has numeric value at most one. Therefore the whole value is at most $2(2^{|l|}-1)+1$, which is strictly less than $2\cdot2^{|l|}=2^{|b::l|}$.
