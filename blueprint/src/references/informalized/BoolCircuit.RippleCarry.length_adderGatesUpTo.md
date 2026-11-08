<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Adder.lean :: BoolCircuit.RippleCarry.length_adderGatesUpTo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the ripple-carry gate list

**Claim.** For all natural numbers $n,k,i$, the gate list consisting of the initial two constant gates followed by $i$ bit blocks has length $2+15i$.

**Proof.** Induct on the number $i$ of bit blocks. With no blocks, the list consists of the two constant gates, so its length is $2$. For the successor step, the construction appends one bit block to the list for $i$ blocks. Expanding the definitions of a bit block, a full adder, and the XOR gate list shows that the new block has $15$ gates. By the induction hypothesis the resulting length is $(2+15i)+15$, which rearranges to $2+15(i+1)$.
