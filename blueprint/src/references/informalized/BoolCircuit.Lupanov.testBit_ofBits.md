<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LupanovGates.lean :: BoolCircuit.Lupanov.testBit_ofBits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bits of a Boolean List

**Claim.** For every finite Boolean list $L$ and index $i$, digit $i$ of its encoding is the entry at index $i$, with out-of-range entries interpreted as false.

**Proof.** Use induction on the list, splitting the head-index cases. For the empty list, its encoding is zero and every digit is false. For a nonempty list at index zero, the encoding is twice the encoding of the tail plus the head's Boolean value, so its lowest digit is the head. At an index one greater than $i$, the shift identity for binary digits says that the digit is digit $i$ of the tail's encoding; the list lookup at that index is likewise lookup $i$ in the tail. The induction hypothesis therefore gives the result.
