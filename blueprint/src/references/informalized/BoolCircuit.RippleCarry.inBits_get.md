<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Adder.lean :: BoolCircuit.RippleCarry.inBits_get -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input-bit extraction

**Claim.** For every Boolean list $w$ and natural numbers $o,j$, extracting the input bit at offset $o+j$ from the entries of $w$ gives $w[o+j]$ when that position exists, and false otherwise.

**Proof.** By definition, `inBits` applies the defaulted list lookup at index $o+j$ to the list of values of the function supplied as input. When that function is `w.get`, its list of values is exactly $w$ (`List.ofFn_get`). Thus the lookup is $w.getD (o+j) false$, as claimed.
