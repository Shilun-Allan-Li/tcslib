<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Helper.lean :: CommunicationComplexity.boolSign_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign of a Boolean sum

**Claim.** For a finite set of indices, the sign of the Boolean sum of the values of $f$ equals the product of their individual signs.

**Proof.** Proceed by induction on the finite set $s$. For the empty set, the Boolean sum is false and the empty product is $1$, so the identity holds. For the inductive step, write the set as the disjoint union of a new element $a$ and a smaller set $s$. The Boolean sum over the enlarged set is the XOR of $f(a)$ with the sum over $s$, while the product splits into the sign of $f(a)$ times the product over $s$. The sign of an XOR is the product of the signs of its two inputs (`boolSign_xor`); applying the induction hypothesis to the smaller set gives the required equality.

**Key facts.** `CommunicationComplexity.boolSign_xor`.
