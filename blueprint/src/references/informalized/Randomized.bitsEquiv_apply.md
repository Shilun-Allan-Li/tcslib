<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomBits.lean :: Randomized.bitsEquiv_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Value of a Bit String

**Claim.** The integer represented by the standard bijection from length-$L$ Boolean strings to integers below $2^L$ equals the value of the corresponding bit list, with the first entry least significant.

**Proof.** The value of the list of bits of $f$ is the sum over positions $j$ of the bit at $j$ times $2^j$ (\texttt{Randomized.bitsVal_ofFn}). Under the standard function-to-integer equivalence, the represented integer is the same weighted sum, with each Boolean coordinate converted to its natural-number value. The standard identification of the two Boolean values with $0$ and $1$ shows term by term that these sums agree, proving the identity.

**Key facts.** `Randomized.bitsVal_ofFn`.
