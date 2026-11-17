<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Uniform.lean :: BoolCircuit.length_encodeList_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower Bound for List Encoding Length

**Claim.** For a list $as$ and an element encoder $f$, the encoding of $as$ has length at least $|as|+1$.

**Proof.** Induct on $as$. The empty list encodes as the one-bit terminator, so its encoding length equals $0+1$. For a list with head $a$ and tail $as'$, the encoding adds a separator bit and the encoding of $f(a)$ before the encoding of the tail. Since the element encoding has nonnegative length, this is at least one more than the tail encoding length. Applying the induction hypothesis to the tail gives a lower bound of $1+(|as'|+1)=|a::as'|+1$.
