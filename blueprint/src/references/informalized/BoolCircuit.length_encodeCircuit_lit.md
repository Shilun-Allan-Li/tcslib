<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/HardFunctions.lean :: BoolCircuit.length_encodeCircuit_lit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a Literal Encoding

**Claim.** For an index $k<n$ and either polarity $s$, the encoding of the literal with index $k$ and polarity $s$ has length $k+3$.

**Proof.** Proceed by induction on $k$. At $k=0$, the literal encoding contains the sign marker, the polarity bit, and the one-bit encoding of zero, so its length is $3$. For the successor case, the proof first observes that increasing the index from $k$ to $k+1$ adds one repeated bit to its natural-number encoding. Hence the literal encoding length at $k+1$ is the length at $k$ plus one. By induction this is $(k+3)+1=k+1+3$, as required.
