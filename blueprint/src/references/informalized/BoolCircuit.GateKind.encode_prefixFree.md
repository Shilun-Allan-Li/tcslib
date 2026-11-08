<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Uniform.lean :: BoolCircuit.GateKind.encode_prefixFree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix-free gate-kind encoding

**Claim.** For any gate kinds $a,b$ and Boolean lists $s,t$, if the encoding of $a$ followed by $s$ equals the encoding of $b$ followed by $t$, then $a=b$ and $s=t$.

**Proof.** The three encodings are the distinct two-bit strings $00$, $01$, and $10$. Compare the first two bits on both sides of the assumed equality. They determine the gate kind uniquely, so $a=b$. The common two-bit prefix can then be canceled from the list equality, yielding $s=t$.
