<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.xorPairEmit_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# XOR of the Leading Bits

**Claim.** For bits $b,c$ and strings $p,u$, the pair-output rule on the encoding of $b$ followed by $p$ and $c$ followed by $u$ returns the one-bit string containing $b\mathbin{\mathrm{xor}}c$.

**Proof.** The leading bits determine the first bit of each decoded component, and both components are nonempty. The rule therefore emits one bit. If both leading bits are false or both are true, that bit is false; if they differ, it is true. These four cases are exactly the truth table for $b\mathbin{\mathrm{xor}}c$.
