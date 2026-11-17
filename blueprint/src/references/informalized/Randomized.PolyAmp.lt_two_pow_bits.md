<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPoly.lean :: Randomized.PolyAmp.lt_two_pow_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Bit-Length Bound

**Claim.** For every natural number $n$, one has $n<2^{|\operatorname{bits}(n)|}$.

**Proof.** The binary size of $n$ is the length of its binary expansion. The standard strict size bound says that every natural number is strictly less than the corresponding power of $2$; substituting the binary length for the size gives $n<2^{|\operatorname{bits}(n)|}$.
