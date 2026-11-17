<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clFinalCount_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Computability of Final Counts

**Claim.** If the input transformation $y$ is polynomial-time computable and a unary word of length $T(x)$ is polynomial-time computable, then the binary representation of the $i$th movement count after $T(x)$ steps of the count process initialized on $y(x)$ is polynomial-time computable.

**Proof.** The record-word construction converts $y(x)$ and the unary encoding of $T(x)$ into the packed record containing the data needed for the count process; by `Complexity.clRecordWords_native`, this encoding is polynomial-time computable. Use the count-output machine on that record. For each input $x$, the quadratic runtime bound for this machine (`Complexity.clCountOutput_quadratic`), with the four auxiliary words empty, gives precisely the binary representation of the desired count. The native-image principle (`Complexity.clNative_image`) says that composing a polynomial-time computable input transformation with a machine whose runtime is bounded by a fixed polynomial in the transformed input length preserves polynomial-time computability. Applying it with the stated quadratic bound proves the claim.

**Key facts.** `Complexity.clRecordWords_native`, `Complexity.clCountOutput_quadratic`, `Complexity.clNative_image`.
