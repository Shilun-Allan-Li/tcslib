<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerComplete.lean :: Complexity.Meyer.sE_edgeOf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign of the Integer Encoding

**Claim.** The sign indicator of the encoding of $(s,a)$ equals $s$: the encoding is negative exactly when $s$ is true.

**Proof.** If $s$ is false, the encoding is the natural number $a$, regarded as an integer, and hence is nonnegative; its negative-sign indicator is false. If $s$ is true, the encoding is $-a-1$, which is strictly negative for every natural number $a$; its indicator is true. These two cases give the asserted equality.
