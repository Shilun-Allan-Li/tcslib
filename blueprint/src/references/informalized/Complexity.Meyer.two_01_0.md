<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineParse.lean :: Complexity.Meyer.two_01_0 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Updated Coordinate

**Claim.** After setting coordinate $0$ to $a$ and then coordinate $1$ to $a'$, the resulting function takes value $a$ at coordinate $0$.

**Proof.** The second update changes only coordinate $1$, so it leaves coordinate $0$ as set by the first update. The first update assigned the value $a$ there.
