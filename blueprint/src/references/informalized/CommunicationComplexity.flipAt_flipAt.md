<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Helper.lean :: CommunicationComplexity.flipAt_flipAt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A single-coordinate flip is an involution

**Claim.** Applying the flip at coordinate $i$ twice to an input $x$ recovers $x$.

**Proof.** Compare the two inputs at each coordinate $j$. If $j=i$, the flip negates the value, and negating it a second time restores the original Boolean value. If $j\ne i$, each flip leaves that coordinate unchanged. The two inputs therefore agree at every coordinate, so they are equal.
