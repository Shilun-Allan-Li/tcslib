<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean :: Complexity.copyDataWrite_next -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Writing the Next Input Payload

**Claim.** If the current payloads equal the copied payload vector with count $j$, then writing the virtual input payload of $x$ at coordinate $j$ on the input lane makes them equal the copied payload vector with count $j+1$.

**Proof.** On each work lane, the write leaves the tape unchanged, so the asserted equality follows directly from the hypothesis. On the input lane, at coordinate $j$ the write replaces the current component by the input payload at $j$. This is precisely the newly included coordinate in the count-$(j+1)$ copied vector; the coordinate is in range since $0\le j<j+1$. At any other coordinate, the tape is unchanged. The old and new copied-payload conditions agree away from $j$: the interval of included nonnegative coordinates grows from those less than $j$ to those less than $j+1$, and the special left-boundary coordinate $-1$ is included in both. Therefore the unchanged payloads already have the required new values.
