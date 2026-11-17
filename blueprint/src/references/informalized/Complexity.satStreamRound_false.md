<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satStreamRound_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Round at a Terminator

**Claim.** When the input has a terminator immediately after the consumed prefix and the current phase is not finished, one round consumes that bit, emits the one-bit string $[0]$, and updates the phase as stated.

**Proof.** Since the consumed length is the length of the prefix $p$, dropping that prefix from $x=p++[0]++r$ leaves a list beginning with $0$. The phase is not $4$, so the round enters the suffix-processing case; the leading terminator branch consumes one bit, emits $[0]$, leaves the fresh cursor at $j$, and sets the phase to $4$ when the old phase is $0$ and to $0$ otherwise. The consumed length becomes $|p|+1$, as claimed.
