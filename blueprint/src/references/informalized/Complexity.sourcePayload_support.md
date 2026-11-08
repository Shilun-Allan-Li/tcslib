<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.sourcePayload_support -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite support of source payloads

**Claim.** After $t$ steps, every source payload at an offset outside $[-3B,3B]$ is blank, provided $t\le B$ and $|x|+1\le B$.

**Proof.** Let $c$ be the configuration reached after $t$ steps. For a work-tape coordinate $j$, the head position lies between $-t$ and $t$, and every cell strictly outside that interval is blank; these are the two conclusions of the source-bounds lemma (`Turing.FinTM.source_bounds`). If $z<-3B$ or $3B<z$, then, using $t\le B$, the position of cell $c$’s head plus $z$ lies strictly below $-t$ or strictly above $t$. The work-tape symbol there is therefore blank, and its payload tag is zero. For the input coordinate, the shifted input index $(c.inputPos-1)+z$ is strictly below $-1$ or strictly above $|x|$, using the bound on the input length and the fact that the input position is within its finite range. The input payload is blank outside those bounds (`Complexity.inputPayload_outside`). Thus every coordinate has the blank payload.

**Key facts.** `Turing.FinTM.source_bounds`, `Complexity.inputPayload_outside`.
