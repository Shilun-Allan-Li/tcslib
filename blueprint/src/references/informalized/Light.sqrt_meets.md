<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Sqrt.lean :: Light.sqrt_meets -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Square root procedure correctness

**Claim.** If the word limit is at least $3K+4$, the square root procedure on input $K$ runs within $18\lfloor\sqrt K\rfloor+12$ steps, returns $\lfloor\sqrt K\rfloor$, and leaves memory unchanged.

**Proof.** First, the square-root bounds give $(\lfloor\sqrt K\rfloor)^2\le K< (\lfloor\sqrt K\rfloor+1)^2$, and also $\lfloor\sqrt K\rfloor\le K$. After initializing the candidate to $0$ and the running square to $1$, establish the loop invariant that before round $i$ the candidate is $i$ and the running square is $(i+1)^2$, with the input and memory unchanged. For each $i<\lfloor\sqrt K\rfloor$, the first square-root bound implies $(i+1)^2\le K$, so the loop test succeeds. The update replaces the running square by $(i+2)^2$, since $(i+2)^2=(i+1)^2+2i+3$, and increments the candidate to $i+1$. The word-limit hypothesis ensures the loop expressions and updates are safe. At $i=\lfloor\sqrt K\rfloor$, the strict upper square-root bound makes the loop test false. The final assignment copies the candidate to the result, yielding the floor square root while preserving memory. The loop-block execution bound and the initializations and final assignment give the stated time bound; `Meets.of_body` then packages this execution as the procedure’s result.

**Key facts.** `Light.Meets.of_body`, `Light.update_frame_setLocal`.
