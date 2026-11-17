<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean :: Turing.body_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Initial run of the iteration body

**Claim.** If $E$ has at least one work tape, the emitted iteration body, begun in its initial configuration on input $x$, reaches the anchor after $3|x|+4$ steps with $x$ on its first work tape and all other work tapes empty, without visiting the anchor earlier or at time zero.

**Proof.** The proof concatenates five safe phases, where a safe run records both its endpoint and that it avoids the anchor at every earlier time. First, the copy phase scans the input and writes its symbols onto the first work tape. Induction on the number of copied symbols gives a safe run of $|x|$ steps (`copy_step`, `SafeRun.trans`, `SafeRun.cons`, `SafeRun.zero`); the step at the end of the input enters the tape-rewind phase (`copy_end`).

Next, the machine moves the first work-tape head left across the copied word. Induction on the number of symbols remaining shows this takes $|x|+1$ steps and reaches the input-rewind state (`rwTape_some`, `rwTape_none`). A single transition begins rewinding the input head (`rwIn0_step`), and then induction on the input-head position rewinds it across the input and returns to the anchor, again in $|x|+1$ steps (`rwInput_some`, `rwInput_zero`). These phases together with the initial copy yield $|x|+(|x|+1)+1+(|x|+1)=3|x|+3$ steps; the final count is $3|x|+4$ because the copy phase also includes the transition at the input end. The established endpoint is the configuration with $x$ on the first work tape and all others empty. Each phase is safe, and their concatenation preserves safety (`SafeRun.trans`). The initial configuration is the zero-progress copy configuration (`initCfg_eq_copyCfg`), so the resulting safe run has the asserted start and endpoint.

**Key facts.** `Turing.SafeRun.zero`, `Turing.SafeRun.cons`, `Turing.SafeRun.trans`, `Turing.copy_step`, `Turing.copy_end`, `Turing.initCfg_eq_copyCfg`, `Turing.rwTape_some`, `Turing.rwTape_none`, `Turing.rwIn0_step`, `Turing.rwInput_some`, `Turing.rwInput_zero`.

**Caveat.** The stated proof source's final arithmetic rewrites the total as $|x|+1+(|x|+1)+1+(|x|+1)=3|x|+4$. The prose above describes those phases, but the supplied upstream statements do not include the intermediate configuration definitions needed to independently verify every phase endpoint.
