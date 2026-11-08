<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineSetup.lean :: Complexity.Meyer.cpy_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copying a Word on the Simulated Tape

**Claim.** Under the stated suffix and length conditions, the copying state reads the remaining suffix of the input, appends it to the $X$ buffer, and after one additional step enters the rewind-$X$ state at the right boundary; the other buffers and head positions remain unchanged, and the output is empty.

**Proof.** Induct on the suffix `rest`. If it is empty, the suffix condition says the next input symbol at position $p-1$ is absent. The machine therefore leaves the copying state, moves into rewind-$X$, and moves the $X$ head left once. The resulting position is the right boundary, and the other tracks and output are unchanged; the run is evaluated as one step after the zero-step run (`runFrom_succ_eq_step`, `runFrom_zero`).

If `rest=b::r`, the suffix condition says the current input symbol is $b$, and the remaining suffix after advancing one position is $r` (`getElem?_of_drop`). The copying transition writes $b$ at the end of the $X$ buffer and advances the input and $X$ heads (`pcfg_step`, `tact_idle_apply`). The tape update is exactly replacement of the buffer by $w_X++[b]` (`bufferTape_write`), while the other buffers and heads are idle; the input head advances to the clamped position for $p+1$ (`moveInputPos_fpos`). Apply the induction hypothesis to $r$ with starting position $p+1$ and buffer $w_X++[b]$. The run decomposition over this first step and the remaining run gives the stated final configuration; the list-length and associativity identities identify its $X$ buffer and head position with those in the claim.

**Key facts.** `Complexity.Meyer.getElem?_of_drop`, `Complexity.Meyer.pcfg_step`, `Complexity.Meyer.tact_idle_apply`, `Complexity.Meyer.bufferTape_write`, `Complexity.Meyer.moveInputPos_fpos`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
