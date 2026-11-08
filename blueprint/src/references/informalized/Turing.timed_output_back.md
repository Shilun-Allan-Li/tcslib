<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_output_back -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Output-Buffer Rewind

**Claim.** Starting in the output-buffer rewind phase with head at position $j-1$, after $j+1$ steps the interpreter is in the flush phase with its buffer head at zero and its real output extended by the bit $1$.

**Proof.** Induct on $j$, using the bound $j\leq |c.output|$. At $j=0$, one step takes the rewind phase directly to flush, and the next step accounts for the stated duration; the output-buffer step rule (`Turing.timed_output_step`) gives the resulting configuration. For the successor case, the buffer head is at position $j$, where the buffer contains the $j$th output bit: the natural-position buffer identity (`Turing.FinTM.bufferTape_nat`) and the list indexing rule establish this read. The output-step rule then moves the head one cell left while remaining in rewind. The induction hypothesis applies at the preceding position and completes the rewind to zero, producing the appended $1$ and flush state. The successor-run and zero-run identities (`Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`) relate these steps to the stated run length.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.FinTM.bufferTape_nat`, `Turing.timed_output_step`.

**Caveat.** The base-case source invokes the output-step rule to enter flush at position $-1$ and then uses simplification to match the target. The supplied upstream statements do not include the timed interpreter’s flush transition, so that final configuration equality cannot be fully detailed from the provided facts.
