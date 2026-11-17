<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_output_forward -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Flushing the Output Buffer

**Claim.** If the interpreter output is the concatenation of $l$ and $r$, then flushing from buffer position $|l|$ for $|r|+1$ steps halts, advances the buffer head to the end of the interpreter output, and appends $r$ to the real output.

**Proof.** Induct on the suffix $r$. If $r$ is empty, the interpreter output is exactly $l$, so the buffer head is already at its end. The natural-position buffer identity (`Turing.FinTM.bufferTape_nat`) and the list-indexing rule show that the next read is blank; the output-step rule (`Turing.timed_output_step`) then takes the flush phase to the halted state without emitting a symbol.

If $r=b::r'$, the universal-table read identity (`Turing.universal_table_read`) says that the buffer at position $|l|$ contains $b$. The output-step rule emits this bit and moves the buffer head right while remaining in flush. The successor-run identity (`Turing.MultiTapeTM.runFrom_succ_eq_step`) separates this first step from the remaining run. Apply the induction hypothesis with prefix $l++[b]$ and real output extended by $b$; the assumed output decomposition supplies its hypothesis. The list and length identities then identify the final buffer position with $|c.output|$ and the real output with $o++r$.

**Key facts.** `Turing.FinTM.bufferTape_nat`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.timed_output_step`, `Turing.universal_table_read`.
