<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_flush -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Flushing buffered output after halting

**Claim.** If the four-tape interpreter configuration has no active state, then after $2|c.\text{output}|+3$ steps from its timed lift with clock word $b$, the timed interpreter has no active state and its real output is $1$ followed by $c.\text{output}$.

**Proof.** Because the original configuration is halted, its timed lift is the output-copying configuration at the start of the emit phase, with the buffer head at the end of the buffered output (`timedOutputCfg`). The initial emit step moves the buffer head back and enters the emit-back phase (`timed_output_step`). The output-back lemma then traverses the buffered output to its beginning, reaching the flush phase and appending the leading $1$ (`timed_output_back`). The output-forward lemma copies the buffered word to the real output, reaches the end, and halts (`timed_output_forward`). Joining these runs gives a total of $1+(|c.\text{output}|+1)+(|c.\text{output}|+1)=2|c.\text{output}|+3$ steps (`timedCut_run_join`), with output $[1]$ followed by the original word.

**Key facts.** `Turing.timed_output_step`, `Turing.timed_output_back`, `Turing.timed_output_forward`, `Turing.timedCut_run_join`.
