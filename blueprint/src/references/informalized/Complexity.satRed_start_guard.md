<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satRed_start_guard -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# No early visit to the streaming state

**Claim.** If the transducer started on a Boolean word has empty output after $t$ steps, then at every earlier time $i<t$ its state is not $9$.

**Proof.** Fix $i<t$ and suppose the configuration at time $i$ is in state $9$. The output-prefix property says that the output at time $i$ is a prefix of the output at time $t$ (\texttt{Turing.MultiTapeTM.output\_prefix}). Since the latter is empty, the former must also be empty. But one more step appends the current output symbol's list representation to the output (\texttt{Turing.MultiTapeTM.step\_output}); in state $9$, the transducer's output rule emits a symbol, so that appended list has length one. The run-at-successive-times identity (\texttt{Turing.MultiTapeTM.runFrom\_succ\_eq\_step'}) therefore makes the output at time $i+1$ have positive length, contradicting that it is a prefix of the empty final output. Hence the state at time $i$ cannot be $9$.

**Key facts.** `Turing.MultiTapeTM.output_prefix`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.step_output`.
