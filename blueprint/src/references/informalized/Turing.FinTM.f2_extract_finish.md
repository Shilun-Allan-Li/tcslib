<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_extract_finish -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completion of Pair Extraction

**Claim.** From state $0$ at position $|pre|$, with tape $a$, head at $|a|-1$ truncated at zero, and empty output, the extractor halts within $2|a|+|rest|+3$ steps with output $(a$ if $first$, otherwise empty$)++(rest$ if $second$, otherwise empty$)$.

**Proof.** The proof first runs the rewind phase for $|a|+1$ steps, reaching the replay state with the work head at the origin. It then runs replay for another $|a|+1$ steps, reaching state $2$, with the head at $|a|$ and output equal to $a$ when $first$ is true and empty otherwise. These two phases are combined by the run-addition law ($\texttt{Turing.MultiTapeTM.runFrom_add}$), using the rewind and replay-finish results ($\texttt{Turing.FinTM.f2_extract_rewind}$ and $\texttt{Turing.FinTM.f2_extract_replay_finish}$). If $second$ is false, one further step halts without changing the output. If $second$ is true, the suffix phase scans and appends $rest$, then halts ($\texttt{Turing.FinTM.f2_extract_suffix}$). In the latter case the output is the replay output followed by $rest$. The chosen times are respectively $2(|a|+1)+1$ and $2(|a|+1)+(|rest|+1)$, each bounded by $2|a|+|rest|+3$. The one-step run equation ($\texttt{Turing.MultiTapeTM.runFrom_succ_eq_step'}$) identifies the final transition in the first case.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.f2_extract_rewind`, `Turing.FinTM.f2_extract_replay_finish`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.f2_extract_suffix`.
