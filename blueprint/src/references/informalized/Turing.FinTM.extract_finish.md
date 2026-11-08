<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.extract_finish -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting after extractor rewind

**Claim.** From the rewind configuration, the pair extractor halts within $2|a|+|rest|+3$ steps and outputs the selected buffer and suffix according to the two flags.

**Proof.** Run the rewind phase for $|a|+1$ steps. The rewind lemma (`Turing.FinTM.extract_rewind`) places the machine in replay state with its work head at zero. Run replay for another $|a|+1$ steps; the replay-finish lemma (`Turing.FinTM.extract_replay_finish`) places it in suffix state, with the output equal to $a$ if `first` is true and empty otherwise. If `second` is false, one further step halts without adding output. If `second` is true, the suffix lemma (`Turing.FinTM.extract_suffix`) runs for $|rest|+1$ steps, halts, and appends exactly $rest$. The two phase lengths plus the final halting step are at most $2|a|+|rest|+3$. The run-addition law (`Turing.MultiTapeTM.runFrom_add`) concatenates these phases, and the successor-step identity (`Turing.MultiTapeTM.runFrom_succ_eq_step'`) handles the single final transition.

**Key facts.** `Turing.FinTM.extract_rewind`, `Turing.FinTM.extract_replay_finish`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.extract_suffix`.
