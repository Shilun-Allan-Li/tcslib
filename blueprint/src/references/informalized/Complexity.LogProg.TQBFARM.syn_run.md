<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Walk.lean :: Complexity.LogProg.TQBFARM.syn_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run of the Syntax Scan

**Claim.** Under the stated pointer, register, and input-length bounds, the program scans the remaining suffix from the syntax-scanning label to the input-exhausted label, updates the automaton state by scanning that suffix, and changes only the pointer to the input length; every pre-endpoint configuration satisfies the precondition and register bound.

**Proof.** Proceed by induction on the number $n$ of input positions remaining. If $n=0$, the pointer is already at the input length. The suffix is empty, so its scan leaves the automaton state unchanged. The program's length-test call takes its exhausted-input branch, and the zero-length run at the resulting label gives the required endpoint; `len_f` packages the exhausted-input branch with the given bounds. If $n+1$ positions remain, the pointer is strictly before the input end. Split the suffix as its bit $b$ followed by the suffix beginning at position $P+1$. Increasing the pointer by one preserves the register bounds, since the new pointer is at most the input length and the input length is at most $B$. The induction hypothesis, with syntax state updated by the transition on $b$, supplies the run for the shorter suffix. The length-test call takes its non-exhausted branch (`len_t`); the input-bit call reads $b$ (`read_b`), as the split shows the bit at position $P$ is $b$. At the resulting transition label, one program step updates the automaton state and advances the pointer, matching the induction hypothesis's starting configuration. Prepending that step is justified by `step_of`. The scan identity for a list fold then identifies the final automaton state with scanning the original suffix. The run lemmas preserve the guard, including the required preconditions and register bounds, throughout.

**Key facts.** `Complexity.LogProg.TQBFARM.fin_of`, `Complexity.LogProg.TQBFARM.len_f`, `Complexity.LogProg.TQBFARM.len_t`, `Complexity.LogProg.TQBFARM.read_b`, `Complexity.LogProg.TQBFARM.step_of`, `Complexity.getD_of_drop`.
