<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Copy_clean -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clean bounded-time input copy

**Claim.** For every Boolean word $x$, the release-wrapped three-state input copier has a first halting time $t$ with $0<t\le 2|x|+3$. At that time it has copied $x$ to tape zero, left the other work tapes blank, returned all heads to their initial positions, and emitted nothing.

**Proof.** The input copier first reaches state $2$ at a positive time $t_0\le 2|x|+2$, with $x$ copied to its work tape and its heads and output in the required positions. The proof identifies its initial configuration with the word-based configuration and rewrites the resulting tape contents as the designated state word. The release-wrapper lemma (\texttt{clA5Stop_clean}) then shows that the wrapped machine, after one additional step, is in its marked exit state with the same tape contents and output. Before that time, the underlying copier has not reached the exit state, by the first-arrival property of $t_0$; hence the wrapper has not halted. Finally, the first-halting-time lemma (\texttt{clA5_call_first_halt}) selects the earliest halting time $u$ no later than $t_0+1$, shows that no earlier configuration is halted, and preserves the configuration reached at $t_0+1$. Thus $0<u\le 2|x|+3$, and the requested clean halted configuration occurs at time $u$.

**Key facts.** `Complexity.clInput_first`, `Complexity.clA5Stop_clean`, `Complexity.clA5_call_first_halt`.
