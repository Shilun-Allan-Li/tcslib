<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_window_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded construction of a symmetric window

**Claim.** Under the stated value, entry-state, and tape-content hypotheses, the machine reaches its exit state within the stated time bound, does not reach it earlier, keeps every work-tape head within the stated distance of its initial position, and leaves the specified word of length $2s+1$ on tape 1 with all other configuration components unchanged.

**Proof.** Let $w$ be the word consisting of $s$ false bits, one true bit, and then $s$ false bits; its length is $2s+1$. First, the proof changes the state type of the initial configuration to the state type of the advancing phase, preserving its tapes and head positions. The advancing-machine result (`Turing.rt_windowAdv_run`) then supplies a time $t$ at most $12(s+|ws|)+20$, with no earlier visit to its designated exit state, and with the required head-position control. At that time it has written $w$ on tape 1, with the head at the right-hand end of the written segment.

The construction next uses the forward skip machine to pass over the empty word. Its run result (`Turing.skipTM_run_ofCfg`) establishes that this takes one step, reaches its exit state for the first time then, and moves tape 1's head one position farther right. The proof checks that the write interval still has the required contents, including its two blank boundary cells, so the backward skip machine can now traverse $w$. Its run result (`Turing.skipBackTM_run_ofCfg`) shows that after $|w|+3$ steps the head has returned to the left-hand side of the segment, with no earlier visit to its exit state.

These phases are joined using the first-exit and head-bound composition principle (`Turing.rt_copy_seam`): if each phase avoids its exit state until its stated endpoint and its heads stay within a common radius, their concatenation has the same first-exit property and radius. The proof applies this principle first to the two skip phases and then to the advancing phase followed by those phases. The advancing bound is enlarged to $2s+|ws|+3$; the skip-phase bounds fit within the same radius, while tapes other than tape 1 keep their initial head positions. The combined endpoint is $t+1+(1+1+(|w|+3))$, which is at most $14(s+|ws|)+27$ because $|w|=2s+1$. The two changes of state labels identify the combined endpoint with the requested exit state. The tape contents and all remaining configuration fields follow from the phase endpoint descriptions and the fact that the skip phases only move the indicated head.

**Key facts.** `Turing.rt_windowAdv_run`, `Turing.skipTM_run_ofCfg`, `Turing.skipBackTM_run_ofCfg`, `Turing.rt_copy_seam`.
