<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_undo_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reversal of a Live Machine Run

**Claim.** If the configurations reached from $c_0$ at every time strictly before $t$ are live, then the restoration machine started from the checkpoint for the configuration at time $t$, with the history of those $t$ steps and input-head position $p$, reaches the completed restoration configuration for $c_0$ and $p$ after exactly $2t+1$ steps.

**Proof.** Proceed by induction on $t$. At $t=0$, the history is empty, and one restoration step reaches the completed restoration configuration by the empty-history transition result (`Complexity.enumCont_undo_empty`).

For the induction step, let $c$ be the original machine’s configuration at time $t$. The live-run hypothesis ensures that $c$ has a state $q$, so its next action $a$ is defined. The configuration at time $t+1$ is $a$ applied to $c$, and its history is the history through time $t$ followed by the entry recording the symbols under $c$’s heads and the moves prescribed by $a$. From the checkpoint for this extended history, the first restoration step reaches the intermediate restoration configuration (`Complexity.enumCont_undo_back`); the next step restores the source configuration and returns to the checkpoint for $c$ with the shorter history (`Complexity.enumCont_undo_write`). Thus two restoration steps reduce the problem to the checkpoint at time $t$. The run composition law identifies the remaining run with the restoration run from that checkpoint, and the induction hypothesis supplies its length $2t+1$. The total is $2+(2t+1)=2(t+1)+1$. The successor time and run composition laws used here are `Turing.MultiTapeTM.runFrom_succ_eq_step'` and `Turing.MultiTapeTM.runFrom_add`; the zero-time case uses `Turing.MultiTapeTM.runFrom_zero`.

**Key facts.** `Complexity.enumCont_undo_empty`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.enumCont_undo_back`, `Complexity.enumCont_undo_write`, `Turing.MultiTapeTM.runFrom_add`.
