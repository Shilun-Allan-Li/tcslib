<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clReplay_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complete Buffer Replay

**Claim.** Starting in the replay machine's start control with buffer $w$, head at $|w|$, and output $out$, after $2|w|+3$ steps it is halted at head position $|w|$, with buffer $w$ and output $out$ followed by $w$.

**Proof.** The first transition moves from the start control into rewind state and places the head at $|w|-1$, leaving the buffer and output unchanged. The remaining run splits into two portions of $|w|+1$ steps (`runFrom_add`), after rewriting the total as $1+(|w|+1)+(|w|+1)$ and decomposing the first step (`runFrom_succ_eq_step`). The backward-rewind lemma (`Complexity.clReplay_back`) takes the machine from rewind state at $|w|-1$ to emitting state at zero. The forward-replay lemma (`Complexity.clReplay_forward`) then appends the entire buffer, since the suffix starting at zero is $w$, and halts with the head at $|w|$.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_add`, `Complexity.clReplay_back`, `Complexity.clReplay_forward`.
