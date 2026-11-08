<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clReplay_from -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Replay from a Buffer Position

**Claim.** For $j\le |w|$, starting in the replay machine's start control with buffer $w$, head at $j$, and output $out$, after $j+|w|+3$ steps the machine is halted at head position $|w|$, with output $out$ followed by $w$.

**Proof.** The first transition releases the start control into rewind state and moves the head from $j$ to $j-1$, leaving the buffer and output unchanged. Split the remaining run into $j+1$ steps and $|w|+1$ steps (`runFrom_add`), using the successor-step decomposition (`runFrom_succ_eq_step`) and the equality $j+|w|+3=1+(j+1)+(|w|+1)$. The backward-rewind lemma (`Complexity.clReplay_back`) takes the machine from rewind state at $j-1$ to emitting state at zero in $j+1$ steps. Then the forward-replay lemma (`Complexity.clReplay_forward`), applied at position zero, takes it to the halted state at head $|w|$ and appends $w.drop\,0=w$ to the output. The step counts combine to the asserted total.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_add`, `Complexity.clReplay_back`, `Complexity.clReplay_forward`.
