<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/Examples.lean :: Complexity.pal_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewind-Phase Configuration Invariant

**Claim.** For every $i\le |x|$, after $i$ steps from state $1$ with input head at position $i$, the full copy of $x$ on the work tape, and work head at cell $|x|$, the machine is in state $1$ with input head at position $0$, while the work tape, work-head position, and empty output are unchanged.

**Proof.** Induct on $i$. For $i=0$, the initial input-head position is already $0$, so the claim holds. For the successor case, the single rewind transition moves the input head from position $i+1$ to position $i$ and preserves the state, work tape, work-head position, and output (`pal_rewind_step`). The bound $i+1\le |x|$ ensures that this transition lemma applies. The run recurrence expresses the run of $i+1$ steps as this first step followed by a run of $i$ steps (`runFrom_succ_eq_step`); applying the induction hypothesis to the resulting configuration completes the argument.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Complexity.pal_rewind_step`.
