<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Frag.lean :: Complexity.LogProg.half_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register halving computation

**Claim.** Under the specified end-marker and halving transitions, the program can transform the binary word for $n$ into the binary word for $\lfloor n/2\rfloor$, with its head at zero, and all earlier configurations satisfy the stated head-position and non-call-state bounds.

**Proof.** Let $w$ be the binary word for $n$. First use the end-marker run result (`toEnd_run`) with the head starting at zero: after $|w|+1$ steps the program is in state $h_0$, with the word unchanged and the head at $|w|-1$. It also supplies the required bounds and non-call-state condition throughout this first phase.

Next apply the leftward halving run result (`halfL_run`) with $k=|w|$. The bit at that index is absent, so this phase starts in $h_0$ with the entire word in place and head at $|w|-1$. After another $|w|+1$ steps it reaches `next`, with the tail of $w$ and head at zero; its intermediate configurations satisfy the corresponding bounds. The binary-word identity `bits_half` identifies that tail with the binary word for $\lfloor n/2\rfloor$. Concatenating the two runs using `rrun_add` gives the claimed total run. For an earlier time, split according to whether it lies before or after the first phase ends. The first phase's bound applies in the former case; in the latter, its endpoint is the starting configuration for the second phase, whose intermediate-time bound applies.

**Key facts.** `Complexity.LogProg.toEnd_run`, `Complexity.LogProg.halfL_run`, `Complexity.LogProg.bits_half`, `Complexity.LogProg.rrun_add`.
