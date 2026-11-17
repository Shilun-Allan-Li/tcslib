<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/Examples.lean :: Complexity.pal_copy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copy-Phase Configuration Invariant

**Claim.** After $t\le |x|$ steps from the initial configuration, the machine is in state $0$, its input head is at position $t+1$, its work head is at cell $t$, the first $t$ bits of $x$ are copied to the work tape, all other cells are blank, and the output is empty.

**Proof.** Induct on $t$. At $t=0$, the initial configuration has state $0$, input head at position $1$, work head at cell $0$, blank work tape, and empty output. These are exactly the asserted values for the empty copied prefix. For the successor step, assume the stated configuration after $t$ steps. Since $t+1\le |x|$, we have $t<|x|$, so the single copy-phase transition applies: it advances the input head to $t+2$, writes $x_t$ at work cell $t$, advances the work head to $t+1$, and leaves the state and output as specified. The tape-update fact that writing $x_t$ at cell $t$ extends the copied prefix by one bit is `palTape_write`; the transition itself is `pal_copy_step`. Finally, iteration satisfies the recurrence that a run of $t+1$ steps is one step followed by a run of $t$ steps (`runFrom_succ_eq_step'`).

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.pal_copy_step`.
