<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZPPEquiv.lean :: Randomized.inZPP_of_mem_ZPPAbort_PTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# From bounded abort machines to zero-error verification

**Claim.** If a finite nondeterministic machine halts within the stated polynomial choice budget, never outputs the incorrect membership bit, and outputs the correct bit with probability at least $1/2$, then the language has an efficient zero-error verifier whose abort probability is at most $1/2$.

**Proof.** Choose the polynomial exponent and coefficient witnessing membership in the abort-machine class. The bounded-halting simulation result (`Randomized.exists_eff_haltRun`) supplies an efficient verifier $M$ whose answer $b$ on a tape of the chosen polynomial length corresponds exactly to the machine halting with output $[b]$. The choice-budget bound (`Turing.choiceBudget_le`) shows that the machine's stipulated choice length fits within this verifier tape length. Because every such run halts, extra tape bits do not change the output (`Turing.NDTM.HaltsWithin.mono` and `Turing.FinNDTM.runWith_eq_runWith_take`).

For any tape, if $M$ answers a bit $b$, the simulated machine has halted with output $[b]$. Its no-wrong-answer hypothesis forces that output to be the membership indicator. Consequently $M$ never returns the wrong bit, whether $x$ is a member or not.

Finally, the event that $M$ aborts is contained in the event that the simulated machine fails to halt with the correct one-bit output. By monotonicity of probability (`Randomized.randProb_mono`), its probability is at most the probability of that failure. The complement rule (`Randomized.randProb_not`) identifies the latter with one minus the probability of correct output. Truncating to the longer tape does not change the probability of an event determined by the first choice-budget bits (`Randomized.randProb_take`), so the assumed correct-output probability of at least $1/2$ gives abort probability at most $1/2$.

**Key facts.** `Randomized.exists_eff_haltRun`, `Turing.choiceBudget_le`, `Turing.NDTM.HaltsWithin.mono`, `Turing.FinNDTM.haltRun_eq_some_iff`, `Turing.FinNDTM.runWith_eq_runWith_take`, `Randomized.randProb_mono`, `Randomized.randProb_not`, `Randomized.randProb_take`.
