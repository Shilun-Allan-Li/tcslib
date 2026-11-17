<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.bufferedSecondCfg_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second-phase lockstep simulation

**Claim.** Starting from a second-phase configuration whose tag satisfies the boundary condition, after any number $t$ of steps the buffered composition matches the corresponding run of $M_2$ with the same physical input position and left-block data, for some tag satisfying the boundary condition at the resulting virtual input-head position.

**Proof.** Induct on $t$. At time zero, choose the original tag: the boundary condition is the hypothesis, and the two configurations are identical. For the successor step, the induction hypothesis supplies a tag for the time-$t$ configuration and identifies the buffered run with its second-phase embedding. Apply the one-step second-phase simulation lemma (`bufferedSecondCfg_step`) to that configuration and tag. It supplies a new tag satisfying the boundary condition after one step and identifies the buffered successor with the embedding of the machine's successor. The successor-time run identity (`runFrom_succ_eq_step'`) rewrites both runs in this form, yielding the claim.

**Key facts.** `Turing.FinTM.bufferedSecondCfg_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
