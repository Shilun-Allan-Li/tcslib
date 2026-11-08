<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_copy_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Opening the Guide Copying Stage

**Claim.** Starting in copy-left phase with a blank guide tape and guide head at cell $0$, after two steps the machine reaches the zero-copy phase with the partial guide for zero copied cells; the other data and heads are unchanged.

**Proof.** The first transition leaves the input head in place, moves the guide head one cell left, and enters copy-left-write. The second writes the interior marker at that cell and moves the guide head back to $0$, entering the first-copy phase. Updating the initially blank guide at coordinate $-1$ gives exactly the partial guide for zero copied cells. `setupCfg_apply` records the effects of both actions on the setup configuration; `moveInputPos_zero` ensures the stationary input head retains its position. The run zero and successor laws express these two transitions as the claimed two-step run.

**Key facts.** `Complexity.setupCfg_apply`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.moveInputPos_zero`.
