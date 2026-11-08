<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARMTime.lean :: Complexity.LogProg.last_tape_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Persistence on the Last Tape

**Claim.** At every time, each cell of the last work tape is either blank or contains true. Once a cell contains true, it remains true at every later time.

**Proof.** We prove the two assertions separately. For the first, use induction on time. At time zero every cell is blank, by the definition of the initial configuration. For the step, the next run configuration is obtained by taking one machine step. The one-step fact that a last-tape cell either keeps its previous contents or becomes true (`Complexity.LogProg.step_last_cell`) shows that a cell previously blank or true is still blank or true. This proves the assertion at every time.\n\nFor persistence, write the later time as the earlier time plus a nonnegative number of steps, which is possible because the earlier time is at most the later one. Induct on that number. With zero steps the claim is the given hypothesis. For the successor step, apply the same one-step fact to the cell. If its contents are unchanged, the induction hypothesis applies; if the cell becomes true, the desired conclusion holds directly. The identification of each next run configuration with one step after the current configuration is supplied by `Turing.MultiTapeTM.runFrom_succ_eq_step'`.

**Key facts.** `Complexity.LogProg.step_last_cell`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
