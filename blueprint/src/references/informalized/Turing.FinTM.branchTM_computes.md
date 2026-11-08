<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.branchTM_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Branch union computation

**Claim.** The branch union computes output $w$ from input $x$ within $t$ steps exactly when the branch selected by $b$ does.

**Proof.** Split on the Boolean $b$. If $b$ is false, the branch union starts in the right-branch state with the initial configuration of $M_2$ on its own tapes; the extra tapes allocated to the left branch are blank and their heads start at zero. The right-configuration run identity (`Turing.FinTM.rightCfg_run`) then identifies every step of the union machine with the corresponding step of $M_2$, while preserving the added blank tapes. By the computation characterization (`Turing.FinTM.computesInTime_iff`), computation is precisely halting with output $w$ at time $t$; the right-branch state is halting exactly when the simulated state of $M_2$ is halting. If $b$ is true, the same argument uses the left-branch initial configuration and the left-configuration run identity (`Turing.FinTM.leftCfg_run`) to identify the run with that of $M_1$, with its added tapes blank. The halting-state condition and output therefore match in this case as well.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.rightCfg_run`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.leftCfg_run`.
