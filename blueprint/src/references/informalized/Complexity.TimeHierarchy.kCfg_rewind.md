<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/ClockMachine.lean :: Complexity.TimeHierarchy.kCfg_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding after halting

**Claim.** If $K$ is in a halting configuration $c$, then after $|c.\mathrm{output}|+2$ steps from its lift, the clock machine has rewound to the start of its input scan, with the stated tape contents, head positions, and empty output.

**Proof.** From the lifted halting configuration, the clock machine takes one step into its counter-scan state, moving the counter head left from the output-length position. The counter-scan routine then traverses the stored output and, on its final scan step, moves the counter head back to cell $0$ and enters the input-rewind phase. The supplied scan lemma (\texttt{cScanCfg_run}) says that from the corresponding scan configuration, after $j+1$ steps for $j\le |c.\mathrm{output}|$, the machine is in state $\mathrm{iStart}$, with the counter storing the output at head position $0$, the original $K$ tapes and heads preserved, the $W$ tapes blank at head position $0$, and empty output. Taking $j=|c.\mathrm{output}|$ gives the claimed total of $|c.\mathrm{output}|+2$ steps. The proof identifies the first step with the counter-scan configuration using the clock transition rule (\texttt{clockTM_step_some}) and the effect of a counter action (\texttt{ctrAction_apply}); the time composition uses the successor-run identity (\texttt{runFrom_succ_eq_step}).

**Key facts.** `Complexity.TimeHierarchy.clockTM_step_some`, `Complexity.TimeHierarchy.ctrAction_apply`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Complexity.TimeHierarchy.cScanCfg_run`.
