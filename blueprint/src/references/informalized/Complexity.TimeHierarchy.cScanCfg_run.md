<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/ClockMachine.lean :: Complexity.TimeHierarchy.cScanCfg_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter-Scan Initialization

**Claim.** For every $j\le |s|$, the clock machine started in its counter-scan state with buffer $s$ and head at $j-1$ reaches the unchanged input configuration after $j+1$ steps, with buffer head at $0$ and state $iStart$.

**Proof.** Proceed by induction on $j$. For $j=0$, the buffer head is at $-1$, where the tape reads none. The counter-scan transition therefore moves the buffer head right and enters $iStart$; together with the unchanged starting configuration, this gives the claimed two-step run, using the zero-run and one-step run equations (`runFrom_zero`, `runFrom_succ_eq_step'`). For the successor case, the head starts at position $j$. Since $j<|s|$, that position contains $s[j]$ (`bufferTape_nat` and the list-index identity). The counter-scan transition moves left when the scanned symbol is present, so one step from the configuration with head at $j$ is exactly the configuration with head at $j-1$, by the counter-action description (`ctrAction_apply`). The induction hypothesis then supplies the remaining $j+1$ steps. The run composition equation (`runFrom_succ_eq_step`) combines these into the required $j+2$ steps, and the bound follows from $j+1\le |s|$.

**Key facts.** `Complexity.TimeHierarchy.clockTM_step_some`, `Complexity.TimeHierarchy.ctrCfg_ctr`, `Complexity.TimeHierarchy.ctrAction_apply`, `Turing.FinTM.bufferTape_left`, `Turing.FinTM.bufferTape_nat`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
