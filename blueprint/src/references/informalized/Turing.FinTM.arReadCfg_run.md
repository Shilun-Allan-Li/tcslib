<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arReadCfg_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evolution Through the Read Sweep

**Claim.** If the original configuration is in state $q$, then for every $j\le N+1$, running the simulator for $j$ steps from its encoded configuration yields the read-sweep configuration at counter $j$.

**Proof.** Proceed by induction on the number of steps $j$. At $j=0$, the read-sweep configuration at counter zero equals the encoded configuration, using the assumption that the original configuration is in state $q$ (`Turing.FinTM.arReadCfg_zero`). For the successor case, suppose the assertion holds at $j$ and $j+1\le N+1$. The run recurrence identifies the run for $j+1$ steps with one simulator step after the run for $j$ steps (`Turing.MultiTapeTM.runFrom_succ_eq_step'`). The induction hypothesis makes that intermediate configuration the read-sweep configuration at counter $j$. Since the bound on $j+1$ implies $j<N+1$, the one-step read-sweep rule advances it to counter $j+1$ (`Turing.FinTM.arReadCfg_step`).

**Key facts.** `Turing.FinTM.arReadCfg_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.arReadCfg_step`.
