<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean :: Complexity.dataCfg_iterates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iterated Macrosteps Track the Source Run

**Claim.** For every $j\le B$, after $j(18B+8)$ simulator steps from the specified macrostep-check configuration, the simulator is again at macrostep-check with unary head at $j+1$, and its simulated state, saved bit, and encoded data tapes agree with the $j$-step run of $M$.

**Proof.** Induct on $j$. For $j=0$, take both register vectors to be blank and keep the given data tapes. The simulator has taken zero steps, its data component is the prescribed initial data, and the source machine is at its initial configuration with empty output, so its default last output bit is false.

For the successor case, the induction hypothesis supplies the simulator configuration and tapes after $j$ macrosteps, with current payloads encoding the source configuration after $j$ steps. Since $j<B$, the unary tape has a unit marker at coordinate $j+1$, by the unary-marker characterization (`Complexity.unaryTape_unit`). The source payloads vanish outside the radius-$3B$ guide: this follows from the support bound (`Complexity.sourcePayload_support`), using the time bound and the input-length hypothesis. Thus the hypotheses of the one-macrostep simulation result hold. That result (`Complexity.dataCfg_simulates`) advances the simulator by $6(3B)+8$ steps, returns it to macrostep-check, and makes its data tapes encode the next source configuration. The step-count identity $(j+1)(6(3B)+8)=j(6(3B)+8)+(6(3B)+8)$ and the run iteration laws identify this with the asserted run after $(j+1)$ macrosteps. The source successor configuration is its one-step transition from the $j$-step run, by `runFrom_succ_eq_step'`, so the state and defaulted last output bit in the conclusion are the required ones.

**Key facts.** `Complexity.unaryTape_unit`, `Complexity.sourcePayload_support`, `Complexity.dataCfg_simulates`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
