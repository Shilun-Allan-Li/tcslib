<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arWriteCfg_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Running the write sweep

**Claim.** For every $j\le N$, running the simulator for $j+1$ steps from the write-sweep configuration at counter $j$ reaches the move-sweep configuration at counter $N+1$.

**Proof.** Induct on $j$. When $j=0$, the assertion is exactly the one-step completion of the write sweep (`arWriteCfg_finish`). For the successor case, the hypothesis $j+1\le N$ ensures that the counter at $j+1$ is nonzero and remains in the write-sweep range. The simulator's next-step rule (`arWriteCfg_step`) therefore takes the configuration at counter $j+1$ to the one at counter $j$. Splitting off this first step from the iterate (`runFrom_succ_eq_step`) leaves a run of $j+1$ steps from counter $j$; the induction hypothesis applies because $j\le N$. Its endpoint is the required move-sweep configuration.

**Key facts.** `Turing.FinTM.arWriteCfg_finish`, `Turing.FinTM.arWriteCfg_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
