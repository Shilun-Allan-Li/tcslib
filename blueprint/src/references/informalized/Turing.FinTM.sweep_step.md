<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.sweep_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Bounded Simulation Burst

**Claim.** Given the stated head bounds and blank cells at both ends of the zone, the simulator carries out one source-machine step in $(2n+5)k+4$ steps and reaches the canonical configuration for the successor with zone enlarged by one block at each end and frontier $z-k$.

**Proof.** Split the stated duration into the preparation time $k+1+(n+1)k+1$ and the finishing time $k+1+(n+2)k+1$; their sum is $(2n+5)k+4$. Run additivity (`runFrom_add`) allows these phases to be applied consecutively. The preparation lemma (`sweep_prepare`) scans and reads the current zone, reaching the right-extension state with the read table and enlarged flagged zone. The finishing lemma (`sweep_finish`) then performs the source transition and returns to the canonical sweep configuration for the successor. The intermediate frontier advances during preparation and shifts during finishing; simplifying these contributions yields $z-k$. By the definition of the source machine's step, its transition action applied to $c$ is exactly the resulting successor configuration.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.sweep_prepare`, `Turing.FinTM.sweep_finish`.
