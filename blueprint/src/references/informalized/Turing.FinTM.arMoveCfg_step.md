<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arMoveCfg_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Move Sweep Countdown

**Claim.** When the move-sweep counter $r$ is nonzero, one simulator step takes the move-sweep configuration at counter $r$ to the same configuration at counter $r-1$.

**Proof.** The configuration is in the move-sweep phase, so the simulator’s transition uses its nonzero-counter branch. That branch makes no changes to the encoded tape contents, input position, output, or pending action; it only decreases each encoded work-head position by one block length. The target configuration uses the same pending action and counter $r-1$. Since the position formula is $\mathrm{base}+(N+1-r)\,d$, replacing $r$ by $r-1$ increases the offset by $d$. This is exactly the head movement prescribed by the pending action, so the resulting positions and all other configuration fields agree.
