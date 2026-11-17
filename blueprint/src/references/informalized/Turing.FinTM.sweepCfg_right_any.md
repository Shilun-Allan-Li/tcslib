<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Sweep.lean :: Turing.FinTM.sweepCfg_right_any -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Forward Sweep Beyond the Stored Zone

**Claim.** Applying the right-moving write action advances the frontier to $z+1$, places $b$ at the head of the left stack, and replaces the right stack by its tail, while preserving the input position and output.

**Proof.** If $r$ is nonempty, write it as $a::r'$. The one-step forward sweep update gives the result directly, with right stack $r'$, by `sweepCfg_right`. If $r$ is empty, the tape representation is unchanged when an explicit blank cell is appended to the right stack (`sweepTape_nil`). Thus the configuration with empty right stack can first be identified with the one having right stack $[\mathrm{none}]$. Applying the forward sweep update to that representation removes the explicit blank and yields the claimed empty tail.

**Key facts.** `Turing.FinTM.sweepCfg_right`, `Turing.FinTM.sweepTape_nil`.
