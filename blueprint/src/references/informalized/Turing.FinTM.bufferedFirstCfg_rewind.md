<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.bufferedFirstCfg_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewind and Dispatch Duration

**Claim.** From a first-phase configuration determined by a halted configuration $c$ of $M_1$, the buffered composition reaches after $|c.\mathrm{output}|+2$ steps the second-phase configuration determined by $M_2$'s initial configuration on that output, with the tag true and the physical input position and left-block data preserved.

**Proof.** Since $c$ is halted, one step of the composite machine leaves the simulated first-machine state halted and begins the buffer scan. The resulting configuration is the scan configuration with the scan head at the initial position; the physical input position stays fixed because the transition moves it by zero (`Turing.moveInputPos_zero`). The remaining scan-run lemma states that starting from scan position $j$, with $j\le |c.\mathrm{output}|$, the composition reaches the second-phase embedding of $M_2$'s initial configuration after $j+1$ further steps, preserving the physical input position and left-block data (`Turing.FinTM.bufferedScanCfg_run`). Apply this at the full output length. Together with the initial step, the total is $1+(|c.\mathrm{output}|+1)=|c.\mathrm{output}|+2$, as claimed; the run-splitting identity for a successor time justifies combining that first step with the scan run (`Turing.MultiTapeTM.runFrom_succ_eq_step`).

**Key facts.** `Turing.moveInputPos_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.FinTM.bufferedScanCfg_run`.
