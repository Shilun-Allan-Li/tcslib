<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arTM_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation time bound

**Claim.** If the source machine halts after exactly $t$ steps and outputs the letterwise encoding of $w$, then the binary simulator computes $w$ after $(3(N+1)+2)t$ steps.

**Proof.** Rewrite the source computation claim using the characterization of computation in terms of the run's halting state and output (`computesInTime_iff`). The simulator's initial configuration is the encoding of the source initial configuration (`arCfg_init`), and its run for $(3(N+1)+2)t$ steps equals the encoding of the source run after $t$ steps (`arCfg_run`). The source run's halting state therefore gives the simulator's halting state. Its output is the source output mapped through the bit decoder; on each encoded bit, the decoder returns that bit (`arBit_embed`). Since the source output is the letterwise image of $w$, the simulator output is $w$. The computation characterization now yields the claim.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.arCfg_init`, `Turing.FinTM.arCfg_run`, `Turing.FinTM.arBit_embed`.
