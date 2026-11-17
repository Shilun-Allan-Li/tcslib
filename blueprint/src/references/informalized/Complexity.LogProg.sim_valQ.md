<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean :: Complexity.LogProg.sim_valQ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nested-Pair Validation Simulation

**Claim.** For a valid nested-pair input, the validation instruction simulates from state $l$ to state $l'$; for an invalid input, it halts with answer false.

**Proof.** Apply the nested-pair run theorem (`valPair_run`) to the validation routine, using the transition and call equations for the register program (`armProg_tr`, `armProg_call`) and the hypothesis identifying $A(l)$ with the nested-pair validation instruction. The theorem supplies reachability for valid inputs and rejection for invalid inputs, beginning at the configuration with the input head positioned at the routine's start and the selected register head at zero. The identity `xCfg_aseam_self` identifies that repositioned configuration with the given initial configuration, and `xCfg_aseam` identifies the routine's final repositioned configuration with the requested configuration at state $l'$. Convert reachability into the claimed bounded simulation by `simTo_of_reaches`, and rejection into halting with false by `haltsWith_of_rejects`; both use the assumption $W\ge0$.

**Key facts.** `Complexity.LogProg.valPair_run`, `Complexity.LogProg.armProg_tr`, `Complexity.LogProg.armProg_call`, `Complexity.LogProg.xCfg_aseam_self`, `Complexity.LogProg.xCfg_aseam`, `Complexity.LogProg.simTo_of_reaches`, `Complexity.LogProg.haltsWith_of_rejects`.
