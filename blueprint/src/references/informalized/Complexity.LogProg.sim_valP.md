<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean :: Complexity.LogProg.sim_valP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary and Payload Validation Simulation

**Claim.** For a valid unary–payload input, the validation instruction simulates from state $l$ to state $l'$; for an invalid input, it halts with answer false.

**Proof.** The proof first applies the valid-payload run theorem (`valPlain_run`) to the validation machine whose initial, intermediate, and final states are the prescribed validation phases. The transition and call equations for the register program (`armProg_tr`, `armProg_call`), together with the hypothesis that $A(l)$ is the validation instruction, identify its actual transitions and show that these phases follow the validation routine. That run theorem gives reachability on valid inputs and rejection on invalid ones, with the run based at the configuration obtained by positioning the input head at the initial validation state and the selected register head at zero. The initial configuration is exactly this repositioned configuration (`xCfg_aseam_self`); at the end, repositioning to state $l'$ yields the desired configuration (`xCfg_aseam`). Finally, reachability implies the stated space-bounded simulation (`simTo_of_reaches`), and rejection implies halting with false (`haltsWith_of_rejects`), using $W\ge0$ in both implications.

**Key facts.** `Complexity.LogProg.valPlain_run`, `Complexity.LogProg.armProg_tr`, `Complexity.LogProg.armProg_call`, `Complexity.LogProg.xCfg_aseam_self`, `Complexity.LogProg.xCfg_aseam`, `Complexity.LogProg.simTo_of_reaches`, `Complexity.LogProg.haltsWith_of_rejects`.
