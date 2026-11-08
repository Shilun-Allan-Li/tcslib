<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMCompile.lean :: Complexity.LogProg.ctr_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Congruence of Compiled Transitions

**Claim.** If two register programs have identical call specifications and their ordinary transitions agree at the program-running state under consideration, then their compiled one-step actions agree at that compiled state.

**Proof.** Fix the input symbol and work-tape contents, so it suffices to compare the resulting actions. Split according to the form of the compiled state. In a program-running state, identical call specifications make both compilations take the same call or non-call branch; in the non-call branch, the assumed equality of ordinary transitions makes the actions identical. In a decider-simulation state and in the two input-return states, the actions depend on the programs only through their call specifications, so the shared call map gives equality. In a register-return state the same is true: the return action is determined by the call specification and the current tape contents. Thus the actions agree in every state case.
