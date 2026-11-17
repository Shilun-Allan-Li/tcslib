<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridge_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Unfolding of the Bridging Machine

**Claim.** A single step from the bridge configuration determined by a control state, input position, stack assignment, and output is the result of applying the transition action selected by that state and the symbols under the input and work-tape heads.

**Proof.** The machine's step is defined by inspecting its current state. In the configuration at issue the state is present, so the step takes the transition action for that state, the current input symbol, and the tuple of work-tape symbols, then applies that action to the configuration. This is exactly the asserted equality.
