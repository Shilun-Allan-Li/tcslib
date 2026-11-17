<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.unusedTape_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Compatibility

**Claim.** For a machine with zero work tapes, adding a blank unused tape commutes with one step: stepping the embedded configuration equals embedding the original successor configuration.

**Proof.** Split according to whether the original configuration is already halting. In the halting case both machines leave the configuration unchanged, so the claimed equality follows directly. If the state is some $q$, the added machine's transition was defined to reproduce the original transition, supplying the same input movement, output, and next state while assigning no write and zero movement to its sole work tape. Since the original has no work-tape indices, the transition's work-symbol input agrees with the original configuration's work-symbol function. Thus the two resulting configurations have the same state, input-head position, and output; their work tapes are both blank and their work-head positions are at the origin. These componentwise agreements give equality of configurations.
