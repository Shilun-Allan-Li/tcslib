<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Wrappers.lean :: Turing.FinTM.redirect_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step correspondence under redirection

**Claim.** Starting from the redirected image of an original configuration, one step of the redirected machine yields the redirected image of the configuration obtained by one step of the original machine.

**Proof.** Split according to whether the original configuration is halted. If it is halted, the original machine's step leaves it fixed (`MultiTapeTM.step_of_halt`). When its last output bit is $b$, the redirected image is also halted and likewise remains fixed. When that bit is not $b$, the redirected image is in the loop state, and the loop fixed-point lemma shows that one step leaves it fixed (`redirect_loop`). In either case the two sides agree. If the original configuration is live, the redirected image is a live paired state with the same input symbol and work-tape symbols as the original configuration. The redirected transition is exactly the redirected version of the original transition action; this follows by splitting on whether that action halts and whether it emits a bit. Applying the action-commutation lemma then identifies the resulting configuration with the redirected image of the original next configuration (`redirect_apply`).

**Key facts.** `Turing.MultiTapeTM.step_of_halt`, `Turing.FinTM.redirect_loop`, `Turing.FinTM.redirect_apply`.
