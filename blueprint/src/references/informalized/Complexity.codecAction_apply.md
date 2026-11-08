<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecAction_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoded Action Reproduces a Machine Step

**Claim.** Applying the action encoded from a configuration gives exactly the configuration obtained by one step of the machine.

**Proof.** Split according to whether the configuration's state is absent or present. If it is absent, the encoded action is the stationary halting action: it leaves the state absent, does not move either kind of head, writes nothing, and emits no output. Applying it therefore leaves every component of the configuration unchanged, as does the machine's one-step rule in a halted state. If the state is present, the encoded action is exactly the transition action of the machine on the configuration's current input and work-tape symbols. Applying this action is therefore the definition of the machine's one-step update.
