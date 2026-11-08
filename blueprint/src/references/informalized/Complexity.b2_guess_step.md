<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_guess_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Guessing-Phase Step

**Claim.** From an active scheduler configuration, one host step advances the normalized scheduler and appends the choice bit exactly when that scheduler step emits.

**Proof.** Since $c$ is active, write its state as $q$. The host is then in its scheduler-simulation branch. Its transition is the lifted transition of the continuation machine, with the extra verifier tapes left unchanged. The lifting property says that applying such a lifted action to the lifted configuration is the lift of applying the original action (`leftCfg_apply`). The continuation-machine step lemma identifies that latter step: it advances the simulated scheduler and, when its transition emits, records the current choice bit on the auxiliary tape; otherwise it records nothing (`cont_guess_step`). The scheduler output itself is suppressed, while the recorded bit is appended to the guessed-word buffer precisely in the emission case. This gives the claimed next guessing-phase configuration.

**Key facts.** `Turing.FinTM.leftCfg_apply`, `Complexity.cont_guess_step`.
