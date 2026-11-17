<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARMCompile.lean :: Complexity.LogProg.mcompileTM_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step simulation with appended memory

**Claim.** If no nonhalting state of a configuration enables a memory instruction, then one step of the memory-augmented compiled machine on that configuration with an appended memory tape agrees with taking one deterministic compiled-machine step and then appending the unchanged memory tape and head position.

**Proof.** First split according to whether the original configuration is halting. If its state is absent, both machines leave the configuration unchanged, including the appended tape. Otherwise write its state as $q$. The hypothesis that memory instructions are not enabled at $q$ lets us compare the transition of the augmented machine with the deterministic compiled transition. The fact that deterministic compilation is independent of its chosen fallback answer at such a state (`detM_tr`) identifies the compiled transition with the one used on the deterministic side. The first $m+k_D$ tape symbols read from the appended configuration are exactly those of the original configuration, and the input symbol is unchanged. Finally, applying the resulting lifted action to a configuration with an appended memory tape is the same as applying the original action and then reattaching that tape with its head position unchanged (`liftAct_apply`). This gives the claimed equality after one step.

**Key facts.** `Complexity.LogProg.detM_tr`, `Complexity.LogProg.liftAct_apply`.
