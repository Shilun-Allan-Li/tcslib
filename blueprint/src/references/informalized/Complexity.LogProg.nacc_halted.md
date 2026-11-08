<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMKit.lean :: Complexity.LogProg.nacc_halted -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance from a Halted Configuration

**Claim.** A halted configuration with recorded answer $res$ is accepting exactly when $res$ is true.

**Proof.** For the forward implication, an accepting run supplies a choice sequence whose resulting answer is true. Starting from a halted configuration, every choice sequence leaves it fixed: this follows immediately by induction on the sequence, since each step from a halted state is fixed. Hence the resulting answer is the original $res$, so $res$ must be true. Conversely, if $res$ is true, choose the empty sequence. It leaves the configuration unchanged, which is halted and has true answer, so it witnesses acceptance.
