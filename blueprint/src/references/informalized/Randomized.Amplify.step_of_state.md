<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplify.lean :: Randomized.Amplify.step_of_state -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Step determined by phase

**Claim.** If an amplified configuration has phase $p$, then its next configuration under choice bit $b$ is obtained by applying the amplified transition for that phase and the symbols currently under its input and work-tape heads.

**Proof.** The configuration's state is the option value `some p`, by hypothesis. The machine's step rule in a nonhalted state applies its transition function to the current input symbol and work-tape symbols. Substituting the given phase and these symbols yields the stated action applied to the configuration.
