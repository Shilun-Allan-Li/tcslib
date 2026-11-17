<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean :: Turing.release_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Releasing the Distinguished Start State

**Claim.** If a configuration in the disjoint union of a singleton and $S$ is in the singleton start state, mapping its state through the chosen anchor and then back to the singleton start state leaves the configuration unchanged.

**Proof.** The hypothesis fixes the configuration's state as the left-summand element. The first state map sends it to the anchor, and the second sends that anchor to the same left-summand element. Every other component of the configuration—input position, work tapes, work-head positions, and output—is unchanged by both state maps. Hence the resulting configuration equals the original.
