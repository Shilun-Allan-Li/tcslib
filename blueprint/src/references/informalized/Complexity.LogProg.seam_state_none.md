<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Program.lean :: Complexity.LogProg.seam_state_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting State Under the Seam

**Claim.** If a configuration has no state, then its seam also has no state.

**Proof.** The state of the seam is obtained by mapping the original optional state through the injection into program states. Mapping the absent value leaves it absent, so the seam's state is none.
