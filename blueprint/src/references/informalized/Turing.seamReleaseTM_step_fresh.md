<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Seam.lean :: Turing.seamReleaseTM_step_fresh -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Seam-Release Step

**Claim.** If the original configuration is in the anchor state, then one seam-release step from its left-summand renaming is the original machine’s next configuration with its state renamed into the right summand.

**Proof.** Because the state is `some anchor`, the original machine takes its transition at the anchor state. The seam-release machine, when in the left summand, is defined to use precisely that same transition, while mapping its successor state through the right-summand injection. The input and work-tape actions and output are therefore identical, and the resulting configuration agrees in every field with the original next configuration after its state is renamed. This proves the equality.
