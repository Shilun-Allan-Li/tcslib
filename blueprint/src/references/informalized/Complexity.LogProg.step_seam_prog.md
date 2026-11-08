<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Program.lean :: Complexity.LogProg.step_seam_prog -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compiled Program Step

**Claim.** At a non-call program node, one step of the compiled machine on the extended configuration agrees with extending the ordinary program machine's one-step result.

**Proof.** The seam configuration has compiled state `prog l`, by the hypothesis that the original configuration is in state $l$. Its input symbol is therefore the same as that of the original configuration, and the compiled machine reads the same symbols on the original work tapes. Since $l$ is not a call node, the compiled transition uses the ordinary program transition. It copies that transition's input movement, register writes and movements, output, and successor state to the original tapes and state component. On the added decider tapes it makes no writes or movements, so their blank contents and idle head positions remain unchanged. Comparing these components gives exactly the seam of the ordinary one-step result.
