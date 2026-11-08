<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Seam.lean :: Turing.seamReleaseTM_step_inr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Seam-Release Step in the Right Summand

**Claim.** For any configuration, one seam-release step from its right-summand state renaming agrees with the original machine’s next step, with the resulting state renamed into the right summand.

**Proof.** Split according to whether the original configuration is halted. If its state is `none`, renaming leaves it halted, and both machines stay at the same configuration; the state renaming on the right also leaves `none` unchanged. If its state is `some q`, the renamed configuration has state `some (Sum.inr q)`. In the right summand, the seam-release transition applies the original transition at `q`, with the same tape readings and actions, and maps its optional successor state through `Sum.inr`. Thus the updated tapes, head positions, output, and renamed successor state agree with the original step followed by state renaming.
