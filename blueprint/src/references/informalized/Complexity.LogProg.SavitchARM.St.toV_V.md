<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean :: Complexity.LogProg.SavitchARM.St.toV_V -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Target code register coordinate

**Claim.** For a state of the Savitch machine, the coordinate at index $11$ in its 18-entry register vector equals the value of its current-node target-code register $V$.

**Proof.** The target-code register $V$ occurs at index $11$ in the ordered register vector. Since $r_V$ denotes this index, evaluating the vector there gives $V$.
