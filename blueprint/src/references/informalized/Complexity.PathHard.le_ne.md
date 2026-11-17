<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardMachine.lean :: Complexity.PathHard.le_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Separation in Comparisons

**Claim.** In either comparison phase, the scratch register is distinct from the register representing the unary-block length or adjacency-word length, as appropriate.

**Proof.** There are two comparison phases. In the unary-block phase the comparison register is the register for the unary-block length; in the adjacency-word phase it is the register for the adjacency-word length. In each case the scratch register has a different register index, so the required inequalities hold by direct evaluation of the two cases.
