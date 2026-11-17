<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathMachine.lean :: Complexity.LogProg.UReg.v_12 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Column slot

**Claim.** For any register state, the value in slot $12$ of its register vector is its column.

**Proof.** By definition, the register vector lists the state’s fields in order, with the column in position $12$. Evaluating the vector at that position gives the column field.
