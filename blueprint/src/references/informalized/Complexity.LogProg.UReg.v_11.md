<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathMachine.lean :: Complexity.LogProg.UReg.v_11 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Candidate vertex slot

**Claim.** For any register state, the value in slot $11$ of its register vector is its row or candidate vertex.

**Proof.** By definition, the register vector lists the state’s fields in order, with the row or candidate vertex in position $11$. Evaluating the vector at that position therefore gives the field directly.
