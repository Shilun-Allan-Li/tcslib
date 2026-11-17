<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathMachine.lean :: Complexity.LogProg.UReg.v_2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Outer counter slot

**Claim.** For any register state, the value in slot $2$ of its register vector is its row or outer counter.

**Proof.** The register vector lists the state’s fields in order, and the row or outer counter is the field in position $2$. Hence the value at that position is the outer counter.
