<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathMachine.lean :: Complexity.LogProg.UReg.v_10 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Walk Length Slot

**Claim.** For any register state, slot $10$ of its register vector contains its walk length.

**Proof.** The register-value vector lists the state’s fields in register order, and the walk length is the field at position $10$. Evaluating the vector at that position gives the walk length.
