<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathMachine.lean :: Complexity.LogProg.UReg.v_13 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scratch sum slot

**Claim.** For any register state, the value in slot $13$ of its register vector is its scratch sum.

**Proof.** The register vector is defined by listing the state’s fields in order, and the scratch sum occupies position $13$. Thus its value at that position is exactly the scratch sum field.
