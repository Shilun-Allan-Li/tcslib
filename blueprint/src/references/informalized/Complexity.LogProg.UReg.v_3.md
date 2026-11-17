<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathMachine.lean :: Complexity.LogProg.UReg.v_3 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inner counter slot

**Claim.** For a register record $\sigma$, the value of its register vector at index $3$ is its inner counter.

**Proof.** By the definition of the register vector, the inner counter is listed at index $3$. Therefore evaluating the vector at that index yields the inner counter field.
