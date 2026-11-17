<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathMachine.lean :: Complexity.LogProg.UReg.v_7 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Step Count Register Entry

**Claim.** For a register record $\sigma$, the value of its register vector at index $7$ is its step count.

**Proof.** By definition, the register vector lists the fields of $\sigma$ in order, with the step count in position $7$. Evaluating that list at index $7$ gives $\sigma.\mathrm{st}$.
