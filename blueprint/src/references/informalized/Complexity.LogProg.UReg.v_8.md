<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathMachine.lean :: Complexity.LogProg.UReg.v_8 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Random Index Register Entry

**Claim.** For a register record $\sigma$, the value of its register vector at index $8$ is its random index.

**Proof.** By definition, the register vector lists the fields of $\sigma$ in order, with the random index in position $8$. Evaluating that list at index $8$ gives $\sigma.\mathrm{nx}$.
