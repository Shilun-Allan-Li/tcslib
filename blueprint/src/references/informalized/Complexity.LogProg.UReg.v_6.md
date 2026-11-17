<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathMachine.lean :: Complexity.LogProg.UReg.v_6 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scratch Register Entry

**Claim.** For a register record $\sigma$, the value of its register vector at index $6$ is its scratch copy.

**Proof.** By definition, the register vector lists the fields of $\sigma$ in order, with the scratch copy in position $6$. Evaluating that list at index $6$ therefore gives $\sigma.\mathrm{tmp}$.
