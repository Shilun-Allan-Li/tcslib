<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathMachine.lean :: Complexity.LogProg.UReg.v_9 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Saved Field Position Entry

**Claim.** For a register record $\sigma$, the value of its register vector at index $9$ is its saved field position.

**Proof.** By definition, the register vector lists the fields of $\sigma$ in order, with the saved field position in position $9$. Evaluating that list at index $9$ gives $\sigma.\mathrm{q}$.
