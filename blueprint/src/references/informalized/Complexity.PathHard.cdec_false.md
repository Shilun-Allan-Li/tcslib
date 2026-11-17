<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardWalk.lean :: Complexity.PathHard.cdec_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deciding a false proposition

**Claim.** If a proposition $P$ is false, its classical Boolean decision value is false.

**Proof.** The hypothesis says there is no proof of $P$. The classical decision procedure therefore selects the negative case, so the Boolean value of the decision is false (`decide_eq_false`).
