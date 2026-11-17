<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine.lean :: Randomized.PolyAmp.Reg.v_5 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register vector entry five

**Claim.** For every register state $\sigma$, the value of its register vector at position $5$ is its run-count register $R$.

**Proof.** By definition, the register vector lists the fields of $\sigma$ in order, with $R$ in position $5$. Evaluating that list at position $5$ therefore gives $\sigma.R$.
