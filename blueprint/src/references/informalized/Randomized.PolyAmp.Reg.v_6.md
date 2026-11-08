<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine.lean :: Randomized.PolyAmp.Reg.v_6 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register vector entry six

**Claim.** For every register state $\sigma$, the value of its register vector at position $6$ is its remaining-runs register $i$.

**Proof.** By definition, the register vector lists the fields of $\sigma$ in order, with $i$ in position $6$. Evaluating that list at position $6$ gives $\sigma.i$.
