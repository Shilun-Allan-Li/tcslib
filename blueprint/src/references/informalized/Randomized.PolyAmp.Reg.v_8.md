<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine.lean :: Randomized.PolyAmp.Reg.v_8 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register vector entry eight

**Claim.** For every register state $\sigma$, the value of its register vector at position $8$ is its current-code register $c$.

**Proof.** By definition, the register vector lists the fields of $\sigma$ in order, with $c$ in position $8$. Evaluating that list at position $8$ gives $\sigma.c$.
