<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine.lean :: Randomized.PolyAmp.Reg.v_9 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register vector entry nine

**Claim.** For every register state $\sigma$, the value of its register vector at position $9$ is its candidate-code register $d$.

**Proof.** By definition, the register vector lists the fields of $\sigma$ in order, with $d$ in position $9$. Evaluating that list at position $9$ gives $\sigma.d$.
