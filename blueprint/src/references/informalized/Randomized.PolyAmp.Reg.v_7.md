<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine.lean :: Randomized.PolyAmp.Reg.v_7 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register vector entry seven

**Claim.** For every register state $\sigma$, the value of its register vector at position $7$ is its accepting-runs register $cnt$.

**Proof.** By definition, the register vector lists the fields of $\sigma$ in order, with $cnt$ in position $7$. Evaluating that list at position $7$ gives $\sigma.cnt$.
