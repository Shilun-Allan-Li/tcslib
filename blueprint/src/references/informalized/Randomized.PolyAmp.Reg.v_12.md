<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine.lean :: Randomized.PolyAmp.Reg.v_12 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Thirteenth Register Value

**Claim.** For any register record $\sigma$, the value of its register-value function at coordinate $12$ is the scratch value for the digit count and the comparison.

**Proof.** By definition, coordinate $12$ of the register-value vector is $\sigma.t$. Evaluating the vector at that coordinate yields the stated equality.
