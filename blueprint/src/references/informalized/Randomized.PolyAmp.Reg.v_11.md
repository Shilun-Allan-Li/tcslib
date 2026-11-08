<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine.lean :: Randomized.PolyAmp.Reg.v_11 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Twelfth Register Value

**Claim.** For any register record $\sigma$, the value of its register-value function at coordinate $11$ is the scratch value for the copies and the power.

**Proof.** The register-value function is defined by a length-$15$ vector with $\sigma.z$ at coordinate $11$. Evaluating the vector there gives $\sigma.z$.
