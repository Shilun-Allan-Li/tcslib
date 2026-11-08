<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine.lean :: Randomized.PolyAmp.Reg.v_10 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Eleventh Register Value

**Claim.** For any register record $\sigma$, the value of its register-value function at coordinate $10$ is the number of coins left.

**Proof.** The register-value function is defined by a length-$15$ vector whose entries, in order, include $\sigma.j$ at coordinate $10$. Evaluating that vector at this coordinate therefore gives $\sigma.j$, as claimed.
