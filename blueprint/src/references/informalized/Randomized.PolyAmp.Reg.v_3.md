<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine.lean :: Randomized.PolyAmp.Reg.v_3 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value in Register Position Three

**Claim.** For every register state $\sigma$, the value of its register vector at position $3$ is its exponent register $e$.

**Proof.** By the definition of the register vector, its entry at position $3$ is $\sigma.e$. Evaluating at that position gives the asserted equality.
