<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.toV_wT -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Selected register value

**Claim.** For any state and Boolean $b$, the value of the register selected by $b$ is $u$ when $b$ is true and $v$ when $b$ is false.

**Proof.** If $b$ is true, the selected register is the one storing $u$, so its value is $u$. If $b$ is false, the selected register is the one storing $v$, so its value is $v$. The two cases give the asserted conditional.
