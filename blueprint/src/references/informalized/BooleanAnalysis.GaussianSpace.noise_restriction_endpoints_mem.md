<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Noise.lean :: BooleanAnalysis.GaussianSpace.noise_restriction_endpoints_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Range of noised restriction endpoints

**Claim.** If a Boolean function takes values in $[0,1]$ and $0\leq\rho\leq1$, then at every point the sum and difference of the noises of its last-coordinate average and half-difference both belong to $[0,1]$.

**Proof.** Apply the range-preservation property of the noise operator separately to the restrictions of $f$ at the last bit $0$ and at the last bit $1$. Each restriction still takes values in $[0,1]$, so both of its noisy values lie in that interval (`noiseOp_mem_unitInterval`). The restriction identity (`noiseOp_restrictLast_eq`) identifies the value for bit $0$ with the sum of the noise of the average and that of the half-difference, since the sign of $0$ is $1$. For bit $1$, its sign is $-1$, so the identity gives the corresponding difference. Both expressions therefore lie in $[0,1]$.

**Key facts.** `BooleanAnalysis.GaussianSpace.noiseOp_mem_unitInterval`, `BooleanAnalysis.GaussianSpace.noiseOp_restrictLast_eq`, `BooleanAnalysis.boolToSign_false`, `BooleanAnalysis.boolToSign_true`.
