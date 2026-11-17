<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Linear.lean :: BooleanAnalysis.GaussianSpace.sum_sq_projectionCoefficients -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expansion of Squared Coefficients

**Claim.** For real coefficient lists $a,b$ and scalars $u,v$, the sum of $(u a_i+v b_i)^2$ expands into the weighted sums of $a_i^2$, $a_i b_i$, and $b_i^2$.

**Proof.** Expand each summand using the real algebraic identity $(u a_i+v b_i)^2=u^2a_i^2+2uv(a_i b_i)+v^2b_i^2$. Summing these identities separates the sum into three sums, and factoring out the constants $u^2$, $2uv$, and $v^2$ yields the claimed formula.
