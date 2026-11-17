<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/ThirdMoments.lean :: BooleanAnalysis.GaussianSpace.Invariance.third_moment_le_of_three_norm_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Third Moment from the Third Norm

**Claim.** If $Z$ belongs to $L^3(\mu)$, $B\ge0$, and $N_3(Z)^2\le B$, then $\int |Z|^3\,d\mu\le B^{3/2}$.

**Proof.** The norm-to-moment identity gives $N_3(Z)^3=\int |Z|^3\,d\mu$ (`rvLpNorm_rpow`). Since $N_3(Z)\ge0$, rewrite this as $\int |Z|^3\,d\mu=(N_3(Z)^2)^{3/2}$. The function $x\mapsto x^{3/2}$ is increasing on nonnegative reals, so the assumed bound $N_3(Z)^2\le B$ implies the result.

**Key facts.** `BooleanAnalysis.Hypercontractivity.rvLpNorm_rpow`.
