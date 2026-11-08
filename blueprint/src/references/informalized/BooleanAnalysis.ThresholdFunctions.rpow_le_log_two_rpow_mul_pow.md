<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/NoiseStability.lean :: BooleanAnalysis.ThresholdFunctions.rpow_le_log_two_rpow_mul_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power bound across exponents

**Claim.** If $\log 2\le L$, $0\le E$, and $E\le d$, then $L^E\le (\log 2)^{-d}L^d$.

**Proof.** Since $\log 2>0$, we have $L>0$. Also $\log 2<1$, so its power $(\log 2)^{-d}$ is at least $1$. Split into two cases. If $L\ge1$, increasing the exponent from $E$ to $d$ can only increase the power, giving $L^E\le L^d$; multiplying by a factor at least $1$ preserves the desired bound. If $L<1$, the nonnegative exponent gives $L^E\le1$. Meanwhile $L\ge\log 2$ implies $L^d\ge(\log 2)^d$, so $(\log 2)^{-d}L^d\ge1$. This proves the bound in either case.
