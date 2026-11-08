<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/HammingBallLimit.lean :: FABL.tendsto_expect_normalizedRademacherStopLoss -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rademacher Stop-Loss Limit

**Claim.** For each real $t$, the expected positive part of the normalized Rademacher sum in dimension $m+1$ minus $t$ converges to the expected positive part of a standard Gaussian minus $t$.

**Proof.** There is a positive constant $C$ such that, for every $m$ and $t$, the absolute difference between these expectations is bounded by $C$ times the normalized Rademacher coefficient in dimension $m+1$ (`exists_normalizedRademacherStopLoss_bound`). That coefficient tends to zero (`tendsto_normalizedRademacherCoefficient_succ`), so the bound tends to zero for the fixed $t$. The distance between the two expectations is nonnegative and squeezed by this vanishing bound, giving the limit.

**Key facts.** `FABL.exists_normalizedRademacherStopLoss_bound`, `FABL.tendsto_normalizedRademacherCoefficient_succ`.
