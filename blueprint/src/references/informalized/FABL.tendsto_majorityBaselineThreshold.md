<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.tendsto_majorityBaselineThreshold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority Baseline Threshold Limit

**Claim.** If $m(q)$ tends to infinity, then $-1/\sqrt{k(q)+m(q)}$ tends to zero, for any natural-number sequence $k$.

**Proof.** Since $k(q)\ge0$, the sum $k(q)+m(q)$ is at least $m(q)$, so it tends to infinity. Its real-valued version therefore tends to infinity, and so does its square root. The reciprocal of a quantity tending to infinity tends to zero; negating that reciprocal preserves the zero limit. The resulting expression is exactly $-1/\sqrt{k(q)+m(q)}$.
