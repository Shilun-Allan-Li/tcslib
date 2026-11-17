<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.tendsto_expect_hammingUpperTailIndicator_of_tail_tendsto -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tail Limit from Gaussian Tails

**Claim.** If the dimensions $d(q)$ tend to infinity and the standard Gaussian upper tails at thresholds $u(q)$ converge to $L$, then the expected indicator that the normalized Rademacher sum in dimension $d(q)$ exceeds $u(q)$ also converges to $L$.

**Proof.** Compare the expectation first with the Gaussian upper tail at the same threshold $u(q)$, and then with $L$. The triangle inequality bounds the absolute error by the sum of these two differences. Eventually $d(q)\ge 1$, so the Berry–Esseen bound (`abs_expect_hammingUpperTailIndicator_dimension_le`) makes the first difference at most $2C(\sqrt{d(q)})^{-1}$. Since $d(q)\to\infty$, this bound tends to zero. The second difference tends to zero by the assumed convergence of the Gaussian tails. Thus the total error tends to zero, proving the result.

**Key facts.** `FABL.abs_expect_hammingUpperTailIndicator_dimension_le`.
