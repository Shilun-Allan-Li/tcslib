<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/InvarianceDistribution.lean :: BooleanAnalysis.GaussianSpace.Invariance.levyDistance_le_of_cdf_comparison -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# CDF comparison bounds Lévy distance

**Claim.** If $w,e\ge 0$ and each measure's CDF at $u$ is at most the other's CDF at $u+w$ plus $e$, then the Lévy distance from $\mu$ to $\nu$ is at most $w+e$.

**Proof.** Set $\epsilon=w+e$, which is nonnegative. For the first Lévy inequality at threshold $u$, use the assumed comparison in the reverse direction at $u-(w+e)$. Its shifted threshold is $u-e$, so it bounds $\nu(( -\infty,u-e])$ by $\mu(( -\infty,u-e+w])$ plus $e$. Since $e\ge0$, the latter CDF is at most the CDF of $\mu$ at $u$. Rearranging gives the required lower inequality, with slack $w+e$ on the left. For the second inequality, the forward comparison at $u$ bounds the CDF of $\mu$ by that of $\nu$ at $u+w$ plus $e$. Monotonicity of measures, since $u+w\le u+w+e$, bounds this in turn by the CDF of $\nu$ at $u+(w+e)$ plus $e$. Thus both defining inequalities hold at scale $w+e$, and the CDF-bound lemma (`levyDistance_le_of_cdf`) gives the result.

**Key facts.** `BooleanAnalysis.GaussianSpace.Invariance.levyDistance_le_of_cdf`.
