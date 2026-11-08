<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Exponential.lean :: BooleanAnalysis.GaussianSpace.tendsto_eLpNorm_zero_of_dominated -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dominated convergence in $L^p$

**Claim.** Under the stated strong measurability, domination, and almost-everywhere convergence hypotheses, the $L^p$ norms of the functions tend to zero.

**Proof.** Because $p$ is positive and finite, its real exponent $p.toReal$ is positive. Raise the pointwise norms to this exponent. The assumed domination bounds these nonnegative functions by $\|b\|^{p.toReal}$, which is integrable because $b\in L^p$; almost-everywhere convergence of $F_k$ to zero makes the powered norms converge almost everywhere to zero. The dominated convergence theorem for nonnegative integrals therefore shows that their integrals tend to zero. The formula expressing the $L^p$ norm as the $1/p.toReal$ power of this integral, and continuity of that power at zero, yield the desired convergence.
