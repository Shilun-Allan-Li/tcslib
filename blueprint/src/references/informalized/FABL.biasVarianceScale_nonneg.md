<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.biasVarianceScale_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of the Bias Variance Scale

**Claim.** For every $p\in[0,1]$, the bias variance scale $4p(1-p)$ is nonnegative.

**Proof.** The factors $4$ and $p$ are nonnegative, and $p\le 1$ implies $1-p\ge 0$. Their product $4p(1-p)$ is therefore nonnegative.
