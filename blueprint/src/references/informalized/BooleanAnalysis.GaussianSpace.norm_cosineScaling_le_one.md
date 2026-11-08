<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/IndicatorRegularity.lean :: BooleanAnalysis.GaussianSpace.norm_cosineScaling_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cosine scaling norm bound

**Claim.** For every $n$ and real $u$, scalar multiplication by $\cos u$ on $\mathbb R^n$ has operator norm at most $1$.

**Proof.** It is enough to bound the norm of the image of each vector by the norm of that vector. Scalar multiplication gives image norm $|\cos u|$ times the vector norm. Since $|\cos u|\leq1$, this is at most the original norm, establishing the operator norm bound.
