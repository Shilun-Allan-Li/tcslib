<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.degree_le_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of degree bounds

**Claim.** If a function has degree at most $d$ in the multiplicative derivative sense, then it has degree at most $d+1$.

**Proof.** Fix a base point and $d+2$ directions. The recursive identity for the Gowers product expresses the $(d+2)$-fold product as the product of two $(d+1)$-fold products: one based at the original point and one based at the point shifted by the last direction. Each equals $1$ by the degree-at-most-$d$ hypothesis, applied to the first $d+1$ directions. Their product is therefore $1$, proving the next degree bound.
