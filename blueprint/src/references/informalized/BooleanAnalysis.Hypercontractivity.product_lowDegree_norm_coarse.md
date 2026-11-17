<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Applications/LowDegree.lean :: BooleanAnalysis.Hypercontractivity.product_lowDegree_norm_coarse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coarse Low-Degree Norm Bound

**Claim.** If λ∈(0,1], q≥2, every coordinate atom has weight at least λ, and f has degree at most k, then ‖f‖q≤(√q λ^(1/q−1/2))ᵏ‖f‖₂.

**Proof.** First note that ‖f‖₂ is nonnegative. If q=2, the λ-power is 1 and √2≥1, so the claimed bound follows directly. If q>2, use the sharper low-degree norm estimate with √(q−1) in place of √q. Because q−1≤q, their square roots are ordered; multiplying by the nonnegative factor λ^(1/q−1/2), raising to the natural power k, and then multiplying by ‖f‖₂ preserves the inequality. This gives the stated coarser bound.

**Key facts.** `BooleanAnalysis.Hypercontractivity.product_lowDegree_norm`.
