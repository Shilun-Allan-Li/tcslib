<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Applications/LowDegree.lean :: BooleanAnalysis.Hypercontractivity.product_lowDegree_norm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sharp Low-Degree Norm Bound

**Claim.** If the coordinate atoms have weight at least λ, then for q>2 a function of degree at most k satisfies ‖f‖q ≤ (√(q−1) λ^(1/q−1/2))ᵏ‖f‖₂.

**Proof.** Define C=√(q−1)λ^(1/q−1/2). Since q>2, √(q−1)≥1. Also λ≤1 and 1/q−1/2<0, so the second factor is at least 1; hence C≥1. Its reciprocal simplifies to (1/√(q−1))λ^(1/2−1/q), the admissible noise radius in the hypercontractive estimate. Apply noise at C to noise at C⁻¹: the operators are inverse, so this composition recovers f. Hypercontractivity bounds the q-norm after the outer noise by the 2-norm before it, giving ‖f‖q≤‖T_C f‖₂. The low-degree noise estimate bounds the latter by Cᵏ‖f‖₂, proving the claim.

**Key facts.** `BooleanAnalysis.Hypercontractivity.product_noise_inverse`, `BooleanAnalysis.Hypercontractivity.product_hypercontractivity`, `BooleanAnalysis.Hypercontractivity.product_lowDegree_noise_norm_two`.
