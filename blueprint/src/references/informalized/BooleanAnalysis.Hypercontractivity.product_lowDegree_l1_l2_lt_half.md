<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Applications/LowDegree.lean :: BooleanAnalysis.Hypercontractivity.product_lowDegree_l1_l2_lt_half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict-Parameter L1–L2 Comparison

**Claim.** For λ strictly between 0 and 1/2, a degree-at-most-k function on the finite product space satisfies ‖f‖₂ ≤ C(λ)ᵏ‖f‖₁, where C(λ) is the product norm comparison constant.

**Proof.** Let q>2 approach 2 from above, and put r equal to the sharp discrete noise radius at q and λ. This radius lies strictly between 0 and 1. The noise operators at r and r⁻¹ are inverses, so f can be written as noise at r applied to noise at r⁻¹ applied to f. Sharp hypercontractivity bounds the q-norm of f by the 2-norm of the latter function. Since f has degree at most k, noise at r⁻¹ increases its 2-norm by at most (r⁻¹)ᵏ; the radius bound r<1 ensures r⁻¹≥1, as required for this estimate. Together these give ‖f‖q ≤ exp(−k log r)‖f‖₂. The norm interpolation inequality then yields ‖f‖₂ ≤ exp(−k log(r)q/(q−2))‖f‖₁. Rewrite this factor as the kth power of exp(−log(r)q/(q−2)). As q tends down to 2, the sharp-radius comparison limit identifies the base's limit as C(λ), and passage to the limit gives the desired inequality.

**Key facts.** `BooleanAnalysis.Hypercontractivity.ComparisonAux.sharp_radius_comparison_limit`, `BooleanAnalysis.Hypercontractivity.SharpDiscrete.radius_pos_lt_one`, `BooleanAnalysis.Hypercontractivity.product_noise_inverse`, `BooleanAnalysis.Hypercontractivity.product_hypercontractivity_sharp`, `BooleanAnalysis.Hypercontractivity.product_lowDegree_noise_norm_two`, `BooleanAnalysis.Hypercontractivity.ComparisonAux.norm_interpolation_bound`.
