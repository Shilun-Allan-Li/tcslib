<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Applications/LowDegree.lean :: BooleanAnalysis.Hypercontractivity.product_lowDegree_concentration -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-Degree Concentration Bound

**Claim.** Under the stated atom lower bound and positive degree parameter, the probability that |f| is at least t times its second norm is at most λᵏ exp(−kλt^(2/k)/(2e)) whenever t meets the stated threshold.

**Proof.** The threshold estimate supplies t>0 and ensures that q=λt^(2/k)/e is at least 2. Markov's inequality for the weighted finite probability space bounds the tail by (‖f‖q/(t‖f‖₂))^q. The coarse low-degree norm estimate bounds ‖f‖q by (√q λ^(1/q−1/2))ᵏ‖f‖₂; positivity of t and ‖f‖₂ permits cancellation and gives a tail bound of ((√q λ^(1/q−1/2))ᵏ/t)^q. Substituting the chosen q and simplifying the powers and exponential yields λᵏ exp(−kλt^(2/k)/(2e)).

**Key facts.** `BooleanAnalysis.Hypercontractivity.ConcentrationAux.scaled_concentration_parameter`, `BooleanAnalysis.Hypercontractivity.FiniteNorms.weighted_tail_le_norm_div_rpow`, `BooleanAnalysis.Hypercontractivity.product_lowDegree_norm_coarse`, `BooleanAnalysis.Hypercontractivity.ConcentrationAux.scaled_concentration_optimized_moment`.
