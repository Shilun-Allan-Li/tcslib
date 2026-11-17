<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Applications.lean :: BooleanAnalysis.Hypercontractivity.product_kkl_isoperimetric -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product KKL Isoperimetry

**Claim.** For a Boolean function of positive variance on a finite product space whose coordinate atoms have weight at least λ, some coordinate has influence at least (I/V)⁻²(9/λ)⁻ᴵⱽ, where V is the variance and I is the total influence.

**Proof.** Set ρ = √λ/3, which is positive. First, each coordinate influence is nonnegative, since it is an expectation of a square against nonnegative product masses. Also V ≤ I: the variance-to-noisy-total bound at noise parameter 1 reduces, using the identity expressing total influence as the sum of component energies weighted by their set sizes, to this inequality. Thus I is positive. Next, sum the coordinate stability bounds over coordinates. Interchanging the finite sums over coordinates and subsets shows that this sum is exactly the weighted component-energy sum with coefficient |S|ρ^|S|; the stability estimate bounds it above by the sum of the coordinate influences raised to the 3/2 power. The variance-to-noisy-total bound at ρ therefore gives Vρᴵⱽ ≤ ∑ᵢ Iᵢ^{3/2}. Apply the finite-sum principle that if nonnegative numbers have positive sum I and their 3/2-power sum is at least A, then one of them is at least (A/I)². With A = Vρᴵⱽ, this yields a coordinate influence at least (Vρᴵⱽ/I)². Finally, the coefficient identity rewrites this expression as (I/V)⁻²(9/λ)⁻ᴵⱽ, as claimed.

**Key facts.** `BooleanAnalysis.Hypercontractivity.ComparisonAux.variance_rpow_ratio_le_noisy_total`, `BooleanAnalysis.Hypercontractivity.RandomizationAux.totalInfluence_eq_sum_card_components`, `BooleanAnalysis.Hypercontractivity.product_stableInfluence_four`, `BooleanAnalysis.Hypercontractivity.FiniteNorms.exists_sq_div_sum_le_of_sum_three_halves`, `BooleanAnalysis.Hypercontractivity.ComparisonAux.kkl_coefficient_eq`.
