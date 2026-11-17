<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/NoiseStability.lean :: BooleanAnalysis.ThresholdFunctions.kane_totalInfluence_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total Influence and Noise Sensitivity Bounds

**Claim.** There is a positive constant giving the stated total-influence estimate for every polynomial threshold function. Moreover, for each positive fixed degree bound, there are a nonnegative constant and a natural exponent giving the stated $\sqrt\delta$ times a logarithmic-power bound on noise sensitivity.

**Proof.** First take the constant and total-influence estimate supplied by `kane_totalInfluence_le`. Fix a positive degree bound $k$, and let $E$ be the exponent appearing in that estimate. This exponent is nonnegative, since its factors are nonnegative. Choose the logarithmic power to be $d=\lceil E\rceil$ and the prefactor to be $\sqrt2\,(2^k)^E(\log2)^{-d}$; it is nonnegative. For a class member and $0<\delta\le1/2$, the influence-to-noise estimate (`influence_bound_implies_noise_bound`) applies: the class is Boolean-valued, is closed under input negation and identification (`polynomialThresholdClass_closed`), and has the total-influence bound just obtained. It bounds sensitivity by the block-count influence estimate divided by the block count. Applying the block-count estimate (`kane_noise_aux`) with $E\le d$ gives the desired prefactor times $\sqrt\delta\,(\log(1/\delta))^d$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.kane_totalInfluence_le`, `BooleanAnalysis.ThresholdFunctions.polynomialThresholdClass_closed`, `BooleanAnalysis.ThresholdFunctions.influence_bound_implies_noise_bound`, `BooleanAnalysis.ThresholdFunctions.kane_noise_aux`.
