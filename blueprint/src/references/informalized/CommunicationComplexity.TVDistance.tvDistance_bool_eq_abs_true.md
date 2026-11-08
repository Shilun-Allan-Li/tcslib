<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/TVDistance.lean :: CommunicationComplexity.TVDistance.tvDistance_bool_eq_abs_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total Variation on the Two-Point Space

**Claim.** For probability measures μ and ν on Bool, their total variation distance equals the absolute difference between their masses at true.

**Proof.** First express total variation distance as one half the sum of the absolute singleton mass differences over the two points (`tvDistance_eq_half_sum`). The mass at false is one minus the mass at true for each probability measure (`measureReal_false_eq_one_sub_true`). Thus the false-point difference is the negative of the true-point difference, so the two absolute differences are equal. Their sum, multiplied by one half, is exactly the absolute difference at true.

**Key facts.** `CommunicationComplexity.TVDistance.tvDistance_eq_half_sum`, `CommunicationComplexity.TVDistance.measureReal_false_eq_one_sub_true`.
