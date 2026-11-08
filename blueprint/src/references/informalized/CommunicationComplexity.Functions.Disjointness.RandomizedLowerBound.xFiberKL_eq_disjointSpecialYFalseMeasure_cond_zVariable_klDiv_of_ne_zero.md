<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/RectangleSwitching.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xFiberKL_eq_disjointSpecialYFalseMeasure_cond_zVariable_klDiv_of_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of Conditional Fiber Divergences

**Claim.** For an achievable record $z$ whose fiber has nonzero mass under the distribution conditioned on disjoint inputs and Bob’s special bit being false, the divergence from the uniform one-bit law of Alice’s special bit conditioned on $Z=z$ equals the divergence of Alice’s special-bit law under that conditioned distribution, further conditioned on $Z=z$.

**Proof.** The nonzero-mass hypothesis transfers to the uniform fiber law: the fiberwise mass of samples with Bob’s special bit false is nonzero (`zFiberMeasure_specialYFalse_ne_zero_of_disjointSpecialYFalseMeasure_ne_zero`). Apply the equality of the two conditional fiber divergences under precisely this nonvanishing condition (`xFiberKL_eq_disjointSpecialYFalseMeasure_cond_zVariable_klDiv`). By the definition of the fiberwise divergence, this gives the asserted equality of real-valued Kullback–Leibler divergences.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.zFiberMeasure_specialYFalse_ne_zero_of_disjointSpecialYFalseMeasure_ne_zero`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xFiberKL_eq_disjointSpecialYFalseMeasure_cond_zVariable_klDiv`.
