<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.shapleySubsetPMF_apply_toReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real Probability of a Subset

**Claim.** The probability of selecting $S$ under the Shapley subset distribution, viewed as a real number, is $1/((n+1)\binom{n}{|S|})$.

**Proof.** Use the formula for the mass of $S$ in the extended nonnegative reals (`shapleySubsetPMF_apply`). Converting the product of inverse natural-number casts to a real probability converts each factor to the corresponding real inverse; the natural-number casts become their real values. The product of the two inverses is the reciprocal of the product, yielding $1/((n+1)\binom{n}{|S|})$.

**Key facts.** `FABL.shapleySubsetPMF_apply`.
