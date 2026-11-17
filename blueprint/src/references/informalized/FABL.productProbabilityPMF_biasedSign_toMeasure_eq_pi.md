<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.productProbabilityPMF_biasedSign_toMeasure_eq_pi -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Measure of the biased-sign product

**Claim.** The measure associated with the $n$-fold product of the biased-sign law equals the product measure with that law as every coordinate marginal.

**Proof.** The product probability mass function is the independent product of $n$ copies of the biased-sign law. The measure associated with any finite independent product of probability mass functions is the product measure of their associated coordinate measures (\texttt{independentProductPMF\_toMeasure}). Applying this fact to the constant family of biased-sign laws gives the asserted equality.

**Key facts.** `FABL.independentProductPMF_toMeasure`.
