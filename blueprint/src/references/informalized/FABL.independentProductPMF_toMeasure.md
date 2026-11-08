<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/CorrelatedGaussianLimit.lean :: FABL.independentProductPMF_toMeasure -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Measure of an independent product distribution

**Claim.** The measure associated with an independent product distribution equals the product measure of the associated coordinate measures.

**Proof.** It suffices to compare the two measures on singleton sets, since finite spaces with measurable singletons have measures determined by their singleton values. At a tuple $x$, the measure associated with the independent product assigns the singleton its point probability, which by the independent-product point-probability formula (\texttt{FABL.independentProductPMF_apply}) is $\prod_i p_i(x_i)$. The product measure of the coordinate measures assigns that singleton the product of the coordinate singleton measures. Each coordinate singleton measure equals $p_i(x_i)$, so the two values agree for every tuple. Hence the measures are equal.

**Key facts.** `FABL.independentProductPMF_apply`.
