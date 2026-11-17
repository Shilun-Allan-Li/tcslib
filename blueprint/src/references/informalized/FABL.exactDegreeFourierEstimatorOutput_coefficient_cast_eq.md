<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/LowDegree.lean :: FABL.exactDegreeFourierEstimatorOutput_coefficient_cast_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Fourier coefficient recovery

**Claim.** Under the degree and sample-accuracy hypotheses, each rounded rational coefficient output by the estimator, viewed as real, equals the corresponding true Fourier coefficient.

**Proof.** Fix a set $S$ in the low-degree family. The granularity theorem for sign-valued functions says that the true coefficient at $S$ is an integer multiple of $2(2^{-1})^k$. Thus write it as $z\,\gamma$, where $z\in\mathbb Z$ and $\gamma=2(2^{-1})^k$ is the degree-$k$ granularity. The assumption that the samples are outside the bad set says that the real empirical coefficient differs from the true coefficient by strictly less than the accuracy parameter, which is $\gamma/4$. Using the identity between rational and real empirical coefficients, and the real-cast formula for $\gamma$, this error is in particular less than $\gamma/2$. The rounding lemma therefore rounds the empirical coefficient to exactly $z\gamma$. Casting that rounded rational value to the reals gives $z\gamma$, which is the true coefficient. The granularity is positive, as required for these comparisons.

**Key facts.** `FABL.isFourierGranular_signValue_of_fourierDegree_le`, `FABL.empiricalFourierCoeff_cast`, `FABL.degreeFourierGranularity_cast`, `FABL.degreeFourierCoefficientAccuracy definition`, `FABL.degreeFourierGranularity_pos`, `FABL.roundToDegreeFourierGranularity_eq_of_close`.

**Caveat.** The accuracy parameter is unfolded directly in the proof rather than invoked through a listed upstream lemma.
