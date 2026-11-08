<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetricConcavity.lean :: FABL.continuousOn_standardGaussianUpperQuantileReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuity of the Gaussian upper quantile

**Claim.** The standard Gaussian upper quantile, viewed as a real-valued function on $(0,1)$, is continuous on that interval.

**Proof.** Restrict the real-valued function to the open interval $(0,1)$. On this restricted domain, each input is represented by a point of the subtype $Ioo(0,1)$, and the defining real-valued function agrees there with the standard Gaussian upper quantile (`standardGaussianUpperQuantileReal_eq`). The latter is continuous on the subtype (`continuous_standardGaussianUpperQuantile`). Thus the restriction is continuous, which is precisely continuity on $(0,1)$.

**Key facts.** `FABL.continuous_standardGaussianUpperQuantile`, `FABL.standardGaussianUpperQuantileReal_eq`.
