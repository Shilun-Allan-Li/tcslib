<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetricConcavity.lean :: FABL.gaussianIsoperimetricReal_apply_of_mem_Ioo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Interior Formula for the Gaussian Isoperimetric Function

**Claim.** For $\alpha\in(0,1)$, the real-valued Gaussian isoperimetric function equals the standard Gaussian density evaluated at the standard Gaussian upper quantile of $\alpha$.

**Proof.** On the open interval $(0,1)$, the real-valued function is defined by extending the interior function, which is continuous there. The extension agrees with that interior function at every point of the interval (\texttt{extendFrom\_extends}, applied using \texttt{FABL.continuousOn\_gaussianIsoperimetricInterior}). The interior function evaluates the Gaussian density at the real-valued upper quantile. For an interior $\alpha$, that real-valued quantile agrees with the upper quantile defined on $(0,1)$ (\texttt{FABL.standardGaussianUpperQuantileReal\_eq}), giving the stated formula.

**Key facts.** `FABL.continuousOn_gaussianIsoperimetricInterior`, `FABL.standardGaussianUpperQuantileReal_eq`.

**Caveat.** The supplied informal statement describes symmetry and a limiting degree-1 weight, but the formal declaration proves only this interior evaluation formula.
