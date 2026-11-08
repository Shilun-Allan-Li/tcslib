<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetricConcavity.lean :: FABL.gaussianIsoperimetricReal_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Interior Positivity of the Gaussian Isoperimetric Function

**Claim.** For every $\alpha\in(0,1)$, the real-valued Gaussian isoperimetric function is positive at $\alpha$.

**Proof.** For interior $\alpha$, the real-valued function equals the standard Gaussian density evaluated at the upper quantile (\texttt{FABL.gaussianIsoperimetricReal\_apply\_of\_mem\_Ioo}). The standard Gaussian density is positive at every real argument, so the function is positive there.

**Key facts.** `FABL.gaussianIsoperimetricReal_apply_of_mem_Ioo`.
