<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/VectorFourier.lean :: FABL.IsVectorFourierGranular.refine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Refining Fourier Granularity

**Claim.** If every Fourier coefficient of the function on the sign cube corresponding to $f$ is an integer multiple of $\delta$, and $\delta=q\varepsilon$ for an integer $q$, then every such coefficient is an integer multiple of $\varepsilon$.

**Proof.** By the characterization of vector Fourier granularity, it suffices to fix a frequency $\gamma$ and exhibit an integer multiple of $\varepsilon$ for its coefficient. The hypothesis provides an integer $z$ such that the coefficient is $z\delta$. Substituting $\delta=q\varepsilon$ gives $z(q\varepsilon)=(zq)\varepsilon$, and $zq$ is an integer. This proves the required granularity at every frequency.

**Key facts.** `FABL.isVectorFourierGranular_iff`.
