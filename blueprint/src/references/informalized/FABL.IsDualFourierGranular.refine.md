<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/SparseSpectrum.lean :: FABL.IsDualFourierGranular.refine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Changing Fourier Granularity

**Claim.** If every dual Fourier coefficient of $f$ is an integer multiple of $\delta$, and $\delta=q\varepsilon$ for an integer $q$, then every such coefficient is an integer multiple of $\varepsilon$.

**Proof.** Fix a dual frequency. By the assumed $\delta$-granularity, its coefficient is $z\delta$ for some integer $z$. Substituting $\delta=q\varepsilon$ gives $(zq)\varepsilon$. Since the product of integers is an integer, this coefficient is an integer multiple of $\varepsilon$.
