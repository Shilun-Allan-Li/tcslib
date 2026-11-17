<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/FiniteNoiseOptimization.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.finite_noise_normalization -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Normalization of Weighted Forms

**Claim.** If $G(f)>0$ and $p\ne0$, then scaling $f$ by $c=G(f)^{-1/p}$ makes its moment equal to one and scales its quadratic form to $F(f)/G(f)^{2/p}$.

**Proof.** The homogeneity identities state that scaling a function by $c$ multiplies its moment by $|c|^p$ and its quadratic form by $c^2$. Since $G(f)>0$, the chosen real power $c=G(f)^{-1/p}$ is positive. The laws of real powers give $c^p=G(f)^{-1}$ and $c^2=G(f)^{-2/p}$. Hence the scaled moment is $G(f)^{-1}G(f)=1$, while the scaled quadratic form is $G(f)^{-2/p}F(f)=F(f)/G(f)^{2/p}$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.SharpDiscrete.finite_noise_homogeneity`.
