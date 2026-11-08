<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/FoolingF₂Polynomials/ViolaSeedLength.lean :: FABL.violaError_baseBias -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Error at the Base Bias

**Claim.** For $\varepsilon>0$ and $d\ge1$, if $b=(\varepsilon/9)^{2^{d-1}}$, then $9b^{1/2^{d-1}}=\varepsilon$.

**Proof.** The base $\varepsilon/9$ is positive, so the real-power law $(a^u)^v=a^{uv}$ applies. Substituting the definition of $b$ into the error expression combines the exponents to give $2^{d-1}\cdot(1/2^{d-1})=1$. Thus the expression becomes $9(\varepsilon/9)^1$, which simplifies to $\varepsilon$.
