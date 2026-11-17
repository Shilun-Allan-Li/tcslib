<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductFourierBases.lean :: FABL.inner_pmfSqrtScaleLinearEquiv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inner product under square-root probability scaling

**Claim.** For a finite set with a full-support probability mass function, the Euclidean inner product of the square-root-scaled images of $f$ and $g$ equals their probability-weighted inner product $\sum_x\pi(x)f(x)g(x)$.

**Proof.** The square-root probability scaling sends a function $f$ to the function whose value at $x$ is $\sqrt{(\pi x).\mathrm{toReal}}f(x)$ (`pmfSqrtScaleLinearEquiv_apply`). Expanding the Euclidean inner product as a finite sum, the contribution at $x$ is therefore $\sqrt{(\pi x).\mathrm{toReal}}g(x)\,\sqrt{(\pi x).\mathrm{toReal}}f(x)$. Rearranging the factors gives $(\sqrt{(\pi x).\mathrm{toReal}})^2f(x)g(x)$. Since $(\pi x).\mathrm{toReal}\ge0$, squaring its square root recovers $(\pi x).\mathrm{toReal}$. Summing these terms gives the defining probability-weighted inner product.

**Key facts.** `FABL.pmfSqrtScaleLinearEquiv_apply`.
