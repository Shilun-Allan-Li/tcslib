<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Basis.lean :: BooleanAnalysis.GaussianSpace.inner_toLp_eq_integral_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inner Product of Gaussian $L^2$ Classes

**Claim.** For $L^2(\gamma_n)$ functions $f$ and $g$, the inner product of their $L^2$ classes is $\int f(x)g(x)\,d\gamma_n(x)$.

**Proof.** The $L^2$ inner product is defined by integrating the product of representatives of the two classes. Each class agrees almost everywhere with its original function, by the representative identities for the $L^2$ construction. Outside the union of the two exceptional null sets, their product therefore agrees with $f(x)g(x)$. Almost-everywhere equality preserves the integral, giving the stated formula.
