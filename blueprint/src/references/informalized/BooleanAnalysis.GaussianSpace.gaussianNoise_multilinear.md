<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise.lean :: BooleanAnalysis.GaussianSpace.gaussianNoise_multilinear -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian noise on multilinear polynomials

**Claim.** For a multilinear polynomial $P_F$ and $rho\in[-1,1]$, Gaussian noise satisfies $T_\rho P_F(x)=P_F(\rho x)$.

**Proof.** Expand $P_F$ as the finite sum over subsets $S$ of its coefficient $F(S)$ times the corresponding coordinate monomial. For each $S$, the function of the Gaussian input is integrable by the integrability of affine Gaussian monomials (\texttt{integrable\_gaussian\_affine\_monomial}). Thus integration distributes over the finite sum. The integral of each affine Gaussian monomial is the product of its deterministic coordinate shifts (\texttt{integral\_gaussian\_affine\_monomial}); here those shifts are $\rho x_i$. Multiplying by $F(S)$ and summing recovers exactly $P_F(\rho x)$.

**Key facts.** `BooleanAnalysis.GaussianSpace.integrable_gaussian_affine_monomial`, `BooleanAnalysis.GaussianSpace.integral_gaussian_affine_monomial`.
