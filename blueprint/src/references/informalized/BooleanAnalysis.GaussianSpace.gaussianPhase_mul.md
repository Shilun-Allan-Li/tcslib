<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Fourier.lean :: BooleanAnalysis.GaussianSpace.gaussianPhase_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Multiplication of Gaussian phases

**Claim.** For the phase $\Phi_c(u,v)=\exp\bigl(ic\sum_j u_jv_j\bigr)$, multiplying the phases with arguments $(a,t,x)$ and $(b,y,t)$ gives the phase with coefficient $1$ and first argument $ax+by$.

**Proof.** Expand the sums and use distributivity to obtain $a\sum_i t_i x_i+b\sum_i y_i t_i=\sum_i(a x_i+b y_i)t_i$. The product of the two exponentials is the exponential of the sum of their exponents; the displayed identity of sums makes that exponent exactly the one defining $\Phi_1(ax+by,t)$.
