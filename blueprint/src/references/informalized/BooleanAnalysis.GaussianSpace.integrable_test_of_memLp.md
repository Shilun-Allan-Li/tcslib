<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Taylor.lean :: BooleanAnalysis.GaussianSpace.integrable_test_of_memLp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability of a smooth function of a random variable

**Claim.** If $Z$ belongs to $L^{m+1}$ on a probability space and $\psi$ is $(m+1)$-times continuously differentiable with bounded $(m+1)$st derivative, then $\psi\circ Z$ is integrable.

**Proof.** For each $j\le m+1$, the function $Z^j$ is integrable: apply the moment-product result `integrable_mul_pow_of_memLp` to the two copies of $Z$, with exponents $j$ and $0$. Thus the Taylor polynomial of $\psi$ at $0$, evaluated at $Z$, is integrable, since it is a finite sum of constant multiples of these powers. Taylor's theorem with bounded remainder (`abs_sub_taylor_le`) bounds the absolute difference between $\psi(Z)$ and this polynomial by $\frac{C}{(m+1)!}|Z|^{m+1}$. The latter is integrable by the assumed $L^{m+1}$ moment. Consequently $|\u001bpsi(Z)|$ is bounded by a sum of integrable functions. Continuity of $\psi$ makes its composition with $Z$ measurable up to almost-everywhere equality, so the domination criterion yields integrability.

**Key facts.** `BooleanAnalysis.Hypercontractivity.integrable_mul_pow_of_memLp`, `BooleanAnalysis.GaussianSpace.abs_sub_taylor_le`.
