<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Polynomial.lean :: BooleanAnalysis.GaussianSpace.exists_polynomial_eval_linear -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial representation of a linear map

**Claim.** Every continuous real-linear map from $\mathbb R^n$ to $\mathbb C$ is represented, on real inputs, by a complex polynomial in the coordinates.

**Proof.** For each coordinate $i$, let $e_i$ be the vector with value $1$ in coordinate $i$ and $0$ elsewhere. Every $x\in\mathbb R^n$ decomposes as $x=\sum_i x_i e_i$, so real-linearity gives $L(x)=\sum_i x_i L(e_i)$. Take the polynomial $P=\sum_i L(e_i)X_i$. Evaluating at the complex coordinates of $x$ gives $\sum_i L(e_i)x_i$, which equals $L(x)$ because multiplication by the real scalar $x_i$ agrees with real scalar multiplication in $\mathbb C$.
