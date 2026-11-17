<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkFourier.lean :: ZkFourier.norm_toOmega -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unit modulus of character values

**Claim.** For every residue $a\in\mathbb{Z}/k\mathbb{Z}$, the root of unity raised to its canonical representative has norm $1$.

**Proof.** Unfolding the definitions, the value is $\exp(2\pi i/k)^{a.val}$. Its norm is the norm of this exponential raised to the nonnegative integer power $a.val$. The norm of a complex exponential is the exponential of the real part of its exponent; here that real part is zero, so the norm of the base is $1$. Hence the norm of every such power is also $1$.
