<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkBLR.lean :: ZkBLR.parseval_lift_omega -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parseval for a root-of-unity lift

**Claim.** For a function from $(\mathbb Z/p\mathbb Z)^n$ to $\mathbb Z/p\mathbb Z$, the sum of the squared moduli of the Fourier coefficients of its root-of-unity lift is $1$.

**Proof.** Parseval's identity identifies the sum of squared Fourier-coefficient moduli with the squared $L^2$ norm of the lift (\texttt{ZkFourier.parseval\_identity}). At every input, the lift is a root of unity, so its modulus is $1$ (\texttt{ZkFourier.norm\_toOmega}); consequently its squared modulus is also $1$. The normalized average of this constant squared modulus is $1$: the domain has $p^n$ elements (\texttt{ZkFourier.card\_ZkVec}), equal to the normalization denominator. Thus Parseval gives the claimed sum.

**Key facts.** `ZkFourier.parseval_identity`, `ZkFourier.norm_toOmega`, `ZkFourier.card_ZkVec`.
