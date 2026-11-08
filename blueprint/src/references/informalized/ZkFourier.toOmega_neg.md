<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkFourier.lean :: ZkFourier.toOmega_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conjugation under negation

**Claim.** For every residue $a\in\mathbb{Z}/k\mathbb{Z}$, the character value at $-a$ is the complex conjugate of the character value at $a$.

**Proof.** First consider the case $a.val=0$. Then $a=0$, so also $-a=0$; both character values are $1$. Otherwise, the canonical representative of $-a$ is $k-a.val$. Write $r=a.val$, so $0<r<k$. The character value at $-a$ is therefore $\exp(2\pi i(k-r)/k)$. Its exponent differs from $-2\pi i r/k$ by $2\pi i$, whose exponential is $1$, so this value equals $\exp(-2\pi i r/k)$. Complex conjugation sends $\exp(2\pi i r/k)$ to $\exp(-2\pi i r/k)$, proving the identity.
