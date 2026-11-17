<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkFourier.lean :: ZkFourier.toOmega_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity of the character

**Claim.** For residues $a,b\in\mathbb{Z}/k\mathbb{Z}$, the value assigned to their sum is the product of their assigned values: $\chi(a+b)=\chi(a)\chi(b)$.

**Proof.** Let $r=a.val$ and $s=b.val$. The canonical representative of $a+b$ is the remainder of $r+s$ upon division by $k$. By the division algorithm, $r+s=(r+s)\bmod k+kq$ for some integer $q$. Thus $\omega_k^{r+s}=\omega_k^{(r+s)\bmod k}(\omega_k^k)^q$. The $k$-th power of the root is $1$ (`rootOfUnity_pow_k`), so the extra factor is $1$. Meanwhile, the laws of exponents give $\omega_k^r\omega_k^s=\omega_k^{r+s}$. Combining these identities yields the desired equality.

**Key facts.** `ZkFourier.rootOfUnity_pow_k`.
