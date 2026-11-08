<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkFourier.lean :: ZkFourier.toOmega_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Multiplication of character arguments

**Claim.** For $j,a\in\mathbb{Z}/k\mathbb{Z}$, $\chi(ja)=(\omega_k^{j.val})^{a.val}$.

**Proof.** Write $r=j.val$ and $s=a.val$. The exponent on the left is the canonical representative of $ja$, namely the remainder of $rs$ modulo $k$. The laws of exponents rewrite the right side as $\omega_k^{rs}$. By division, $rs=(rs\bmod k)+kq$ for some nonnegative integer $q$, so $\omega_k^{rs}=\omega_k^{rs\bmod k}(\omega_k^k)^q$. Since $\omega_k^k=1$ (`rootOfUnity_pow_k`), this is exactly the left side.

**Key facts.** `ZkFourier.rootOfUnity_pow_k`.
