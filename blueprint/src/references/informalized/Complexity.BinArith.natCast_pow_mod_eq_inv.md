<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/DetModMath.lean :: Complexity.BinArith.natCast_pow_mod_eq_inv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponent formula for modular inverses

**Claim.** For prime $p$ and $a$ nonzero modulo $p$, the residue of $a^{p-2}$ modulo $p$ is the multiplicative inverse of the residue of $a$.

**Proof.** In $\mathbb{Z}/p\mathbb{Z}$, reducing a natural number modulo $p$ does not change its residue, and casting a power gives the corresponding power of the cast. It remains to show that $a\cdot a^{p-2}=1$. Since $p$ is prime, $p\ge 2$, so $p-2+1=p-1$. Fermat's theorem for the finite field $\mathbb{Z}/p\mathbb{Z}$ gives $a^{p-1}=1$ when $a$ is nonzero. Thus $a\cdot a^{p-2}=1$, which characterizes $a^{-1}$.
