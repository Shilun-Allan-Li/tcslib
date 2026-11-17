<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkBLR.lean :: ZkBLR.BLR_soundness_prime -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prime-field soundness bound

**Claim.** For prime $p$, a normalized function on $\mathbb Z_p^n$ that is $\varepsilon$-far from every linear function has BLR acceptance probability at most $1-\frac{p-1}{p}(1-\cos(2\pi/p))\varepsilon$.

**Proof.** Apply the general residue-ring soundness bound (`ZkBLR.BLR_soundness_general`) with modulus $p$. Since $p$ is prime, its totient is $p-1$; substituting this identity into the general bound gives the displayed prime-field estimate. Primality also ensures $p\ge2$, as required by the general result.

**Key facts.** `ZkBLR.BLR_soundness_general`.
