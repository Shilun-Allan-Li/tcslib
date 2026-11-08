<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.pow_two_pow_eq_abs_pow_two_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even powers and absolute values

**Claim.** For every positive integer $k$ and every real number $a$, one has $a^{2^k}=|a|^{2^k}$.

**Proof.** Since $k>0$, write $k=r+1$ for some natural number $r$. Then $2^k=2\cdot 2^r$ is an even exponent. Every even power of a real number equals the same power of its absolute value, so $a^{2^k}=|a|^{2^k}$.
