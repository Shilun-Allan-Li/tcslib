<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Fingerprint.lean :: Randomized.four_mul_le_four_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# An exponential inequality

**Claim.** For every natural number $M\ge12$, $4M(1+5M2^M)\le2^{2M}$.

**Proof.** First prove by induction for all $M\ge12$ that $21M^2\le2^M$. At the base $M=12$, this is a direct numerical inequality. For the successor step, the hypothesis $M\ge12$ gives $12M\le M^2$; expanding $(M+1)^2$ then shows $21(M+1)^2\le2\cdot21M^2$. The induction hypothesis bounds this by $2\cdot2^M=2^{M+1}$. Finally, rewrite $2^{2M}$ as $(2^M)^2$ and use $21M^2\le2^M$, together with $1\le2^M$, to obtain $4M(1+5M2^M)\le(2^M)^2$.
