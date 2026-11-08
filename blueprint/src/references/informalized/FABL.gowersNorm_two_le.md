<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.gowersNorm_two_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity from the second Gowers norm

**Claim.** For every integer $k\ge 2$ and every $f\colon\mathbb F_2^n\to\mathbb R$, the order-two Gowers norm of $f$ is at most its order-$k$ Gowers norm.

**Proof.** Induct on $k$. The case $k=0$ is impossible under the hypothesis $2\le k$. At a successor $k+1$, if $k=1$, the desired inequality compares the order-two norm with itself and is equality. Otherwise $k\ge2$, so the induction hypothesis gives $\|f\|_{U^2}\le\|f\|_{U^k}$. The one-step monotonicity of Gowers norms gives $\|f\|_{U^k}\le\|f\|_{U^{k+1}}$; chaining these inequalities proves the result.

**Key facts.** `FABL.gowersNorm_mono`.
