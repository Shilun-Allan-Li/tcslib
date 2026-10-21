<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Decomposition.lean :: BooleanAnalysis.Hypercontractivity.expect_cs_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Cauchy–Schwarz for the uniform expectation of Boolean functions

**Claim.** Let $g, h : \{0,1\}^n \to \mathbb{R}$ be functions on the Boolean hypercube, and let $\mathbb{E}[\,\cdot\,]$ denote the expectation under the uniform measure. Then the expectation of the product $g^2 h^2$ is controlled by the fourth moments of $g$ and $h$ via $\bigl(\mathbb{E}[g^2 h^2]\bigr)^2 \le \mathbb{E}[g^4]\cdot\mathbb{E}[h^4]$. This is nothing but the Cauchy–Schwarz inequality applied to the functions $g^2$ and $h^2$, transported from raw sums to the normalized uniform expectation.

**Proof.** Throughout, write $w = (1/2)^n = 2^{-n}$ for the uniform weight, so that the expectation is $\mathbb{E}[f] = w \sum_{x \in \{0,1\}^n} f(x)$. Unfolding this definition, the claim $\bigl(\mathbb{E}[g^2h^2]\bigr)^2 \le \mathbb{E}[g^4]\,\mathbb{E}[h^4]$ becomes
\[
  w^2\Bigl(\sum_x g(x)^2 h(x)^2\Bigr)^2 \;\le\; w^2\Bigl(\sum_x g(x)^4\Bigr)\Bigl(\sum_x h(x)^4\Bigr),
\]
since the left side squares the single factor $w$ while the right side multiplies two of them. The proof separates the common weight $w^2 \ge 0$ from a purely combinatorial inequality on the bare sums.

1. **The sum-level inequality.** We first show
\[
  \Bigl(\sum_x g(x)^2 h(x)^2\Bigr)^2 \;\le\; \Bigl(\sum_x g(x)^4\Bigr)\Bigl(\sum_x h(x)^4\Bigr).
\]
This is the discrete Cauchy–Schwarz inequality — the finite-sum statement that for any real-valued $u, v$ on the index set, $\bigl(\sum_x u(x) v(x)\bigr)^2 \le \bigl(\sum_x u(x)^2\bigr)\bigl(\sum_x v(x)^2\bigr)$ (`Finset.sum_mul_sq_le_sq_mul_sq`). Apply it with $u(x) = g(x)^2$ and $v(x) = h(x)^2$. The left-hand side is then $\bigl(\sum_x g(x)^2 h(x)^2\bigr)^2$ exactly, and the right-hand side is $\bigl(\sum_x (g(x)^2)^2\bigr)\bigl(\sum_x (h(x)^2)^2\bigr)$, which equals $\bigl(\sum_x g(x)^4\bigr)\bigl(\sum_x h(x)^4\bigr)$ after the elementary identity $(t^2)^2 = t^4$ rewrites each summand. This matching of exponents is the only bookkeeping involved.

2. **Scaling by the weight.** It remains to multiply the inequality of Step 1 through by the nonnegative constant $w^2$. Since $w = 2^{-n} > 0$ we have $w^2 \ge 0$, and multiplying both sides of a valid inequality $A \le B$ by a nonnegative number preserves it: $w^2 A \le w^2 B$. Taking $A = \bigl(\sum_x g^2 h^2\bigr)^2$ and $B = \bigl(\sum_x g^4\bigr)\bigl(\sum_x h^4\bigr)$ yields precisely the displayed form of the goal above, which is the asserted inequality for the expectations. This completes the proof.

**Key facts.** `Finset.sum_mul_sq_le_sq_mul_sq`.
