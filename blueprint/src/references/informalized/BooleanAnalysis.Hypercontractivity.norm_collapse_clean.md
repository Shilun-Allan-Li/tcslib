<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/General/Kernel.lean :: BooleanAnalysis.Hypercontractivity.norm_collapse_clean -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Final-coordinate averaging preserves the power mean

**Claim.** Fix a natural number $n$, a real exponent $p \ge 1$, and a function $f : \{0,1\}^{n+1} \to \mathbb{R}$ on the $(n+1)$-dimensional Boolean cube. For $x' \in \{0,1\}^n$ write $(x',0)$ and $(x',1)$ for its two extensions by a final bit. Then the uniform expectation over $\{0,1\}^{n+1}$ of $|f|^p$ equals the uniform expectation over $\{0,1\}^n$ of the average of $|f|^p$ across the two final-bit extensions:
\[
  \mathbb{E}_{x' \in \{0,1\}^n}\!\left[\frac{|f(x',0)|^p + |f(x',1)|^p}{2}\right]
  \;=\; \mathbb{E}_{x \in \{0,1\}^{n+1}}\!\bigl[|f(x)|^p\bigr].
\]

**Proof.** All of the mathematical content of this statement lives in a companion lemma, *final-coordinate collapse for $p$-th powers* (`norm_collapse_rpow`), and the present proof does nothing more than restate that lemma in its intended cosmetic form. We first recall the companion fact and why it holds, then describe the two trivial adjustments that turn it into the statement above.

1. **The underlying fact.** The companion lemma (`norm_collapse_rpow`) asserts that for any exponent $p > 0$,
\[
  \mathbb{E}_{x \in \{0,1\}^{n+1}}\!\bigl[|f(x)|^p\bigr]
  \;=\; \mathbb{E}_{x' \in \{0,1\}^n}\!\left[\tfrac{1}{2}\bigl(|f(x',0)|^p + |f(x',1)|^p\bigr)\right].
\]
This is pure reindexing. Appending a final bit, $(x',b) \mapsto (x',b)$ (the operation $\mathrm{snoc}$), is a bijection between $\{0,1\}^n \times \{0,1\}$ and $\{0,1\}^{n+1}$; every point $x$ of the larger cube is $(x',0)$ or $(x',1)$ for exactly one pair $(x',b)$. Under this bijection the uniform weight on $\{0,1\}^{n+1}$, namely $2^{-(n+1)}$, factors as $2^{-n}\cdot\tfrac12$. Hence the uniform sum over $\{0,1\}^{n+1}$ splits as a uniform expectation over $x' \in \{0,1\}^n$ of the quantity $\tfrac12\bigl(|f(x',0)|^p + |f(x',1)|^p\bigr)$, which is exactly the claimed identity.

2. **Matching the exponent hypothesis.** The present lemma assumes $p \ge 1$, whereas the companion fact only requires $p > 0$. The extra strength is unused: one simply notes $p \ge 1 \Rightarrow p > 0$ and feeds that to the companion lemma. (In the formal text this is the one-line arithmetic deduction `linarith`.)

3. **Reconciling the two cosmetic differences.** The companion identity differs from the target in exactly two superficial ways, both resolved by inspection. First, the two sides are written in the opposite order, so we read the companion equation from right to left. Second, the inner quantity is written there as $\tfrac12\bigl(|f(x',0)|^p + |f(x',1)|^p\bigr)$ and here as $\tfrac{|f(x',0)|^p + |f(x',1)|^p}{2}$; these agree for every $x'$ by the elementary identity $\tfrac12(a+b) = \tfrac{a+b}{2}$. Since the two integrands coincide pointwise in $x'$, the two expectations coincide, and the target identity follows.

No further argument is needed: the result is the companion collapse lemma, transposed and with its averaging constant pulled inside the fraction.

**Key facts.** `BooleanAnalysis.Hypercontractivity.norm_collapse_rpow`.
