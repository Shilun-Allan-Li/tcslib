<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/BernoulliCost.lean :: BernoulliCost.exp_neg_eventually_small -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Exponential Tails Eventually Fall Below Any Threshold

**Claim.** For every real $p > 0$ and every $\varepsilon > 0$ there is a natural number $N$ such that $\exp\!\left(-\tfrac{mp}{3}\right) < \varepsilon$ for all natural numbers $m \ge N$. In words: as the index $m$ grows, the exponential tail $\exp(-mp/3)$ is eventually smaller than any prescribed positive bound.

**Proof.** The Lean proof does not estimate $N$ explicitly. Instead it shows that the sequence $m \mapsto \exp(-mp/3)$ converges to $0$ as $m \to \infty$, and then reads off the required $N$ from what convergence to $0$ means. The convergence is built up by chaining together the limiting behaviour of each operation applied to $m$.

1. **The index tends to infinity.** As a natural number $m$ grows without bound, so does its real-number image: the cast $m \mapsto (m : \mathbb{R})$ tends to $+\infty$ along the "eventually larger" filter on $\mathbb{N}$ (`tendsto_natCast_atTop_atTop`).

2. **Scaling and dividing by positive constants preserve this.** Multiplying by the fixed positive constant $p$ keeps a quantity tending to $+\infty$ (since $p > 0$), so $mp \to +\infty$; dividing by the fixed positive constant $3$ likewise preserves the limit (the proof discharges $3 > 0$ by a routine positivity check), so $\tfrac{mp}{3} \to +\infty$.

3. **Negation flips the direction.** Negating a quantity that tends to $+\infty$ gives one tending to $-\infty$ (`Filter.tendsto_neg_atTop_atBot`), so $-\tfrac{mp}{3} \to -\infty$. A small rewriting step reconciles the two equivalent ways of placing the sign, $-\tfrac{mp}{3}$ versus $\tfrac{-mp}{3}$, so that this fact matches the expression in the statement.

4. **The exponential vanishes at $-\infty$.** Since $\exp(x) \to 0$ as $x \to -\infty$ (`Real.tendsto_exp_atBot`), composing with the previous step yields
\[
\exp\!\left(-\tfrac{mp}{3}\right) \longrightarrow 0 \qquad (m \to \infty).
\]

5. **Convergence to $0$ forces the tail below $\varepsilon$.** Because $\varepsilon > 0$, the open half-line $\{x : x < \varepsilon\}$ is a neighbourhood of $0$ (`gt_mem_nhds`). By definition of convergence, a sequence tending to $0$ eventually lands in every neighbourhood of $0$; hence $\exp(-mp/3)$ is eventually less than $\varepsilon$.

6. **Unpacking "eventually".** For the filter of large indices, "eventually $P(m)$" means precisely that there is some $N$ with $P(m)$ holding for all $m \ge N$ (`Filter.eventually_atTop`). Extracting this $N$ gives exactly the claimed statement: $\exp(-mp/3) < \varepsilon$ whenever $m \ge N$.
