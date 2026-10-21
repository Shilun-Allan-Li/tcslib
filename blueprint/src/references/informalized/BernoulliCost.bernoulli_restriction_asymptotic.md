<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/BernoulliCost.lean :: BernoulliCost.bernoulli_restriction_asymptotic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Asymptotic Bernoulli Restriction Cost Bound

**Claim.** Fix a parameter $p$ with $0 < p \le 1$, positive integers $w, s > 0$, and a tolerance $\varepsilon > 0$. Then there is a threshold $N \in \mathbb{N}$ such that for every $n \ge N$ with $n > 0$ and every decidable event on restrictions of $n$ variables, the following implication holds: if the fixed-size restriction probability obeys $R_k[\mathrm{event}] \le \left(\tfrac{5kw}{n}\right)^{s}$ for all $k \le n$, then the probability of the event under a Bernoulli($p$) random restriction obeys $\Pr_p[\mathrm{event}] \le (10pw)^{s} + \varepsilon$.

**Proof.** The proof is a direct deduction from the finite-size cost bound: the only work is to choose the threshold $N$ large enough that an exponentially small error term, which the finite-size bound leaves behind, drops below the prescribed tolerance $\varepsilon$.

The key input is the **finite-size Bernoulli restriction cost bound** (`bernoulli_restriction_cost`): for a *fixed* $n > 0$, under the same hypotheses $0 < p \le 1$, $w, s > 0$, and the same fixed-size assumption $R_k[\mathrm{event}] \le \left(\tfrac{5kw}{n}\right)^{s}$ for all $k \le n$, one has the explicit estimate
\[
  \Pr_p[\mathrm{event}] \;\le\; (10pw)^{s} + \exp\!\left(-\tfrac{np}{3}\right).
\]
This already has the shape of the desired conclusion, except that the clean error term $\varepsilon$ is replaced by the concrete quantity $\exp(-np/3)$. Since $p > 0$, this term tends to $0$ as $n \to \infty$, so for all sufficiently large $n$ it falls below $\varepsilon$. Making this precise is the whole content of the asymptotic statement.

1. **Choose the threshold.** Because $p > 0$, the exponential decay fact (`exp_neg_eventually_small`) provides an $N \in \mathbb{N}$ such that for every $m \ge N$,
\[
  \exp\!\left(-\tfrac{mp}{3}\right) < \varepsilon.
\]
This $N$ depends only on $p$ and $\varepsilon$ (not on $w$, $s$, or the event), and it is the witness we return.

2. **Verify the conclusion for each admissible $n$.** Take any $n \ge N$ with $n > 0$, any decidable event on restrictions of $n$ variables, and suppose the fixed-size hypothesis $R_k[\mathrm{event}] \le \left(\tfrac{5kw}{n}\right)^{s}$ holds for all $k \le n$. Since $n > 0$, the finite-size cost bound applies and gives
\[
  \Pr_p[\mathrm{event}] \;\le\; (10pw)^{s} + \exp\!\left(-\tfrac{np}{3}\right).
\]

3. **Absorb the error term.** As $n \ge N$, step 1 (applied with $m = n$) yields $\exp(-np/3) < \varepsilon$, hence $\exp(-np/3) \le \varepsilon$. Adding $(10pw)^{s}$ to both sides and chaining with the inequality of step 2 gives
\[
  \Pr_p[\mathrm{event}] \;\le\; (10pw)^{s} + \exp\!\left(-\tfrac{np}{3}\right) \;\le\; (10pw)^{s} + \varepsilon,
\]
which is exactly the claimed bound. This completes the proof.

**Key facts.** `BernoulliCost.exp_neg_eventually_small`, `BernoulliCost.bernoulli_restriction_cost`.
