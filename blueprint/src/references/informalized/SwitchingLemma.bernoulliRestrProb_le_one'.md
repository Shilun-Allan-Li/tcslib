<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/BernoulliRestriction.lean :: SwitchingLemma.bernoulliRestrProb_le_one' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Bernoulli Restriction Probability Is at Most One

**Claim.** Fix a number of variables $n$ and a real parameter $p$ with $0 \le p \le 1$. For any decidable predicate (event) on restrictions of $n$ variables, the probability that the event holds under a Bernoulli($p$) random restriction is at most $1$. Here that probability is the weighted sum $\sum_\rho w_p(\rho)\,\mathbf{1}[\text{event holds at }\rho]$ over all restrictions $\rho \colon \{0,\dots,n-1\} \to \{0,1,*\}$, where the weight $w_p(\rho) = p^{\,|\mathrm{free}(\rho)|}\bigl(\tfrac{1-p}{2}\bigr)^{\,n-|\mathrm{free}(\rho)|}$ and $\mathrm{free}(\rho)$ is the set of variables left unset by $\rho$.

**Proof.** The probability in question is, by definition,
\[
\mathrm{Prob}_p(\text{event}) \;=\; \sum_{\rho}\, w_p(\rho)\cdot \mathbf{1}[\text{event holds at }\rho],
\]
the sum ranging over all restrictions $\rho$ of the $n$ variables, where the indicator is $1$ when the event holds at $\rho$ and $0$ otherwise. The argument is a single term-by-term comparison followed by one known identity.

1. **Drop the indicator from each term.** In every summand the indicator satisfies $\mathbf{1}[\text{event holds at }\rho]\le 1$. Since the weight $w_p(\rho)$ is nonnegative whenever $0\le p\le 1$ — the weight is a product of nonnegative powers, as $p\ge 0$ and $\tfrac{1-p}{2}\ge 0$ follow from $p\le 1$ (*Bernoulli restriction weights are nonnegative*, `bernoulliRestrWeight_nonneg'`) — multiplying the inequality $\mathbf{1}[\cdots]\le 1$ by $w_p(\rho)$ preserves its direction. Hence
\[
w_p(\rho)\cdot \mathbf{1}[\text{event holds at }\rho]\;\le\; w_p(\rho)\cdot 1 \;=\; w_p(\rho)
\]
for every restriction $\rho$.

2. **Sum the comparison.** Adding these pointwise inequalities over all $\rho$ gives
\[
\mathrm{Prob}_p(\text{event})\;\le\;\sum_{\rho} w_p(\rho).
\]

3. **Use that the weights total $1$.** The Bernoulli restriction weights form a genuine probability distribution: they sum to one over all restrictions (*Bernoulli restriction weights sum to one*, `bernoulliRestrWeight_sum_one`), so $\sum_\rho w_p(\rho) = 1$. Combining this with the previous step yields $\mathrm{Prob}_p(\text{event})\le 1$, as claimed.

The whole point is that discarding the indicator can only increase a nonnegative-weighted sum, after which the weights' being a normalized distribution finishes the bound.

**Key facts.** `SwitchingLemma.bernoulliRestrWeight_nonneg'`, `SwitchingLemma.bernoulliRestrWeight_sum_one`.
