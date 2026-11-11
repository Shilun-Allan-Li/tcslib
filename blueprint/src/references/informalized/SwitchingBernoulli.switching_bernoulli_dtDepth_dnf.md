<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/SwitchingBernoulli.lean :: SwitchingBernoulli.switching_bernoulli_dtDepth_dnf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Switching bound for DNFs

**Claim.** For a DNF of width at most $w$ satisfying the stated distinct-variable and no-duplicate-literal conditions, the Bernoulli restriction probability that the restricted function has decision-tree depth greater than $t$ is at most $2^{-t}+\exp(-np/3)$.

**Proof.** When $t=0$, the probability is at most $1$, which is no greater than the claimed right-hand side. For positive $t$, apply the Bernoulli restriction cost bound to the event that the restricted decision-tree depth exceeds $t$, using parameter $2w$. Its fixed-size hypothesis is supplied by the rescaled fixed-size switching bound: for every number $k$ of free variables, the event has probability at most $(5k(2w)/n)^t$. The cost bound therefore gives $(10pw)^t+\exp(-np/3)$. Finally, $p\le 1/(40w)$ implies $10pw\le 1/4\le 1/2$, so $(10pw)^t\le (1/2)^t$, as required.

**Key facts.** `SwitchingLemma.bernoulliRestrProb_le_one'`, `SwitchingBernoulli.switching_fixedSize_bound_rescaled`, `BernoulliCost.bernoulli_restriction_cost`.
