<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.bernoulliMarginalContribution_eq_influence_div -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Marginal Contribution and Influence

**Claim.** For $p\in(0,1)$ and a monotone, zero-one-valued function on subsets, the Bernoulli marginal contribution at each coordinate equals the Bernoulli subset influence divided by $p(1-p)$.

**Proof.** The influence identity says that the subset influence is $p(1-p)$ times the marginal contribution (\texttt{bernoulliSubsetInfluence\_eq\_mul\_marginalContribution}). Since $0<p<1$, both $p$ and $1-p$ are nonzero, so their product is nonzero. Dividing the identity by this product yields the claimed formula.

**Key facts.** `FABL.bernoulliSubsetInfluence_eq_mul_marginalContribution`.
