<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.sum_shapleyLayerWeight_add_card_compl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shapley Weights on Complementary Subsets

**Claim.** For $J\subseteq\{1,\ldots,n\}$ and $t\le |J|$, the sum of the layer weights $w(n,t+|U|)$ over subsets $U$ of the complement of $J$ equals $w(|J|,t)$.

**Proof.** Express each layer weight in the sum as the integral of its Bernoulli subset mass: $w(n,k)=\int_0^1 p^k(1-p)^{n-k}\,dp$, valid when $k\le n$ (`integral_bernoulliSubsetMass_eq_shapleyLayerWeight`). This condition holds for $k=t+|U|$ since $t\le |J|$ and $|U|\le |J^c|$. Interchange the finite sum and integral. For each $p$, factor out $p^t(1-p)^{|J|-t}$. The remaining sum over $U\subseteq J^c$ is $\sum_U p^{|U|}(1-p)^{|J^c|-|U|}=1$: it is the product expansion of $\prod_{j\in J^c}(p+(1-p))$. Thus the integral reduces to $\int_0^1p^t(1-p)^{|J|-t}\,dp$, which is $w(|J|,t)$ by the same integral identity.

**Key facts.** `FABL.integral_bernoulliSubsetMass_eq_shapleyLayerWeight`.
