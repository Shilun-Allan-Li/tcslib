<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionCardTail.lean :: RestrictionFourier.bernoulliRestrProb_subset_freeVars -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Free-set marginal of a Bernoulli random restriction

**Claim.** Fix $n \in \mathbb{N}$, a real parameter $p$, and a subset $T \subseteq \{1,\dots,n\}$ of the coordinates. Draw a Bernoulli$(p)$ random restriction $\rho$ on $n$ variables — each coordinate is independently left free (unset) with weight $p$ and fixed to $0$ or to $1$ with weight $(1-p)/2$ each — and let $J$ denote its set of free variables. Then the total Bernoulli weight carried by those restrictions whose free set contains $T$ is exactly $p^{\lvert T\rvert}$; that is, $\Pr[\,T \subseteq J\,] = p^{\lvert T\rvert}$.

**Proof.** Recall the setup. A restriction $\rho$ on $n$ variables assigns to each coordinate $i$ a value $\rho_i \in \{0,1,\ast\}$, where $\ast$ (Lean's `none`) means "left free"; the free set is $J = \mathrm{freeVars}(\rho) = \{i : \rho_i = \ast\}$. The Bernoulli weight of $\rho$ is
\[
  w(\rho) \;=\; p^{\lvert J\rvert}\,\Bigl(\tfrac{1-p}{2}\Bigr)^{\,n-\lvert J\rvert},
\]
and $\Pr[T \subseteq J] = \sum_{\rho} w(\rho)\,\mathbf 1[\,T \subseteq \mathrm{freeVars}(\rho)\,]$, the sum ranging over all $3^n$ restrictions. The proof evaluates this sum by factorizing it coordinate by coordinate.

1. **Rewrite the event as a product of single-coordinate tests.** The condition $T \subseteq \mathrm{freeVars}(\rho)$ holds precisely when $\rho_i = \ast$ for every $i \in T$. Hence its indicator splits as a product over all coordinates,
\[
  \mathbf 1[\,T \subseteq \mathrm{freeVars}(\rho)\,]
  \;=\; \prod_{i=1}^{n} h_i(\rho_i),
  \qquad
  h_i(v) = \begin{cases} \mathbf 1[\,v = \ast\,], & i \in T,\\[2pt] 1, & i \notin T,\end{cases}
\]
since the whole product is $1$ exactly when each factor with $i \in T$ is $1$ and the factors with $i \notin T$ contribute nothing (indicator-as-product, `indicator_subset_eq_prod`).

2. **Factorize the weighted sum into independent coordinates.** The Bernoulli weight itself factorizes: writing $\nu(\ast) = p$ and $\nu(0) = \nu(1) = (1-p)/2$ for the per-coordinate weight (Lean's `varWeight`), one has $w(\rho) = \prod_i \nu(\rho_i)$, so $w$ is a product measure. Summing a product of per-coordinate functions against a product measure turns the sum over all restrictions into a product of one-dimensional sums (`sum_bernoulli_prod`):
\[
  \sum_{\rho} w(\rho)\prod_{i} h_i(\rho_i)
  \;=\; \prod_{i=1}^{n}\;\sum_{v \in \{0,1,\ast\}} \nu(v)\,h_i(v).
\]
This is the step that encodes the independence of the coordinates under the Bernoulli measure.

3. **Evaluate each one-dimensional sum.** Fix a coordinate $i$ and consider $S_i = \sum_{v} \nu(v)\,h_i(v)$, splitting on whether $i \in T$.
   - If $i \in T$, then $h_i(v) = \mathbf 1[v = \ast]$, so only the term $v = \ast$ survives and $S_i = \nu(\ast) = p$.
   - If $i \notin T$, then $h_i \equiv 1$, so $S_i$ is the total weight of a single coordinate, $\nu(\ast) + \nu(0) + \nu(1) = p + \tfrac{1-p}{2} + \tfrac{1-p}{2} = p + (1-p) = 1$.
   
   In both cases this is elementary arithmetic once the three values of $\nu$ are substituted. Thus $S_i = p$ when $i \in T$ and $S_i = 1$ otherwise.

4. **Collapse the product.** Substituting these values gives
\[
  \Pr[T \subseteq J] \;=\; \prod_{i=1}^{n}\bigl(\text{if } i \in T \text{ then } p \text{ else } 1\bigr).
\]
The factors with $i \notin T$ are all $1$ and drop out, leaving the product over $i \in T$ (`Finset.prod_ite_mem` together with $\mathrm{univ} \cap T = T$). Each surviving factor equals the constant $p$, so the product is $p^{\lvert T\rvert}$ (`Finset.prod_const`). This is the claimed value.

**Key facts.** `RestrictionFourier.indicator_subset_eq_prod`, `RestrictionFourier.sum_bernoulli_prod`.
