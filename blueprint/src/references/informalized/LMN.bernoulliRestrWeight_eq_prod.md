<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionCompose.lean :: LMN.bernoulliRestrWeight_eq_prod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Bernoulli restriction weight factors over coordinates

**Claim.** Let $p$ be a real parameter and let $\rho$ be a restriction on $n$ variables, each coordinate being either fixed to a Boolean value or left free. Write $k$ for the number of free coordinates. Then the Bernoulli weight of $\rho$, namely $p^{k}\bigl(\tfrac{1-p}{2}\bigr)^{\,n-k}$, equals the product $\prod_{i=1}^{n} w_p(\rho(i))$ of the per-coordinate weights, where $w_p(\rho(i))=p$ when coordinate $i$ is free and $w_p(\rho(i))=\tfrac{1-p}{2}$ when it is fixed.

**Proof.** The proof rewrites the product on the right until it matches the closed form on the left; the only real idea is to split the index set into the free and the fixed coordinates.

1. **Split the product along free versus fixed coordinates.** Let $F=\{\,i : \rho(i)\text{ is free}\,\}$ be the set of free coordinates, so that $|F|=k$. Since $F$ is a subset of the full index set $\{1,\dots,n\}$, the product over all coordinates factors as a product over $F$ times a product over its complement:
\[
  \prod_{i=1}^{n} w_p(\rho(i))
  \;=\;
  \Bigl(\prod_{i\in F} w_p(\rho(i))\Bigr)
  \cdot
  \Bigl(\prod_{i\notin F} w_p(\rho(i))\Bigr).
\]
This is the multiplicativity of a finite product over a set partitioned into a subset and its complement (`Finset.prod_sdiff`), used here with the complement taken inside the universe $\{1,\dots,n\}$.

2. **Evaluate each factor as a constant.** By the definition of $F$, a coordinate $i$ lies in $F$ exactly when $\rho(i)$ is free, in which case $w_p(\rho(i))=p$; and $i$ lies outside $F$ exactly when $\rho(i)$ is fixed, in which case $w_p(\rho(i))=\tfrac{1-p}{2}$. The fixed case is a routine check on the definition of $w_p$: a coordinate not marked free carries some Boolean value, and $w_p$ returns $\tfrac{1-p}{2}$ whichever value it is. Each of the two products is therefore a product of a single constant, so it collapses to a power:
\[
  \prod_{i\in F} w_p(\rho(i)) = p^{\,|F|},
  \qquad
  \prod_{i\notin F} w_p(\rho(i)) = \Bigl(\tfrac{1-p}{2}\Bigr)^{\,|F^{c}|}.
\]

3. **Count the fixed coordinates.** The complement $F^{c}=\{1,\dots,n\}\setminus F$ has cardinality $n-|F|$, since $F$ sits inside an $n$-element index set (`Finset.card_sdiff` together with the fact that the universe has $n$ elements). Hence the right-hand side equals
\[
  p^{\,k}\Bigl(\tfrac{1-p}{2}\Bigr)^{\,n-k},
\]
which is exactly the definition of the Bernoulli weight $\mathrm{bernoulliRestrWeight}(p,\rho)$.

4. **Reconcile the two forms.** Unfolding the Bernoulli weight makes both sides literally equal; the remaining work is purely algebraic normalization, matching the expression $\tfrac{1-p}{2}$ against the expanded form $\tfrac12-\tfrac{p}{2}$ and distributing the exponent over the quotient. No further mathematical content is involved. $\qquad\blacksquare$
