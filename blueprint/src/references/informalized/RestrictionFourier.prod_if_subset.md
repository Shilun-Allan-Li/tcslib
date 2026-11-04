<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionFourier.lean :: RestrictionFourier.prod_if_subset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# A three-valued weight product over coordinates

**Claim.** Fix a real number $p$ and two subsets $S, U \subseteq \{1,\dots,n\}$. Assign to each coordinate $i$ the weight $p$ when $i \in S$, the weight $1-p$ when $i \in U \setminus S$, and the weight $1$ otherwise. Then the product of these weights over all $n$ coordinates equals $p^{|S|}\,(1-p)^{|U \setminus S|}$, where $|\cdot|$ denotes cardinality.

**Proof.** The weight attached to coordinate $i$ is the nested conditional
\[
  w(i) \;=\; \begin{cases} p & i \in S,\\ 1-p & i \notin S \ \text{and}\ i \in U,\\ 1 & \text{otherwise.}\end{cases}
\]
The argument splits the full product over $\{1,\dots,n\}$ into its part on $S$ and its part on the complement $\{1,\dots,n\}\setminus S$, evaluates each factor, and multiplies.

1. **Split off $S$.** Since $S$ is a subset of the whole index set, the product over all coordinates factors as the product over $\{1,\dots,n\}\setminus S$ times the product over $S$ (`Finset.prod_sdiff`). It therefore suffices to compute these two factors separately.

2. **The factor over $S$.** For every $i \in S$ the first branch of the conditional fires, so $w(i) = p$ there. The product of the constant $p$ over $S$ is thus $p^{|S|}$.

3. **The factor over the complement.** For $i \notin S$ the test $i \in S$ fails, so on $\{1,\dots,n\}\setminus S$ the weight collapses to the two-valued form $w(i) = 1-p$ if $i \in U$ and $w(i) = 1$ otherwise. A product of such indicator factors — a value on the members of $U$ and $1$ on the rest — keeps only the terms where the test holds (`Finset.prod_ite_mem`); that is, it equals the product of $1-p$ over $\big(\{1,\dots,n\}\setminus S\big)\cap U$. This intersection is exactly $U \setminus S$, since an element lies in it iff it belongs to $U$ but not to $S$. Hence the factor is the constant $1-p$ raised to the power $|U \setminus S|$, namely $(1-p)^{|U \setminus S|}$.

4. **Combine.** Multiplying the two factors gives $p^{|S|}\,(1-p)^{|U \setminus S|}$, as claimed (the two pieces are produced in the opposite order and simply commuted into place).
