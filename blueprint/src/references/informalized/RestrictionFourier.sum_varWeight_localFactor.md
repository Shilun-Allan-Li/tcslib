<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionFourier.lean :: RestrictionFourier.sum_varWeight_localFactor -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Averaging a single local factor against the Bernoulli weight

**Claim.** Fix a real parameter $p$, two coordinate sets $U, S \subseteq [n]$, and a coordinate $i \in [n]$. Let $w_p$ be the per-variable Bernoulli weight, which assigns $w_p(\text{free}) = p$ to the free value and $w_p(v) = (1-p)/2$ to each of the two fixed Boolean values, and let $\ell_{U,S,i}$ be the per-coordinate local factor at $i$. Then the weighted sum over the three possible per-coordinate values $v$ (free, or fixed to either Boolean) equals $p$ when $i \in S$, equals $0$ when $i \in U \setminus S$, and equals $1$ otherwise.

**Proof.** The variable ranges over the three-element type of per-coordinate values: the free value, written $\mathrm{none}$, and the two fixed values $\mathrm{some}\,\mathsf{false}$ and $\mathrm{some}\,\mathsf{true}$. Expanding the weighted sum over these three cases and inserting the definition of $w_p$ gives, in every case,
\[
  \sum_{v} w_p(v)\,\ell_{U,S,i}(v)
  \;=\;
  p\cdot \ell_{U,S,i}(\mathrm{none})
  \;+\; \tfrac{1-p}{2}\,\ell_{U,S,i}(\mathrm{some}\,\mathsf{false})
  \;+\; \tfrac{1-p}{2}\,\ell_{U,S,i}(\mathrm{some}\,\mathsf{true}).
\]
The proof splits on whether $i \in S$ and whether $i \in U$ and evaluates the local factor in each resulting case; the three distinct outcomes correspond exactly to the three branches of $\ell_{U,S,i}$'s definition. Recall that the sign attached to a fixed Boolean is $+1$ for $\mathsf{false}$ and $-1$ for $\mathsf{true}$.

1. **$i \in S$.** Here the local factor is $1$ on the free value and $0$ on both fixed values, so only the first term survives and the sum is $p\cdot 1 = p$. (Membership of $i$ in $U$ plays no role, which is why the two Lean cases with $i \in S$ collapse to the same computation.)

2. **$i \in U$ but $i \notin S$.** Now the local factor is $0$ on the free value and equals the Boolean sign on the fixed values: $+1$ on $\mathsf{false}$ and $-1$ on $\mathsf{true}$. The free term vanishes and the two fixed terms are equal and opposite,
\[
  \tfrac{1-p}{2}\cdot(+1) + \tfrac{1-p}{2}\cdot(-1) = 0,
\]
so the sum is $0$.

3. **$i \notin S$ and $i \notin U$.** Here the local factor is identically $1$, so the sum collects the full weight,
\[
  p + \tfrac{1-p}{2} + \tfrac{1-p}{2} = p + (1-p) = 1.
\]

Each of these three identities is an elementary rational computation closed by `ring`, and together they match the three branches of the claimed value. $\qquad\blacksquare$
