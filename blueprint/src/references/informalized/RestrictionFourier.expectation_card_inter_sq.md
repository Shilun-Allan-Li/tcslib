<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionCardTail.lean :: RestrictionFourier.expectation_card_inter_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Second moment of the free-coordinate count under a Bernoulli restriction

**Claim.** Fix $n\in\mathbb{N}$, a real parameter $p$, and a set of coordinates $U\subseteq\mathrm{Fin}\,n$. Each restriction $\rho$ on $n$ variables partitions the coordinates into fixed and free ones; write $J(\rho)$ for the set of free variables and weight $\rho$ by its Bernoulli weight $p^{|J(\rho)|}\bigl(\tfrac{1-p}{2}\bigr)^{\,n-|J(\rho)|}$. Then the weighted sum of $|U\cap J(\rho)|^2$ over all restrictions equals $p\,|U| + p^2\bigl(|U|^2-|U|\bigr)$.

**Proof.** Throughout, for a coordinate $i$ and a restriction $\rho$ write $\mathbf 1_i(\rho)$ for the indicator $[\rho_i=\text{none}]$, equal to $1$ when $i$ is free under $\rho$ and $0$ otherwise. The quantity being summed is, probabilistically, the second moment of $|U\cap J(\rho)|=\sum_{i\in U}\mathbf 1_i(\rho)$ under the Bernoulli-$p$ restriction measure, and the proof computes it by expanding the square and evaluating the resulting first and second moments of the indicators coordinate by coordinate.

1. **Expand the square as a double sum of indicators.** The size of $U\cap J(\rho)$ counts the coordinates of $U$ that are free under $\rho$, so
\[
|U\cap J(\rho)| \;=\; \sum_{i\in U}\mathbf 1_i(\rho)
\]
(this is `card_inter_eq_sum`). Squaring and distributing the product over the two sums gives, for each fixed $\rho$,
\[
w(\rho)\,|U\cap J(\rho)|^2 \;=\; \sum_{i\in U}\sum_{j\in U} w(\rho)\,\mathbf 1_i(\rho)\,\mathbf 1_j(\rho),
\]
where $w(\rho)$ denotes the Bernoulli weight. This is the step `hsq`; it is a purely algebraic rearrangement (write the square as a product of two copies of the sum and expand).

2. **Interchange the order of summation.** Summing the previous identity over all $\rho$ and moving the (finite) sum over restrictions inside the two sums over $U$ turns the left-hand side into
\[
\sum_{i\in U}\sum_{j\in U}\;\sum_{\rho} w(\rho)\,\mathbf 1_i(\rho)\,\mathbf 1_j(\rho).
\]
Finite sums commute freely, so this is justified without any hypothesis on $p$.

3. **Evaluate the inner sum over restrictions (the pairwise moment).** Fix $i,j\in U$. There are two cases.
   - If $i=j$, then $\mathbf 1_i(\rho)\,\mathbf 1_i(\rho)=\mathbf 1_i(\rho)$ because the indicator takes only the values $0$ and $1$, and the inner sum becomes the first moment of a single indicator:
   \[
   \sum_{\rho} w(\rho)\,\mathbf 1_i(\rho) \;=\; p .
   \]
   This is the fact that a fixed coordinate is free with total Bernoulli weight exactly $p$ (`expectation_free_indicator`).
   - If $i\neq j$, the inner sum is the joint moment of two distinct indicators, which evaluates to
   \[
   \sum_{\rho} w(\rho)\,\mathbf 1_i(\rho)\,\mathbf 1_j(\rho) \;=\; p^2 ,
   \]
   reflecting that distinct coordinates are freed independently (`expectation_free_indicator_pair`).

   In short, the inner sum equals $p$ on the diagonal $i=j$ and $p^2$ off it.

4. **Sum over the inner index $j$ (one row).** Fix $i\in U$. We must compute $\sum_{j\in U}\bigl(\,[i=j]\,p + [i\neq j]\,p^2\,\bigr)$. Writing each summand as
\[
[i=j]\,p + [i\neq j]\,p^2 \;=\; p^2 + \bigl([i=j]\,(p-p^2)\bigr)
\]
separates a constant term from a single-point correction. The constant $p^2$ summed over the $|U|$ elements of $U$ contributes $|U|\,p^2$; the correction term is nonzero only at $j=i$, and since $i\in U$ it contributes exactly $p-p^2$. Hence each row sums to
\[
\sum_{j\in U}\bigl(\,[i=j]\,p + [i\neq j]\,p^2\,\bigr) \;=\; |U|\,p^2 + (p - p^2) \;=\; p^2\bigl(|U|-1\bigr) + p .
\]
This is the step `hrow`.

5. **Sum over the outer index $i$ and simplify.** The row value $p^2(|U|-1)+p$ does not depend on $i$, so summing it over the $|U|$ elements of $U$ multiplies it by $|U|$:
\[
|U|\,\bigl(p^2(|U|-1)+p\bigr) \;=\; p^2\bigl(|U|^2-|U|\bigr) + p\,|U| .
\]
Rearranging gives exactly $p\,|U| + p^2\bigl(|U|^2-|U|\bigr)$, which is the claimed value. $\qquad\blacksquare$

**Key facts.** `RestrictionFourier.card_inter_eq_sum`, `RestrictionFourier.expectation_free_indicator`, `RestrictionFourier.expectation_free_indicator_pair`.
