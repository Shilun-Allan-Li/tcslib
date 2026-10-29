<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionCompose.lean :: LMN.compose_fiber_weight_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Independent random restrictions compose multiplicatively

**Claim.** Work with restrictions of $n$ Boolean variables, where a restriction $\rho\colon\{0,\dots,n-1\}\to\{\ast,0,1\}$ either leaves a variable free ($\ast$) or fixes it to a bit. For a parameter $p$, the Bernoulli weight $w_p(\rho)=p^{\,f(\rho)}\bigl(\tfrac{1-p}{2}\bigr)^{\,n-f(\rho)}$, where $f(\rho)$ is the number of free variables, is the probability that the $p$-restriction model produces $\rho$: each variable is kept free with probability $p$, and otherwise set to $0$ or to $1$, each with probability $\tfrac{1-p}{2}$. The composite $\rho_1\!\triangleright\!\rho_2$ applies $\rho_1$ first and fills each still-free variable with $\rho_2$'s value there (coordinatewise, $(\rho_1\!\triangleright\!\rho_2)(i)=\rho_1(i)$ if $\rho_1(i)\neq\ast$, else $\rho_2(i)$). The claim is that drawing $\rho_1$ from the $p$-model and $\rho_2$ independently from the $q$-model and composing them reproduces exactly the $pq$-model: for every fixed restriction $\sigma$,
\[
\sum_{\rho_1}\sum_{\rho_2} w_p(\rho_1)\,w_q(\rho_2)\,[\,\rho_1\!\triangleright\!\rho_2=\sigma\,]\;=\;w_{pq}(\sigma),
\]
the sums ranging over all restrictions and $[\cdot]$ denoting the $0/1$ indicator.

**Proof.** The argument reduces the global identity to its one-variable instance by factoring every ingredient — weight and indicator alike — over the $n$ coordinates, swapping the order of summation and product, and then applying the single-variable fact to each coordinate.

Throughout write $v_p$ for the single-coordinate weight: $v_p(\ast)=p$ and $v_p(b)=\tfrac{1-p}{2}$ for a fixed bit $b$. The defining identity (`LMN.bernoulliRestrWeight_eq_prod`) is that the restriction weight factors as a product over coordinates,
\[
w_p(\rho)=\prod_{i=0}^{n-1} v_p\bigl(\rho(i)\bigr),
\]
which is just the observation that $p^{f(\rho)}(\tfrac{1-p}{2})^{n-f(\rho)}$ collects one factor $p$ per free coordinate and one factor $\tfrac{1-p}{2}$ per fixed coordinate.

1. **Factor each summand over coordinates.** Fix $\rho_1,\rho_2$. By the product formula above, $w_p(\rho_1)\,w_q(\rho_2)=\prod_i v_p(\rho_1(i))\prod_i v_q(\rho_2(i))=\prod_i\bigl(v_p(\rho_1(i))\,v_q(\rho_2(i))\bigr)$. The indicator also factors: two restrictions are equal exactly when they agree at every coordinate, so $[\,\rho_1\!\triangleright\!\rho_2=\sigma\,]=\prod_i[\,(\rho_1\!\triangleright\!\rho_2)(i)=\sigma(i)\,]$ — each coordinate indicator is $0$ or $1$, and the product is $1$ iff every coordinate matches. Recalling that $(\rho_1\!\triangleright\!\rho_2)(i)$ is $\rho_1(i)$ when free, else $\rho_2(i)$, the whole summand becomes
\[
\prod_{i} v_p(\rho_1(i))\,v_q(\rho_2(i))\,[\,(\rho_1\!\triangleright\!\rho_2)(i)=\sigma(i)\,].
\]

2. **Merge the two restrictions into one coordinatewise-paired object.** The double sum $\sum_{\rho_1}\sum_{\rho_2}$ is a sum over the pair $(\rho_1,\rho_2)$. Currying is a bijection between such pairs of functions and single functions $g\colon i\mapsto(\rho_1(i),\rho_2(i))$ valued in pairs of entries; re-indexing the sum along it turns the left-hand side into
\[
\sum_{g}\ \prod_{i} v_p(g(i)_1)\,v_q(g(i)_2)\,[\,g(i)_1\!\triangleright\! g(i)_2=\sigma(i)\,],
\]
where $g$ ranges over all functions assigning to each variable a pair of entries, and $x\!\triangleright\! y$ is the one-variable composite ($x$ if fixed, else $y$).

3. **Exchange product and sum.** The sum over functions $g$ of a product over coordinates is the fully expanded form of a product over coordinates of sums: by the distributive law (`Finset.prod_sum`, read from a product of sums to a sum over all choice functions), re-indexed by the same correspondence between a function $g$ and its tuple of coordinate values,
\[
\sum_{g}\ \prod_{i} T_i\bigl(g(i)\bigr)\;=\;\prod_{i}\ \sum_{x}\ T_i(x),
\]
where $T_i(x)=v_p(x_1)\,v_q(x_2)\,[\,x_1\!\triangleright\! x_2=\sigma(i)\,]$ and $x$ ranges over pairs of entries. The right-hand side is a product over the $n$ coordinates of independent one-variable sums.

4. **Apply the one-variable identity.** For each coordinate $i$, write the sum over pairs $x=(a,b)$ as a double sum over the two entries and invoke the single-variable composition law (`LMN.varWeight_compose_sum`):
\[
\sum_{a}\sum_{b} v_p(a)\,v_q(b)\,[\,a\!\triangleright\! b=\sigma(i)\,]\;=\;v_{pq}\bigl(\sigma(i)\bigr).
\]
This is the crux — the probabilistic statement for a single variable, that keeping it free through both stages has probability $p\cdot q$ while fixing it (at either stage) accounts for the remaining mass $\tfrac{1-pq}{2}$ per bit — and the whole lemma is its coordinatewise power.

5. **Reassemble.** Substituting step 4 into step 3,
\[
\sum_{\rho_1}\sum_{\rho_2} w_p(\rho_1)\,w_q(\rho_2)\,[\,\rho_1\!\triangleright\!\rho_2=\sigma\,]\;=\;\prod_{i} v_{pq}\bigl(\sigma(i)\bigr),
\]
and the product formula (`LMN.bernoulliRestrWeight_eq_prod`) with parameter $pq$ identifies the right-hand side as $w_{pq}(\sigma)$, which is the claim. $\qquad\blacksquare$

**Key facts.** `LMN.bernoulliRestrWeight_eq_prod`, `LMN.varWeight_compose_sum`.
