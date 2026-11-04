<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/FourthMoment.lean :: BooleanAnalysis.Hypercontractivity.innerProduct_le_L43_L4 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Hölder's inequality for Boolean functions at exponents 4/3 and 4

**Claim.** Let $f,g:\{0,1\}^n\to\mathbb{R}$ be Boolean functions, with every expectation taken against the uniform probability measure on $\{0,1\}^n$. Then the $L^2$ inner product $\langle f,g\rangle=\mathbb{E}[fg]$ obeys the Hölder bound $\langle f,g\rangle\le\bigl(\mathbb{E}[\,|f|^{4/3}\,]\bigr)^{3/4}\bigl(\mathbb{E}[\,|g|^{4}\,]\bigr)^{1/4}$, i.e. $f$ is controlled in $L^{4/3}$ and $g$ in $L^{4}$, the conjugate exponent.

**Proof.** Throughout write $w=2^{-n}$ for the uniform weight, so that $\langle f,g\rangle=w\sum_{x}f(x)g(x)$ and, for any Boolean function $h$, $\mathbb{E}[h]=w\sum_{x}h(x)$, the sum ranging over all $x\in\{0,1\}^n$. The proof reduces the claim to the finite (unweighted) Hölder inequality and then redistributes the uniform weight $w$ so that the bare sums become genuine expectations. The exponents are $p=4/3$ and $q=4$, which are conjugate: $\tfrac1p+\tfrac1q=\tfrac34+\tfrac14=1$.

1. **Pass to absolute values.** For each point $x$ we have $f(x)g(x)\le|f(x)g(x)|=|f(x)|\,|g(x)|$. Summing over $x$ and multiplying by the nonnegative weight $w$ gives
\[
  \langle f,g\rangle=w\sum_{x}f(x)g(x)\;\le\;w\sum_{x}|f(x)|\,|g(x)|.
\]

2. **Finite Hölder inequality.** Since $p=4/3>1$ and $\tfrac1p+\tfrac1q=1$, the pair $(p,q)$ are conjugate exponents. Applying the discrete Hölder inequality for nonnegative sequences over the finite index set $\{0,1\}^n$ to the values $|f(x)|$ and $|g(x)|$ yields
\[
  \sum_{x}|f(x)|\,|g(x)|\;\le\;\Bigl(\sum_{x}|f(x)|^{p}\Bigr)^{1/p}\Bigl(\sum_{x}|g(x)|^{q}\Bigr)^{1/q}.
\]
Combined with Step 1 (the weight $w$ is nonnegative, so the inequality survives multiplication by it),
\[
  \langle f,g\rangle\;\le\;w\,\Bigl(\sum_{x}|f(x)|^{p}\Bigr)^{1/p}\Bigl(\sum_{x}|g(x)|^{q}\Bigr)^{1/q}.
\]

3. **Split the weight along the conjugate exponents.** Because $\tfrac1p+\tfrac1q=1$, the law of exponents gives
\[
  w=w^{1/p+1/q}=w^{1/p}\,w^{1/q}.
\]
Substituting and regrouping the two factors $w^{1/p},w^{1/q}$ with their companions,
\[
  \langle f,g\rangle\;\le\;\Bigl(w^{1/p}\bigl(\textstyle\sum_{x}|f(x)|^{p}\bigr)^{1/p}\Bigr)\Bigl(w^{1/q}\bigl(\textstyle\sum_{x}|g(x)|^{q}\bigr)^{1/q}\Bigr).
\]

4. **Absorb the weight into each power.** Since $w\ge0$ and each sum $\sum_x|f(x)|^{p}$, $\sum_x|g(x)|^{q}$ is nonnegative, the identity $(ab)^{s}=a^{s}b^{s}$ for nonnegative bases lets us pull $w^{1/p}$ and $w^{1/q}$ inside the respective powers:
\[
  \langle f,g\rangle\;\le\;\Bigl(w\sum_{x}|f(x)|^{p}\Bigr)^{1/p}\Bigl(w\sum_{x}|g(x)|^{q}\Bigr)^{1/q}
  =\bigl(\mathbb{E}[\,|f|^{p}\,]\bigr)^{1/p}\bigl(\mathbb{E}[\,|g|^{q}\,]\bigr)^{1/q}.
\]
This is the decisive point: the weight redistribution works exactly because $\tfrac1p+\tfrac1q=1$, and it is what turns the two unweighted sums of Step 2 into the uniform-measure expectations.

5. **Read off the exponents.** Finally $\tfrac1p=\tfrac34$ and $\tfrac1q=\tfrac14$, while $|g(x)|^{q}=|g(x)|^{4}$ (the real power at the natural number $4$ agrees with the ordinary fourth power — a routine identification). Hence
\[
  \langle f,g\rangle\;\le\;\bigl(\mathbb{E}[\,|f|^{4/3}\,]\bigr)^{3/4}\bigl(\mathbb{E}[\,|g|^{4}\,]\bigr)^{1/4},
\]
as claimed.
