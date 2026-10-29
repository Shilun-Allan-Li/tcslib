<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/OneBit.lean :: BooleanAnalysis.Hypercontractivity.one_bit_val_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Reading a One-Bit Function off Its Fourier Coefficients

**Claim.** Let $f\colon\{0,1\}^1\to\mathbb{R}$ be a real-valued function of a single bit, and let $\hat f(\emptyset)$ and $\hat f(\{0\})$ denote its two Fourier–Walsh coefficients, indexed by the only two frequency sets available on one coordinate: the empty set and the singleton $\{0\}$. Writing $x_1$ for the input whose sole coordinate carries the bit value $\mathrm{true}$ — the value that the sign encoding sends to $-1$ — the function's value there is the difference of these two coefficients, $f(x_1)=\hat f(\emptyset)-\hat f(\{0\})$.

**Proof.** The argument is simply the Fourier–Walsh expansion written out in full on a single coordinate and evaluated at the point $x_1$.

1. **Expand into characters.** For any point $x$ of the cube, the Fourier–Walsh expansion (`walsh_expansion`) expresses $f$ as the sum of its coefficients against the parity characters,
\[
  f(x)=\sum_{S}\hat f(S)\,\chi_S(x),
\]
the sum ranging over all subsets $S$ of the coordinate set. Here the coordinate set is a one-element set, so the only two subsets are $\emptyset$ and $\{0\}$; that the collection of all subsets is exactly the pair $\{\emptyset,\{0\}\}$ is the bookkeeping fact `finsetFin1_univ`, and that these two subsets are distinct — so the sum over the pair genuinely splits into two terms — is `finsetFin1_ne`. The expansion therefore collapses to
\[
  f(x)=\hat f(\emptyset)\,\chi_\emptyset(x)+\hat f(\{0\})\,\chi_{\{0\}}(x).
\]

2. **Evaluate the two characters at $x_1$.** By definition $\chi_S(x)=\prod_{i\in S}\mathrm{sign}(x_i)$, where the sign encoding sends $\mathrm{true}$ to $-1$ and $\mathrm{false}$ to $+1$. For $S=\emptyset$ the product is empty, so $\chi_\emptyset(x_1)=1$. For $S=\{0\}$ the product has the single factor $\mathrm{sign}\big((x_1)_0\big)$; since the sole coordinate of $x_1$ is $\mathrm{true}$, this factor is $-1$, and so $\chi_{\{0\}}(x_1)=-1$.

3. **Combine.** Substituting these two values,
\[
  f(x_1)=\hat f(\emptyset)\cdot 1+\hat f(\{0\})\cdot(-1)=\hat f(\emptyset)-\hat f(\{0\}),
\]
which is the claimed identity.

**Key facts.** `BooleanAnalysis.walsh_expansion`, `BooleanAnalysis.Hypercontractivity.finsetFin1_univ`, `BooleanAnalysis.Hypercontractivity.finsetFin1_ne`.
