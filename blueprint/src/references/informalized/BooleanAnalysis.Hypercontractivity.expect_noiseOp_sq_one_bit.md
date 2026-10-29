<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/OneBit.lean :: BooleanAnalysis.Hypercontractivity.expect_noiseOp_sq_one_bit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Expected square of a noised one-bit function

**Claim.** Fix a real number $\rho$ and a Boolean function $f\colon\{0,1\}^1\to\mathbb{R}$ of a single bit. Let $T_\rho$ be the spectral noise operator, which scales the Fourier coefficient at each frequency $S$ by $\rho^{|S|}$. Then the expected square of $T_\rho f$ under the uniform measure on $\{0,1\}^1$ equals $\hat f(\emptyset)^2 + \rho^2\,\hat f(\{0\})^2$, where $\emptyset$ and $\{0\}$ are the only two subsets of the one-element coordinate set.

**Proof.** The argument is a direct instance of Parseval's identity, specialised to a single coordinate where the frequency set has exactly two elements.

1. **From an expected square to an inner product.** The expectation $\mathbb{E}\big[(T_\rho f)^2\big]$ is, by the definitions of the uniform expectation and the inner product $\langle g, h\rangle = \mathbb{E}[g\,h]$, nothing other than $\langle T_\rho f,\,T_\rho f\rangle$: squaring a value and averaging is the same as pairing the function with itself. This is a purely notational rearrangement.

2. **Parseval.** The characters $\chi_S(x) = (-1)^{\sum_{i\in S}x_i}$ form an orthonormal basis for functions on the cube under this inner product, so for any $g$ one has $\langle g, g\rangle = \sum_{S}\hat g(S)^2$ (`parseval`). Applying this to $g = T_\rho f$ gives
\[
  \mathbb{E}\big[(T_\rho f)^2\big] \;=\; \sum_{S\subseteq\{0\}} \widehat{T_\rho f}(S)^2 .
\]

3. **Fourier coefficients of the noised function.** The noise operator acts diagonally on the Fourier side: its definition multiplies the coefficient at $S$ by $\rho^{|S|}$, and indeed $\widehat{T_\rho f}(S) = \rho^{|S|}\,\hat f(S)$ (`noiseOp_fourier`). Substituting turns the sum into $\sum_{S} \rho^{2|S|}\,\hat f(S)^2$.

4. **Enumerating the frequencies of one bit.** With a single coordinate, the collection of all subsets of the index set is precisely $\{\emptyset,\,\{0\}\}$ (`finsetFin1_univ`), and these two subsets are distinct (`finsetFin1_ne`), so the sum over all frequencies is the two-term sum over this pair.

5. **Evaluating the two terms.** The empty set has cardinality $0$, so its weight is $\rho^0 = 1$; the singleton $\{0\}$ has cardinality $1$, so its weight is $\rho^2$. Hence
\[
  \sum_{S} \rho^{2|S|}\,\hat f(S)^2 \;=\; \rho^{0}\,\hat f(\emptyset)^2 + \rho^{2}\,\hat f(\{0\})^2 \;=\; \hat f(\emptyset)^2 + \rho^2\,\hat f(\{0\})^2,
\]
which is the claimed value.

**Key facts.** `BooleanAnalysis.parseval`, `BooleanAnalysis.noiseOp_fourier`, `BooleanAnalysis.Hypercontractivity.finsetFin1_univ`, `BooleanAnalysis.Hypercontractivity.finsetFin1_ne`.
