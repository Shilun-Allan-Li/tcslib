<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/KKL/Basic.lean :: KKL.lowDegree_l2_error -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Squared truncation error equals the high-degree Fourier weight

**Claim.** Let $f:\{0,1\}^n\to\mathbb R$ be a real function on the uniform Boolean cube and let $k\in\mathbb N$. Write $f^{\le k}=\sum_{|S|\le k}\widehat f(S)\,\chi_S$ for the degree-$\le k$ truncation of $f$, and $\mathbb E[\,\cdot\,]$ for the average over the uniformly random point of the cube. Then the mean-squared error incurred by replacing $f$ with its truncation equals the Fourier mass carried by the levels above $k$: $\mathbb E\big[(f-f^{\le k})^2\big]=\sum_{|S|>k}\widehat f(S)^2.$

**Proof.** The argument is the orthogonality calculation one expects, but it is routed deliberately through the *high-degree part* $f^{>k}$ (the library's complementary piece to $f^{\le k}$) rather than manipulating the truncation directly: the error function is recognised as $f^{>k}$, Parseval is applied to it, and its Fourier coefficients are then read off by subtraction.

1. **The error is the high-degree part.** The library records that the low- and high-degree parts reconstruct $f$ pointwise: $f^{\le k}(x)+f^{>k}(x)=f(x)$ for every $x$ (`low_plus_high_eq`). Rearranging gives $f(x)-f^{\le k}(x)=f^{>k}(x)$, so the pointwise error is exactly the high-degree part $f^{>k}$.

2. **Rewrite the squared error as a self inner product.** By definition the quantity in question is $\mathbb E\big[(f-f^{\le k})^2\big]$. Substituting the identity of Step 1 under the expectation and writing $t^2=t\cdot t$ turns this into $\mathbb E\big[f^{>k}\cdot f^{>k}\big]=\langle f^{>k},f^{>k}\rangle$, where $\langle g,h\rangle:=\mathbb E[g\,h]$ is the inner product on the cube.

3. **Apply Parseval.** Parseval's identity (`parseval`) states that $\langle g,g\rangle=\sum_{S}\widehat g(S)^2$ for any $g$, the sum running over all subsets $S\subseteq\{1,\dots,n\}$. Taking $g=f^{>k}$ gives
\[
\mathbb E\big[(f-f^{\le k})^2\big]=\sum_{S}\widehat{f^{>k}}(S)^2 .
\]
It remains to identify these coefficients level by level.

4. **Fourier coefficients of the high-degree part.** Fix $S$. Using $f^{>k}=f-f^{\le k}$ from Step 1 and the linearity of the inner product in its first slot (expand $\langle f-f^{\le k},\chi_S\rangle=\mathbb E[(f-f^{\le k})\chi_S]$ and split the averaging sum), we get $\widehat{f^{>k}}(S)=\widehat f(S)-\widehat{f^{\le k}}(S)$. The coefficients of the truncation are supplied by `fourierCoeff_lowDegreePart`: because $f^{\le k}$ is the projection of $f$ onto the characters of degree $\le k$ and these characters are orthonormal, $\widehat{f^{\le k}}(S)=\widehat f(S)$ when $|S|\le k$ and $0$ otherwise. Hence:
   - if $|S|\le k$, then $\widehat{f^{>k}}(S)=\widehat f(S)-\widehat f(S)=0$;
   - if $|S|>k$, then $\widehat{f^{>k}}(S)=\widehat f(S)-0=\widehat f(S)$.
   In short, $\widehat{f^{>k}}(S)=\widehat f(S)$ for $|S|>k$ and vanishes for $|S|\le k$.

5. **Conclude.** Feeding Step 4 into the sum of Step 3, each term $\widehat{f^{>k}}(S)^2$ equals $\widehat f(S)^2$ when $|S|>k$ and $0$ otherwise (since $0^2=0$). Therefore $\sum_{S}\widehat{f^{>k}}(S)^2=\sum_{|S|>k}\widehat f(S)^2$, which is the asserted identity.

**Key facts.** `KKL.low_plus_high_eq`, `BooleanAnalysis.parseval`, `KKL.fourierCoeff_lowDegreePart`.
