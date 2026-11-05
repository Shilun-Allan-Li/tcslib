<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/KKL/Basic.lean :: KKL.fourierCoeff_lowDegreePart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Fourier coefficients of the low-degree truncation

**Claim.** Let $f:\{0,1\}^n\to\mathbb R$ be a function on the uniform Boolean cube, let $k\in\mathbb N$, and let $f^{\le k}$ be the degree-$k$ truncation of $f$, i.e. the function obtained by keeping only those Fourier terms of $f$ indexed by sets of size at most $k$. Then for every $S\subseteq[n]$ the Fourier coefficient of the truncation is $\widehat{f^{\le k}}(S)=\widehat f(S)$ when $|S|\le k$, and $\widehat{f^{\le k}}(S)=0$ when $|S|>k$. In words: truncating to degree $k$ keeps the low-degree coefficients unchanged and kills the high-degree ones.

**Proof.** Throughout, $\langle g,h\rangle=\mathbb E_{x}\,[g(x)h(x)]$ denotes the inner product under the uniform measure on $\{0,1\}^n$, the characters are $\chi_T(x)=\prod_{i\in T}(-1)^{x_i}$, and $\widehat g(T)=\langle g,\chi_T\rangle$. By definition the truncation is the explicit Fourier expansion
\[
f^{\le k}(x)=\sum_{T\subseteq[n]}\mathbf 1[\,|T|\le k\,]\;\widehat f(T)\,\chi_T(x),
\]
so the entire statement is a single computation of $\langle f^{\le k},\chi_S\rangle$, carried out exactly as follows.

1. **Expand by linearity.** Writing the Fourier coefficient as an expectation and inserting the definition of $f^{\le k}$,
\[
\widehat{f^{\le k}}(S)=\Big\langle \sum_{T}\mathbf 1[|T|\le k]\,\widehat f(T)\,\chi_T,\;\chi_S\Big\rangle
=\mathbb E_x\Big[\Big(\sum_{T}\mathbf 1[|T|\le k]\,\widehat f(T)\,\chi_T(x)\Big)\chi_S(x)\Big].
\]
Since the sum over $T$ is finite, the expectation (a weighted finite sum over $x$) commutes with it; distributing $\chi_S(x)$ across the sum and interchanging the order of summation over $x$ and over $T$ gives
\[
\widehat{f^{\le k}}(S)=\sum_{T}\mathbf 1[|T|\le k]\,\widehat f(T)\,\mathbb E_x\big[\chi_T(x)\chi_S(x)\big]
=\sum_{T}\mathbf 1[|T|\le k]\,\widehat f(T)\,\langle\chi_T,\chi_S\rangle .
\]
This is the only genuinely "analytic" move; everything after it is bookkeeping.

2. **Apply orthonormality of the characters.** The characters form an orthonormal system: $\langle\chi_T,\chi_S\rangle=\mathbf 1[T=S]$ (`BooleanAnalysis.fourier_coeff_chi`). Substituting, every term with $T\ne S$ vanishes, so
\[
\widehat{f^{\le k}}(S)=\sum_{T}\mathbf 1[|T|\le k]\,\widehat f(T)\,\mathbf 1[T=S].
\]

3. **Collapse the Kronecker delta.** Only the term $T=S$ survives the factor $\mathbf 1[T=S]$, and in that term the side condition $\mathbf 1[|T|\le k]$ becomes $\mathbf 1[|S|\le k]$. Reading off the single surviving summand,
\[
\widehat{f^{\le k}}(S)=\mathbf 1[|S|\le k]\,\widehat f(S)
=\begin{cases}\widehat f(S), & |S|\le k,\\[2pt] 0, & |S|>k,\end{cases}
\]
which is exactly the claim.

**Key facts.** `BooleanAnalysis.fourier_coeff_chi`.
