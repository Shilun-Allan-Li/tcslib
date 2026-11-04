<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/KKL/Basic.lean :: KKL.lowDegreePart_depends_on_influential -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Approximating the low-degree part by an influential-coordinate junta

**Claim.** Let $f:\{0,1\}^n\to\mathbb R$ be a function on the uniform Boolean cube, let $k\in\mathbb N$, and let $\tau>0$. Write $J_\tau(f)=\{i : I_i(f)\ge\tau\}$ for its set of $\tau$-influential coordinates, where $I_i(h)=\tfrac14\,\mathbb E_x\big(h(x)-h(x^{(i)})\big)^2$ and $x^{(i)}$ flips coordinate $i$. Then there is a function $g$ depending only on the coordinates in $J_\tau(f)$ (a $J_\tau(f)$-junta) such that the low-degree truncation $f^{\le k}$ is close to it in mean square, namely $\mathbb E\big(f^{\le k}-g\big)^2\le n\tau$.

**Proof.** Throughout, $\hat f(S)=\mathbb E_x\,f(x)\chi_S(x)$ denotes the Fourier coefficient of $f$ at $S\subseteq\{1,\dots,n\}$, where $\chi_S(x)=\prod_{i\in S}(-1)^{x_i}$ is the corresponding character, and $f^{\le k}=\sum_{|S|\le k}\hat f(S)\,\chi_S$ is the low-degree part. Write $J=J_\tau(f)$ for brevity.

**1. The approximant.** Take
\[
g \;=\; \sum_{\substack{|S|\le k\\ S\subseteq J}} \hat f(S)\,\chi_S,
\]
that is, $f^{\le k}$ with every Fourier character whose support strays outside $J$ deleted. This is the natural candidate: it keeps exactly the part of $f^{\le k}$ that can be built from coordinates in $J$.

**2. $g$ is a $J$-junta.** Each surviving character $\chi_S$ has $S\subseteq J$, so its value $\prod_{i\in S}(-1)^{x_i}$ is determined by the coordinates of $x$ lying in $J$. Hence if $x$ and $y$ agree on every coordinate of $J$, then $\chi_S(x)=\chi_S(y)$ for all such $S$, and summing gives $g(x)=g(y)$. Thus $g$ depends only on $J$.

**3. The difference and its mean square (Parseval).** Subtracting term by term, the characters with $S\subseteq J$ cancel, leaving
\[
f^{\le k}-g \;=\; h \;:=\; \sum_{\substack{|S|\le k\\ S\not\subseteq J}} \hat f(S)\,\chi_S .
\]
Now $\mathbb E\,h^2=\langle h,h\rangle=\sum_T \hat h(T)^2$ by Parseval's identity (`parseval`). The Fourier coefficients of $h$ are read off from the orthonormality of the characters, $\langle\chi_S,\chi_T\rangle=[S=T]$ (`fourier_coeff_chi`): the inner product $\hat h(T)=\langle h,\chi_T\rangle$ picks out the single term $S=T$ from the defining sum, so
\[
\hat h(T)=\begin{cases}\hat f(T),& |T|\le k\ \text{and}\ T\not\subseteq J,\\[2pt] 0,&\text{otherwise.}\end{cases}
\]
Therefore
\[
\mathbb E\big(f^{\le k}-g\big)^2 \;=\; \sum_{\substack{|S|\le k\\ S\not\subseteq J}} \hat f(S)^2 \;\le\; \sum_{S\not\subseteq J} \hat f(S)^2 ,
\]
the inequality being the (harmless) step of dropping the degree restriction $|S|\le k$, which only adds nonnegative squares.

**4. Union bound over the excluded coordinates.** Using the Fourier formula for influence, $I_i(f)=\sum_{S\ni i}\hat f(S)^2$ (`influence_eq_sum_fourier`), the right-hand sum below expands and, after exchanging the order of summation, dominates term by term:
\[
\sum_{S\not\subseteq J}\hat f(S)^2 \;\le\; \sum_{i\notin J}\ \sum_{S\ni i}\hat f(S)^2 \;=\; \sum_{i\notin J} I_i(f).
\]
The comparison holds character by character: if $S\not\subseteq J$ then $S$ contains at least one coordinate $i\notin J$, so $\hat f(S)^2$ appears among the nonnegative terms on the right (formally, it is bounded by the single summand indexed by that $i$); if instead $S\subseteq J$ its left-hand contribution is $0$.

**5. Bounding the leftover influence.** Every coordinate $i\notin J$ fails the defining condition $I_i(f)\ge\tau$ of $J=J_\tau(f)$, so $I_i(f)<\tau$. Since there are at most $n$ coordinates in all,
\[
\sum_{i\notin J} I_i(f) \;\le\; \sum_{i\notin J}\tau \;\le\; n\tau .
\]
Chaining Steps 3–5 yields $\mathbb E\big(f^{\le k}-g\big)^2\le n\tau$, which together with the junta property of Step 2 completes the proof.

**Key facts.** `BooleanAnalysis.parseval`, `BooleanAnalysis.fourier_coeff_chi`, `BooleanAnalysis.influence_eq_sum_fourier`.
