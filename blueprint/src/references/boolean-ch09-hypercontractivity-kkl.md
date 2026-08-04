<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: 4ba63c9394e55298c5325a5d491092ceed68cf23063051ca11508391b4990d8f -->

<a id="pdf-4ba63c9394e5-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.90 -->
# Chapter 9. Basics of hypercontractivity

Context: Bonami (1970) proved the central hypercontractivity result. This chapter treats easier special cases covering nearly all applications; the full theorem's proof is deferred to Chapter 10.

<a id="pdf-4ba63c9394e5-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.97 -->
**The Hypercontractivity Theorem.** For `f : {-1,1}^n → ℝ` and `1 ≤ p ≤ q ≤ ∞`,

$$\lVert T_\rho f\rVert_q \le \lVert f\rVert_p \quad\text{for } 0 \le \rho \le \sqrt{\tfrac{p-1}{q-1}}.$$

<a id="pdf-4ba63c9394e5-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.96 -->
**Bonami Lemma.** If `f : {-1,1}^n → ℝ` has degree `k`, then

$$\lVert f\rVert_4 \le \sqrt{3}^{\,k}\,\lVert f\rVert_2.$$

Interpretation (compressed): a low-degree `f(x)` for `x ∼ {-1,1}^n` is a "reasonable" random variable, nicely distributed around its mean. The lemma has an easy inductive proof and already yields many hypercontractivity applications (KKL Theorem, Invariance Principle).

<a id="pdf-4ba63c9394e5-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.96 -->
**(2, q)-Hypercontractivity Theorem.** For `f : {-1,1}^n → ℝ` and `2 ≤ q ≤ ∞`,

$$\lVert T_{1/\sqrt{q-1}}\, f\rVert_q \le \lVert f\rVert_2.$$

Consequence: if `f` has degree at most `k`, then `‖f‖_q ≤ √(q-1)^k ‖f‖_2`. (Quantifies `T_ρ` as a smoothing operator / reasonableness of low-degree polynomials; generalizes the Level-1 Inequality to Level-k Inequalities and gives a Chernoff-like tail bound.)

<a id="pdf-4ba63c9394e5-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.96 -->
**(p, 2)-Hypercontractivity Theorem.** For `f : {-1,1}^n → ℝ` and `1 ≤ p ≤ 2`,

$$\lVert T_{\sqrt{p-1}}\, f\rVert_2 \le \lVert f\rVert_p.$$

Equivalently, `Stab_ρ[f] ≤ ‖f‖_{1+ρ}^2` for `0 ≤ ρ ≤ 1`. This is "equivalent" to the (2,q)-theorem via Hölder's inequality; specialized to `f : {-1,1}^n → {0,1}` it quantifies the noisy hypercube graph as a small-set expander (small `A`, `x ∈ A`, `y ∼ N_ρ(x)` ⟹ `y` unlikely in `A`).

<a id="pdf-4ba63c9394e5-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.90 -->
## 9.1. Low-degree polynomials are reasonable

(Motivational prose, compressed): random variables can behave badly; a small 4th-to-2nd moment ratio is a simple condition guaranteeing good behavior.

<a id="pdf-4ba63c9394e5-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.85 -->
**Definition 9.1.** For a real number `B ≥ 1`, a real random variable `X` is *B-reasonable* if

$$\mathbb{E}[X^4] \le B\,\mathbb{E}[X^2]^2,$$

equivalently `‖X‖_4 ≤ B^{1/4} ‖X‖_2`. Smaller `B` = more reasonable. Scale-invariant but not translation-invariant. Related (Ch. 11) 3rd-moment condition `E[|X|^3] ≤ B·E[X^2]^{3/2}`; the 4th-moment condition is strictly stronger since `E[|X|^3] = E[|X|·X^2] ≤ √(E[X^2])·√(E[X^4]) ≤ √B·E[X^2]^{3/2}`, though finite-3rd/infinite-4th-moment variables exist.

<a id="pdf-4ba63c9394e5-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.80 -->
**Example 9.2.** A uniform `x ∼ {-1,1}` is 1-reasonable. A standard Gaussian `g ∼ N(0,1)` has `E[g^4] = 3`, so is 3-reasonable. A uniform `u ∼ [-1,1]` is `9/5`-reasonable. (Continued p.3): these `B` are small constants. An "unreasonable" example: a highly biased Bernoulli `Pr[y=1] = 2^{-n}`, `Pr[y=0] = 1 - 2^{-n}` for large `n`, which is not `B`-reasonable unless `B ≥ 2^n`.

<a id="pdf-4ba63c9394e5-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.92 -->
**Proposition 9.3.** Let `X ≢ 0` be `B`-reasonable. Then for all `t > 0`,

$$\Pr\big[\,|X| \ge t\,\lVert X\rVert_2\,\big] \le B/t^4.$$

<a id="pdf-4ba63c9394e5-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.92 -->
**Proof.** By Markov's inequality applied to `X^4`:

$$\Pr[|X| \ge t\lVert X\rVert_2] = \Pr[X^4 \ge t^4 \lVert X\rVert_2^4] \le \frac{\mathbb{E}[X^4]}{t^4\,\mathbb{E}[X^2]^2} \le \frac{B}{t^4}. \qquad\square$$

<a id="pdf-4ba63c9394e5-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.90 -->
**Proposition 9.4.** Let `X ≢ 0` be `B`-reasonable. Then for all `t ∈ [0,1]`,

$$\Pr\big[\,|X| > t\,\lVert X\rVert_2\,\big] \ge (1 - t^2)^2 / B.$$

(Generalization: Exercise 9.12.)

<a id="pdf-4ba63c9394e5-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.90 -->
**Proof.** Apply the Paley–Zygmund inequality (second moment method) to `X^2`:

$$\Pr[|X| \ge t\lVert X\rVert_2] = \Pr[X^2 \ge t^2\mathbb{E}[X^2]] \ge \frac{(1-t^2)^2\,\mathbb{E}[X^2]^2}{\mathbb{E}[X^4]} \ge \frac{(1-t^2)^2}{B}. \qquad\square$$

<a id="pdf-4ba63c9394e5-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.90 -->
**Proposition 9.5.** Let `X` be a discrete random variable with pmf `π`, and set

$$\lambda = \min(\pi) = \min_{x \in \mathrm{range}(X)} \Pr[X = x].$$

Then `X` is `(1/λ)`-reasonable.

<a id="pdf-4ba63c9394e5-p003-b006"></a>
<!-- pdf-source: page=3; block=6; confidence=0.90 -->
**Proof.** Let `M = ‖X‖_∞`. Since `Pr[|X| = M] ≥ λ`, we have `λM^2 ≤ E[X^2]`, hence `M^2 ≤ E[X^2]/λ`. Then

$$\mathbb{E}[X^4] = \mathbb{E}[X^2 \cdot X^2] \le M^2\,\mathbb{E}[X^2] \le (1/\lambda)\,\mathbb{E}[X^2]^2. \qquad\square$$

<a id="pdf-4ba63c9394e5-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.90 -->
The converse of Proposition 9.5 fails: for X = (x₁+···+xₙ)/√n with uniform ±1 bits, X is nearly a standard Gaussian (large n) and is 3-reasonable, yet its "λ" ≈ 2⁻ⁿ is tiny. Building an unreasonable variable from independent uniform ±1 bits requires many bits (Prop 9.5) and a high-degree combination; e.g. Example 9.2's y = (1±x₁)(1+x₂)···(1+xₙ)/2ⁿ has degree n. High degree is indeed necessary, as the Bonami Lemma shows.

<a id="pdf-4ba63c9394e5-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.92 -->
**The Bonami Lemma.** For each k, if f : {−1,1}ⁿ → ℝ has degree at most k and x₁,…,xₙ are independent uniform ±1 bits, then f(x) is 9ᵏ-reasonable:

E[f⁴] ≤ 9ᵏ E[f²]²,  equivalently  ‖f‖₄ ≤ (√3)ᵏ ‖f‖₂.

<a id="pdf-4ba63c9394e5-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.90 -->
The Bonami Lemma is a special case of hypercontractivity, but many results (KKL Theorem, Invariance Principle) need only it. The proof is by induction on n; the only non-automatic step is an application of Cauchy–Schwarz.

<a id="pdf-4ba63c9394e5-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.88 -->
**Proof of the Bonami Lemma.** Assume k ≥ 1 (else f is constant, trivial). Induct on n; base case n = 0 trivial. For n ≥ 1 decompose f(x) = xₙ Dₙf(x) + Eₙf(x) (Proposition 2.24), where deg(Dₙf) ≤ k−1, deg(Eₙf) ≤ k, and Dₙf, Eₙf are independent of xₙ. Write d = Dₙf(x), e = Eₙf(x). Then

E[f⁴] = E[(xₙd + e)⁴] = E[xₙ⁴]E[d⁴] + 4E[xₙ³]E[d³e] + 6E[xₙ²]E[d²e²] + 4E[xₙ]E[de³] + E[e⁴],

using independence of xₙ from d and e. Next apply E[xₙ] = E[xₙ³] = 0 and E[xₙ²] = E[xₙ⁴] = 1 (continued next page).

<a id="pdf-4ba63c9394e5-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.85 -->
**Proof (continued).** The moment values give

E[f⁴] = E[d⁴] + 6E[d²e²] + E[e⁴]   (9.1),

and a similar simpler computation gives E[f²] = E[d²] + E[e²]   (9.2).

Since d = Dₙf has degree ≤ k−1 in n−1 variables, induction gives E[d⁴] ≤ 9^{k−1}E[d²]²; likewise E[e⁴] ≤ 9ᵏE[e²]² (deg Eₙf ≤ k). By Cauchy–Schwarz E[d²e²] ≤ √(E[d⁴])·√(E[e⁴]). Hence

E[f⁴] ≤ 9^{k−1}E[d²]² + 6√(9^{k−1}E[d²]²·9ᵏE[e²]²) + 9ᵏE[e²]² ≤ 9ᵏ(E[d²] + E[e²])² = 9ᵏE[f²]²,

using 9^{k−1}E[d²]² ≤ 9ᵏE[d²]² and (9.2). ∎

<a id="pdf-4ba63c9394e5-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.90 -->
Sharpness is explored in Exercises 9.2, 9.3, 9.37, 9.38. The final step needs only E[xᵢ⁴] ≤ 9 (not = 9), so the lemma also holds when the xᵢ are standard Gaussians, uniform on [−1,1], or a mixture (Exercise 9.4).

<a id="pdf-4ba63c9394e5-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.92 -->
**Corollary 9.6.** Let x₁,…,xₙ be independent (not necessarily identically distributed) with E[xᵢ] = E[xᵢ³] = 0 (holds, e.g., if −xᵢ has the same distribution as xᵢ), each xᵢ being B-reasonable. If f = F(x₁,…,xₙ) with F multilinear of degree at most k, then f is max(B, 9)ᵏ-reasonable.

<a id="pdf-4ba63c9394e5-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.90 -->
First application: combine the Bonami Lemma with Proposition 9.4 to show a low-degree function is not too concentrated around its mean.

<a id="pdf-4ba63c9394e5-p005-b005"></a>
<!-- pdf-source: page=5; block=5; confidence=0.92 -->
**Theorem 9.7.** Let f : {−1,1}ⁿ → ℝ be nonconstant of degree at most k; write µ = E[f], σ = √Var[f]. Then

Pr_{x∼{−1,1}ⁿ}[ |f(x) − µ| > ½σ ] ≥ (1/16)·9⁻ᵏ.

<a id="pdf-4ba63c9394e5-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.88 -->
**Proof.** Let g = (1/σ)(f − µ), a function of degree at most k with ‖g‖₂ = 1. By the Bonami Lemma g is 9ᵏ-reasonable. The result follows by applying Proposition 9.4 to g with t = ½. ∎

<a id="pdf-4ba63c9394e5-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.90 -->
Theorem 9.7 gives a short proof of the FKN Theorem (Chapter 2.5): if f : {−1,1}ⁿ → {−1,1} has W¹[f] ≥ 1−δ, then f is O(δ)-close to ±χᵢ for some i ∈ [n].

<a id="pdf-4ba63c9394e5-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.93 -->
**Proof of the FKN Theorem.** Write $\ell = f^{=1}$, so $\mathbb{E}[\ell^2] = \mathbf{W}^1[f] = 1-\delta$; WLOG $\delta \le \tfrac{1}{1600}$. It suffices to show $\mathrm{Var}[\ell^2] \le 6400\delta$, because (Exercise 1.20)

$$\tfrac12\mathrm{Var}[\ell^2] = \sum_{i\neq j}\hat f(i)^2\hat f(j)^2 = \Big(\sum_i \hat f(i)^2\Big)^2 - \sum_i \hat f(i)^4 = (1-\delta)^2 - \sum_i\hat f(i)^4 \ge (1-2\delta) - \sum_i\hat f(i)^4.$$

Then $\mathrm{Var}[\ell^2]\le 6400\delta$ gives $1-3202\delta \le \sum_i \hat f(i)^4 \le \max_i\hat f(i)^2\cdot\sum_i\hat f(i)^2 \le \max_i\hat f(i)^2 \le \max_i|\hat f(i)|$, giving closeness to $\pm\chi_i$.

To bound $\mathrm{Var}[\ell^2]$, apply Theorem 9.7 to the degree-2 function $\ell^2$, yielding $\Pr[\,|\ell^2 - (1-\delta)| \ge \tfrac12\sqrt{\mathrm{Var}[\ell^2]}\,] \ge \tfrac1{16}9^{1-2} = \tfrac1{144}$. Now suppose for contradiction $\mathrm{Var}[\ell^2] > 6400\delta$; then

$$\tfrac1{144} \le \Pr[\,|\ell^2 - (1-\delta)| > 40\sqrt\delta\,] \le \Pr[\,|\ell^2 - 1| > 39\sqrt\delta\,].\tag{9.3}$$

Since $|f|\equiv 1$, a short calculation (Exercise 9.5) gives $(f-\ell)^2 \ge 169\delta$ whenever $|\ell^2-1|>39\sqrt\delta$. By (9.3), $\mathbb{E}[(f-\ell)^2] \ge \tfrac1{144}\cdot 169\delta > \delta$, contradicting $\mathbb{E}[(f-\ell)^2] = 1 - \mathbf{W}^1[f] = \delta$. Hence $\mathrm{Var}[\ell^2]\le 6400\delta$. $\square$

<a id="pdf-4ba63c9394e5-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.95 -->
## 9.2. Small subsets of the hypercube are noise-sensitive

<a id="pdf-4ba63c9394e5-p006-b005"></a>
<!-- pdf-source: page=6; block=5; confidence=0.85 -->
Immediate consequence of the Bonami Lemma: for any f : {−1,1}ⁿ → ℝ and k ∈ ℕ,

‖T_{1/√3} f^{=k}‖₄ = (1/√3)ᵏ ‖f^{=k}‖₄ ≤ ‖f^{=k}‖₂.   (9.4)

<a id="pdf-4ba63c9394e5-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.90 -->
Notes that the preceding degree-k result is a special case of the (2,4)-Hypercontractivity Theorem, which drops the degree-k homogeneity assumption.

<a id="pdf-4ba63c9394e5-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.95 -->
**(2,4)-Hypercontractivity Theorem.** For $f:\{-1,1\}^n\to\mathbb{R}$,
$$\|T_{1/\sqrt{3}}f\|_4 \le \|f\|_2.$$

<a id="pdf-4ba63c9394e5-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.85 -->
Summing (9.4) over $k$ can be made to work (Exercise 9.6), but the induction from the Bonami Lemma is used instead.

<a id="pdf-4ba63c9394e5-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.92 -->
**Proof.** Show $\mathbb{E}[(Tf)(x)^4]\le \mathbb{E}[f(x)^2]^2$ by the same Bonami induction, with $T=T_{1/\sqrt3}$; retaining the notation $d,e$, we have $Tf = x_n\cdot\tfrac1{\sqrt3}Td + Te$. Similar computations to the Bonami Lemma proof yield

$$\begin{aligned}\mathbb{E}[(Tf)^4] &= \big(\tfrac1{\sqrt3}\big)^4\mathbb{E}[(Td)^4] + 6\big(\tfrac1{\sqrt3}\big)^2\mathbb{E}[(Td)^2(Te)^2] + \mathbb{E}[(Te)^4]\\ &\le \mathbb{E}[(Td)^4] + 2\,\mathbb{E}[(Td)^2(Te)^2] + \mathbb{E}[(Te)^4]\\ &\le \mathbb{E}[(Td)^4] + 2\sqrt{\mathbb{E}[(Td)^4]}\sqrt{\mathbb{E}[(Te)^4]} + \mathbb{E}[(Te)^4]\\ &\le \mathbb{E}[d^2]^2 + 2\,\mathbb{E}[d^2]\mathbb{E}[e^2] + \mathbb{E}[e^2]^2\\ &= \big(\mathbb{E}[d^2]+\mathbb{E}[e^2]\big)^2 = \mathbb{E}[f^2]^2,\end{aligned}$$

where the second inequality is Cauchy–Schwarz, the third is induction, and the final equality is analogous to (9.2). $\square$

<a id="pdf-4ba63c9394e5-p007-b005"></a>
<!-- pdf-source: page=7; block=5; confidence=0.85 -->
Explains the name: $T_{1/\sqrt3}$ is not only an $L^2$ contraction but even a contraction $L^2\to L^4$. Notes $\|T_{1/\sqrt3}f\|_4$ lacks combinatorial meaning, whereas $\|T_{1/\sqrt3}f\|_2=\sqrt{\langle T_{1/\sqrt3}f,T_{1/\sqrt3}f\rangle}=\sqrt{\langle f,T_{1/\sqrt3}T_{1/\sqrt3}f\rangle}=\sqrt{\mathrm{Stab}_{1/3}[f]}$ does; this quantity is exposed by "flipping the norms across 2" via Hölder's inequality, using self-adjointness of $T_{1/\sqrt3}$.

<a id="pdf-4ba63c9394e5-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.95 -->
**(4/3,2)-Hypercontractivity Theorem.** For $f:\{-1,1\}^n\to\mathbb{R}$,
$$\|T_{1/\sqrt3}f\|_2 \le \|f\|_{4/3};$$
i.e. $\mathrm{Stab}_{1/3}[f]\le \|f\|_{4/3}^2$. (9.5)

<a id="pdf-4ba63c9394e5-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.90 -->
**Proof.** With $T=T_{1/\sqrt3}$: $\|Tf\|_2^2=\langle Tf,Tf\rangle=\langle f,TTf\rangle\le\|f\|_{4/3}\,\|TTf\|_4\le\|f\|_{4/3}\,\|Tf\|_2$ (9.6), by Hölder's inequality and the (2,4)-Hypercontractivity Theorem applied to $Tf$. Divide through by $\|Tf\|_2$ (assumed nonzero). $\square$

<a id="pdf-4ba63c9394e5-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.85 -->
The LHS of (9.5) is natural; the RHS is just 1 for $f:\{-1,1\}^n\to\{-1,1\}$, but interesting for $f:\{-1,1\}^n\to\{0,1\}$.

<a id="pdf-4ba63c9394e5-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.95 -->
**Corollary 9.8.** Let $A\subseteq\{-1,1\}^n$ have volume $\alpha$, i.e. $1_A:\{-1,1\}^n\to\{0,1\}$ with $\mathbb{E}[1_A]=\alpha$. Then
$$\mathrm{Stab}_{1/3}[1_A]=\Pr_{x\sim\{-1,1\}^n,\;y\sim N_{1/3}(x)}[x\in A,\;y\in A]\le\alpha^{3/2}.$$
Equivalently (for $\alpha>0$), $\Pr_{x\sim A,\;y\sim N_{1/3}(x)}[y\in A]\le\alpha^{1/2}.$

<a id="pdf-4ba63c9394e5-p008-b005"></a>
<!-- pdf-source: page=8; block=5; confidence=0.85 -->
**Proof.** Immediate from (9.5): $\|1_A\|_{4/3}^2=\big(\mathbb{E}_x|1_A(x)|^{4/3}\big)^{3/2}=\big(\mathbb{E}_x[1_A(x)]\big)^{3/2}=\alpha^{3/2}$. $\square$ (Generalization to other noise rates: Section 9.5.)

<a id="pdf-4ba63c9394e5-p008-b006"></a>
<!-- pdf-source: page=8; block=6; confidence=0.85 -->
**Example 9.9.** Take $\alpha=2^{-k}$, $k\in\mathbb{N}^+$, $A$ a subcube of codimension $k$ (e.g. $1_A:\mathbb{F}_2^n\to\{0,1\}$ the AND of the first $k$ coordinates). For $x\in A$, $y\sim N_{1/3}(x)$ lies in $A$ iff the first $k$ coordinates are unchanged, with probability $(2/3)^k=(2/3)^{\log(1/\alpha)}=\alpha^{\log(3/2)}=\alpha^{.585}\le\alpha^{1/2}$. The bound $\alpha^{1/2}$ is essentially sharp when $A$ is a Hamming ball (Exercise 9.24).

<a id="pdf-4ba63c9394e5-p008-b007"></a>
<!-- pdf-source: page=8; block=7; confidence=0.90 -->
**Definition 9.10.** For $n\in\mathbb{N}^+$ and $\rho\in[-1,1]$, the $n$-dimensional $\rho$-stable hypercube graph is the edge-weighted complete directed graph on $\{-1,1\}^n$ where the weight on directed edge $(x,y)$ equals $\Pr[(x,y)]$ for a $\rho$-correlated pair $(x,y)$. When $\rho=1-2\delta$ with $\delta\in[0,1]$, it is also called the $\delta$-noisy hypercube graph. (Weight formula continues on the next page.)

<a id="pdf-4ba63c9394e5-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.90 -->
The weight on $(x,y)$ is $\Pr[(x,y)]$ where $x\sim\{-1,1\}^n$ is uniform and $y$ is formed from $x$ by independently negating each coordinate with probability $\delta$.

<a id="pdf-4ba63c9394e5-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.95 -->
**Remark 9.11.** Edge weights are nonnegative and sum to 1. The graph is regular: total edge weight leaving (or entering) each $x$ is $2^{-n}$. It is symmetric ($\mathrm{wt}(x,y)=\mathrm{wt}(y,x)$), so it may be viewed as undirected with undirected-edge weight $2^{1-n}\,\delta^{\Delta(x,y)}(1-\delta)^{n-\Delta(x,y)}$. Best viewed as the discrete-time reversible Markov chain on $\{-1,1\}^n$ where a step from $x$ moves to $y\sim N_\rho(x)$, with uniform stationary distribution; one discrete step equals running the usual continuous-time hypercube chain for time $t=\ln(1/\rho)$ (for $\rho\in[0,1]$).

<a id="pdf-4ba63c9394e5-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.85 -->
Corollary 9.8 says the $1/3$-stable ($=1/3$-noisy) hypercube graph is a small-set expander: for a random vertex $x\in A$ ($A$ an $\alpha$-fraction) and a random edge out of $x$, one lands outside $A$ with probability $\ge 1-\alpha^{1/2}$. Compare the Level-1 Inequality (Section 5.4), the $\rho\to0^+$ limit; the general-$\rho$ statement is the Small-Set Expansion Theorem (Section 9.5).

<a id="pdf-4ba63c9394e5-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.85 -->
Corollary 9.8 also holds with $1_A$ replaced by $g:\{-1,1\}^n\to\{-1,0,1\}$, taking $\alpha=\Pr[g\ne0]=\mathbb{E}[g^2]$. This arises with $g=D_i f$ for Boolean $f:\{-1,1\}^n\to\{-1,1\}$, where $\mathrm{Stab}_{1/3}[g]=\mathrm{Inf}_i^{(1/3)}[f]$ (the $1/3$-stable influence of $i$), yielding the next corollary.

<a id="pdf-4ba63c9394e5-p009-b005"></a>
<!-- pdf-source: page=9; block=5; confidence=0.95 -->
**Corollary 9.12.** For $f:\{-1,1\}^n\to\{-1,1\}$, $\;\mathrm{Inf}_i^{(1/3)}[f]\le \mathrm{Inf}_i[f]^{3/2}$ for all $i$.

<a id="pdf-4ba63c9394e5-p009-b006"></a>
<!-- pdf-source: page=9; block=6; confidence=0.85 -->
Notes the KKL Theorem (Chapter 4.2) essentially follows by summing Corollary 9.12 over $i\in[n]$ (proof in Section 9.6). Reframing Corollary 9.8: since noise stability roughly measures how low a function's Fourier weight sits, an $f:\{-1,1\}^n\to\{0,1\}$ with small mean $\alpha$ cannot have much Fourier weight at low degree (statement continues beyond these pages).

<a id="pdf-4ba63c9394e5-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.90 -->
Derives level-$k$ inequalities. For $k\in\mathbb N$, from $\alpha^{3/2}\ge\mathrm{Stab}_{1/3}[f]\ge(1/3)^k\,W^{\le k}[f]$ it follows that
$$W^{\le k}[f]\le 3^k\alpha^{3/2}.\tag{9.7}$$
For $k=1$: $W^{\le1}[f]\le3\alpha^{3/2}$ (nontrivial but weaker than the Level-1 Inequality of §5.4). For larger $k$, e.g. $k=.25\log(1/\alpha)$, (9.7) gives $W^{\le.25\log(1/\alpha)}[f]\le \alpha^{-.25\log 3 + 3/2}\le\alpha^{1.1}\ll\alpha=\lVert f\rVert_2^2$, i.e. almost all of $f$'s Fourier weight is above degree $.25\log(1/\alpha)$. Improved versions are deferred to §9.5.

<a id="pdf-4ba63c9394e5-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.97 -->
**§9.3. $(2,q)$- and $(p,2)$-hypercontractivity for a single bit.**

<a id="pdf-4ba63c9394e5-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.86 -->
Bounding higher norms by the 2-norm would sharpen the concentration/anticoncentration results (Propositions 9.3, 9.4), and bounding the $(2+\varepsilon)$-norm strengthens the level-$k$ inequalities. The 4-norm was used first for simplicity (Bonami Lemma, $(2,4)$-Hypercontractivity Theorem). Generalization to other norms uses the hypercontractivity form: it is formally stronger (Theorem 9.21) and avoids the fact that being '$B$-reasonable' is not translation-invariant — one generalizes the condition $\|a+\rho bX\|_q\le\|a+bX\|_p$ (the $n=1$ case of $(2,4)$-Hypercontractivity) instead.

<a id="pdf-4ba63c9394e5-p010-b004"></a>
<!-- pdf-source: page=10; block=4; confidence=0.95 -->
**Definition 9.13.** For $1\le p\le q\le\infty$ and $0\le\rho<1$, a real random variable $X$ (with $\|X\|_q<\infty$) is *$(p,q,\rho)$-hypercontractive* if
$$\|a+\rho bX\|_q\le\|a+bX\|_p\quad\text{for all constants }a,b\in\mathbb R.$$

<a id="pdf-4ba63c9394e5-p010-b005"></a>
<!-- pdf-source: page=10; block=5; confidence=0.93 -->
**Remark 9.14.** By homogeneity it suffices to check the condition for $a=1$ (any $b\in\mathbb R$), or even for $a=b=1$ (cf. Exercise 9.9(a)). Also (Exercise 9.11), if $X$ is $(p,q,\rho)$-hypercontractive then it is $(p,q,\rho')$-hypercontractive for every $\rho'\le\rho$.

<a id="pdf-4ba63c9394e5-p010-b006"></a>
<!-- pdf-source: page=10; block=6; confidence=0.90 -->
Exercise 9.10: if $X$ is hypercontractive then $\mathrm E[X]=0$, so hypercontractivity (like reasonableness) is not translation-invariant. Nonetheless the translation by an arbitrary $a$ in the definition greatly facilitates proofs by induction (e.g. the property of Exercise 10.2).

<a id="pdf-4ba63c9394e5-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.95 -->
**Proposition 9.15.** If $X$ and $Y$ are independent $(p,q,\rho)$-hypercontractive random variables, then $X+Y$ is also $(p,q,\rho)$-hypercontractive.

<a id="pdf-4ba63c9394e5-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.90 -->
The $n=1$ case of the $(2,4)$-Hypercontractivity Theorem says a single uniform $\pm1$ bit $x$ is $(2,4,1/\sqrt3)$-hypercontractive; the $(4/3,2)$-Hypercontractivity Theorem says $x$ is also $(4/3,2,1/\sqrt3)$-hypercontractive. The rest of the section generalizes to $(2,q,\rho)$- and $(p,2,\rho)$-hypercontractivity, focusing on $p=2$ or $q=2$; the cases $p,q\ne2$ and non-uniform variables (other than $\pm1$ bits) are deferred to Chapter 10.

<a id="pdf-4ba63c9394e5-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.90 -->
$x$ is known $(2,q,1/\sqrt3)$-hypercontractive for $q=4$. To probe other $q$, try $q=6$; even integer $q$ is convenient since no absolute value is needed when computing $\|a+\rho bx\|_q$.

<a id="pdf-4ba63c9394e5-p011-b004"></a>
<!-- pdf-source: page=11; block=4; confidence=0.95 -->
**Proposition 9.16.** For $x$ a uniform $\pm1$ bit, $\|a+\rho bx\|_6\le\|a+bx\|_2$ for all $a,b\in\mathbb R$ if and only if $\rho\le1/\sqrt5$. That is, $x$ is $(2,6,1/\sqrt5)$-hypercontractive.

<a id="pdf-4ba63c9394e5-p011-b005"></a>
<!-- pdf-source: page=11; block=5; confidence=0.92 -->
**Proof.** Raising to the 6th power, show
$$\mathrm E[(a+\rho bx)^6]\le\mathrm E[(a+bx)^2]^3.\tag{9.8}$$
Trivial when $a=0$; otherwise set $a=1$ by homogeneity. Expanding and using $\mathrm E[x^k]=0$ for odd $k$, $=1$ for even $k$, (9.8) becomes
$$1+15\rho^2b^2+15\rho^4b^4+\rho^6b^6\le(1+b^2)^3=1+3b^2+3b^4+b^6.\tag{9.9}$$
Comparing term-by-term, the $b^2$ coefficient is the limiting factor: (9.9) holds for all $b\in\mathbb R$ iff $1+15\rho^2\le1+3$, i.e. $\rho\le1/\sqrt5$; necessity follows by letting $b\to0$. $\square$

<a id="pdf-4ba63c9394e5-p011-b006"></a>
<!-- pdf-source: page=11; block=6; confidence=0.83 -->
Repeating for $q=8$, the $b^2$ coefficient is again the limiting factor, and $x$ is $(2,8,\rho)$-hypercontractive iff $\rho^2\le\binom{4}{1}/\binom{8}{2}=1/7$, i.e. $\rho\le1/\sqrt7$. This motivates the general Theorem 9.17.

<a id="pdf-4ba63c9394e5-p011-b007"></a>
<!-- pdf-source: page=11; block=7; confidence=0.85 -->
**Theorem 9.17.** For $x$ a uniform $\pm1$ bit and $q\in[2,\infty]$,
$$\|a+\rho bx\|_q\le\|a+bx\|_2\quad\text{for all }a,b\in\mathbb R,\text{ assuming }\rho\le1/\sqrt{q-1}.$$
Equivalent statements: $\big\|a+\tfrac{1}{\sqrt{q-1}}bx\big\|_q^2\le a^2+b^2$; that $x$ is $(2,q,1/\sqrt{q-1})$-hypercontractive; and that $\|\mathrm T_{1/\sqrt{q-1}}f\|_q\le\|f\|_2$ holds for any $f:\{-1,1\}\to\mathbb R$.

<a id="pdf-4ba63c9394e5-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.92 -->
For even integer $q$, Theorem 9.17 proves as for $q=6$ (Exercise 9.36), even under more general moment conditions on $x$ as in Corollary 9.6. Obtaining Theorem 9.17 for all real $q>2$ takes more: naively forging ahead as in Proposition 9.16, using the series expansions for $(1+\rho bx)^q$ and $(1+b^2)^{q/2}$ from the Generalized Binomial Theorem (with $|b|<1$, so convergence is fine), fails because the coefficients in the expansion of $(1+b^2)^{q/2}$ are sometimes negative. The remedy: first prove the analogous $(p,2,\rho)$-hypercontractivity statement (where the negative coefficients vanish), then 'flip the norms across 2'.

<a id="pdf-4ba63c9394e5-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.93 -->
**Theorem 9.18.** For $x$ a uniform $\pm1$ bit and $1\le p\le2$,
$$\|a+\rho bx\|_2\le\|a+bx\|_p\quad\text{for all }a,b\in\mathbb R,\text{ assuming }0\le\rho\le\sqrt{p-1}.$$
That is, $x$ is $(p,2,\sqrt{p-1})$-hypercontractive.

<a id="pdf-4ba63c9394e5-p012-b003"></a>
<!-- pdf-source: page=12; block=3; confidence=0.88 -->
**Proof.** By Remark 9.14 assume $a=1$; by Exercise 9.7 reduce to $|b|\le1$, writing $b=\varepsilon$, at the extremal $\rho=\sqrt{p-1}$ (the $|b|=1$ case by continuity). Must show
$$\|1+\sqrt{p-1}\,\varepsilon x\|_2^p\le\|1+\varepsilon x\|_p^p,\quad\text{i.e.}\quad \mathrm E[(1+\sqrt{p-1}\,\varepsilon x)^2]^{p/2}\le\mathrm E[(1+\varepsilon x)^p].\tag{9.10}$$
The left side is $(1+(p-1)\varepsilon^2)^{p/2}\le1+\tfrac{p(p-1)}{2}\varepsilon^2$, (9.11) using $(1+t)^\theta\le1+\theta t$ for $t\ge0$, $0\le\theta\le1$. By the Generalized Binomial Theorem (valid since $|\varepsilon x|<1$) and $\mathrm E[x^{\text{odd}}]=0$, $\mathrm E[x^{\text{even}}]=1$, the right side is
$$\mathrm E[(1+\varepsilon x)^p]=1+\tfrac{p(p-1)}{2}\varepsilon^2+\frac{p(p-1)(p-2)(p-3)}{4!}\varepsilon^4+\frac{p(p-1)(p-2)(p-3)(p-4)(p-5)}{6!}\varepsilon^6+\cdots.$$
Each 'post-quadratic' term $\frac{p(p-1)(p-2)(p-3)\cdots(p-(2k-1))}{(2k)!}\varepsilon^{2k}$ is $\ge0$: for $1\le p\le2$ its numerator has two positive factors and an even number of negative factors. Hence the right side dominates the left, proving (9.10). $\square$

<a id="pdf-4ba63c9394e5-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.90 -->
To deduce Theorem 9.17 from Theorem 9.18 we again flip the norms across 2, using that $T_\rho$ is self-adjoint. This is accomplished by taking $\Omega=\{-1,1\}$, $\pi=\pi_{1/2}$, $q=2$, $T=T_{\sqrt{p-1}}$, and $C=1$ in the following Proposition 9.19 (noting that $1/\sqrt{p'-1}=\sqrt{p-1}$).

<a id="pdf-4ba63c9394e5-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.92 -->
**Proposition 9.19.** Let $T$ be a self-adjoint operator on $L^2(\Omega,\pi)$, let $1\le p,q\le\infty$, and let $p',q'$ be their conjugate Hölder indices. Assume $\|Tf\|_q\le C\|f\|_p$ for all $f$. Then $\|Tg\|_{p'}\le C\|g\|_{q'}$ for all $g$.

<a id="pdf-4ba63c9394e5-p013-b003"></a>
<!-- pdf-source: page=13; block=3; confidence=0.75 -->
**Proof.** $\|Tg\|_{p_0}=\sup_{\|f\|_p=1}\langle f,Tg\rangle=\sup_{\|f\|_p=1}\langle Tf,g\rangle\le\sup_{\|f\|_p=1}\|Tf\|_q\,\|g\|_{q_0}\le C\|g\|_{q_0}$. The first equality is sharpness of Hölder's inequality, the second is self-adjointness of $T$, the third is Hölder's inequality, and the last uses the hypothesis $\|Tf\|_q\le C\|f\|_p$. $\square$

<a id="pdf-4ba63c9394e5-p013-b004"></a>
<!-- pdf-source: page=13; block=4; confidence=0.60 -->
So far it is established that a uniform $\pm1$ bit $x$ is $(p,2,\sqrt{p-1})$-hypercontractive and $(2,q,1/\sqrt{q-1})$-hypercontractive. The next section uses a simple induction to obtain the full $(2,q)$- and $(p,2)$-Hypercontractivity Theorems.

<a id="pdf-4ba63c9394e5-p013-b005"></a>
<!-- pdf-source: page=13; block=5; confidence=0.95 -->
## 9.4. Two-Function Hypercontractivity and Induction

<a id="pdf-4ba63c9394e5-p013-b006"></a>
<!-- pdf-source: page=13; block=6; confidence=0.95 -->
For a single bit $f:\{-1,1\}\to\mathbb{R}$ we have $\|T_{\sqrt{p-1}}f\|_2\le\|f\|_p$ and $\|T_{1/\sqrt{q-1}}f\|_q\le\|f\|_2$ (for $p\le 2\le q$). Goal: extend to general $f:\{-1,1\}^n\to\mathbb{R}$ (the $(p,2)$- and $(2,q)$-Theorems) by induction on $n$. Two methods: "induction by derivatives", using $f(x)=x_nD_nf(x)+E_nf(x)$ (as in the Bonami Lemma), and "induction by restrictions", via the subfunctions $f_{\pm1}$ fixing the $n$th coordinate (as in the OSSS Inequality, Ch. 8.6). Both reduce one function to two ($D_nf,E_nf$ or $f_{+1},f_{-1}$), so it helps to prove a generalized two-function statement.

<a id="pdf-4ba63c9394e5-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.80 -->
Seeking a two-function form. The $(4/3,2)$-Theorem as noise stability reads $\mathrm{Stab}_{1/3}[f]\le\|f\|_{4/3}^2$. Theorem 9.18 (case $n=1$) generalizes this to $\mathrm{Stab}_{p-1}[f]\le\|f\|_p^2$ for $1\le p\le 2$, i.e. $\mathrm{Stab}_\rho[f]=\mathbb{E}_{(x,y)\ \rho\text{-correlated}}[f(x)f(y)]\le\|f\|_{1+\rho}^2$ for $0\le\rho\le1$.

<a id="pdf-4ba63c9394e5-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.80 -->
Guessed generalization for $f,g:\{-1,1\}^n\to\mathbb{R}$, eq. (9.12): $\mathbb{E}_{(x,y)\ \rho\text{-correlated}}[f(x)g(y)]\le\|f\|_{1+\rho}\,\|g\|_{1+\rho}$. Interpretation (Corollary 9.8): for indicators of $A,B\subseteq\{-1,1\}^n$ it upper-bounds the probability of stepping $A\to B$ on the $\rho$-stable hypercube graph; sharp when $A,B$ have equal volume, and for unequal sizes one expects to use different norms for $f$ and $g$.

<a id="pdf-4ba63c9394e5-p014-b003"></a>
<!-- pdf-source: page=14; block=3; confidence=0.95 -->
Split the correlation as $\rho=\sqrt{rs}$ with $0\le r,s\le1$, using $\mathbb{E}_{(x,y)\ \sqrt{rs}\text{-correlated}}[f(x)g(y)]=\mathbb{E}[\,T_{\sqrt r}f\cdot T_{\sqrt s}g\,]$. Then by Cauchy–Schwarz and $(p,2)$-hypercontractivity (proven for $n=1$, Thm 9.18), eq. (9.13): $\mathbb{E}_{(x,y)\ \rho\text{-correlated}}[f(x)g(y)]=\mathbb{E}[T_{\sqrt r}f\cdot T_{\sqrt s}g]\le\|T_{\sqrt r}f\|_2\|T_{\sqrt s}g\|_2\le\|f\|_{1+r}\|g\|_{1+s}$.

<a id="pdf-4ba63c9394e5-p014-b004"></a>
<!-- pdf-source: page=14; block=4; confidence=0.75 -->
**(Weak) Two-Function Hypercontractivity Theorem.** Let $f,g:\{-1,1\}^n\to\mathbb{R}$, let $0\le\rho\le1$, and assume $\rho=\sqrt{rs}$ with $0\le r,s\le1$. Then $\mathbb{E}_{(x,y)\ \rho\text{-correlated}}[f(x)g(y)]\le\|f\|_{1+r}\,\|g\|_{1+s}$.

<a id="pdf-4ba63c9394e5-p014-b005"></a>
<!-- pdf-source: page=14; block=5; confidence=0.85 -->
Called "Weak" because the hypothesis $r,s\le1$ is not actually necessary (see Ch. 10.1). So far established only for $n=1$.

<a id="pdf-4ba63c9394e5-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.85 -->
The theorem extends to general $n$ by an almost trivial "induction by restrictions" (extension via "induction by derivatives" is also possible; Exercise 9.16). The induction is stated in general notation below.

<a id="pdf-4ba63c9394e5-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.90 -->
**Two-Function Hypercontractivity Induction Theorem.** Let $0\le\rho\le1$ and assume $\mathbb{E}_{(x,y)\ \rho\text{-correlated}}[f(x)g(y)]\le\|f\|_p\,\|g\|_q$ holds for every $f,g\in L^2(\Omega,\pi)$. Then the same inequality holds for every $f,g\in L^2(\Omega^n,\pi^{\otimes n})$.

<a id="pdf-4ba63c9394e5-p015-b003"></a>
<!-- pdf-source: page=15; block=3; confidence=0.85 -->
**Proof.** Induction on $n$; the $n=1$ case holds by assumption. For $n>1$, take $f,g\in L^2(\Omega^n,\pi^{\otimes n})$ and a $\rho$-correlated pair $(x,y)$ under $\pi^{\otimes n}$. Write $x=(x_0,x_n)$ with $x_0=(x_1,\dots,x_{n-1})$, similarly $y$; then $(x_0,y_0)$ and $(x_n,y_n)$ are $\rho$-correlated pairs of lengths $n-1$ and $1$. Let $f^{x_n}$ be $f$ restricted to last coordinate $=x_n$. Then
$$\mathbb{E}_{(x,y)}[f(x)g(y)]=\mathbb{E}_{(x_n,y_n)}\mathbb{E}_{(x_0,y_0)}[f^{x_n}(x_0)g^{y_n}(y_0)]\le\mathbb{E}_{(x_n,y_n)}\big[\|f^{x_n}\|_p\,\|g^{y_n}\|_q\big]$$
by induction. Define $F(x_n)=\|f^{x_n}\|_p$ and $G(y_n)=\|g^{y_n}\|_q$ in $L^2(\Omega,\pi)$; the base case gives $\mathbb{E}_{(x_n,y_n)}[F(x_n)G(y_n)]\le\|F\|_p\|G\|_q$. Finally $\|F\|_p=(\mathbb{E}_{x_n}|F(x_n)|^p)^{1/p}=(\mathbb{E}_{x_n}\|f^{x_n}\|_p^p)^{1/p}=(\mathbb{E}_{x_n}\mathbb{E}_{x_0}|f^{x_n}(x_0)|^p)^{1/p}=\|f\|_p$, and similarly $\|G\|_q=\|g\|_q$. Hence $\mathbb{E}[f(x)g(y)]\le\|f\|_p\|g\|_q$, completing the induction. $\square$

<a id="pdf-4ba63c9394e5-p015-b004"></a>
<!-- pdf-source: page=15; block=4; confidence=0.90 -->
**Remark 9.20.** More generally, if the inequality holds over each $(\Omega_1,\pi_1),\dots,(\Omega_n,\pi_n)$, it also holds over the product $(\Omega_1\times\cdots\times\Omega_n,\ \pi_1\otimes\cdots\otimes\pi_n)$; only notational changes to the proof are needed.

<a id="pdf-4ba63c9394e5-p015-b005"></a>
<!-- pdf-source: page=15; block=5; confidence=0.85 -->
The Weak Two-Function Hypercontractivity Theorem is now fully established. Setting $g=f$ and $r=s=\rho$ gives the full $(p,2)$-Hypercontractivity Theorem; then applying Proposition 9.19 gives the $(2,q)$-Hypercontractivity Theorem for all $f:\{-1,1\}^n\to\mathbb{R}$.

<a id="pdf-4ba63c9394e5-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.90 -->
**9.5. Applications of hypercontractivity.** Revisiting applications from §9.1–9.2 using the $(2,q)$- and $(p,2)$-Hypercontractivity Theorems, starting with a generalization of the Bonami Lemma.

<a id="pdf-4ba63c9394e5-p016-b002"></a>
<!-- pdf-source: page=16; block=2; confidence=0.85 -->
**Theorem 9.21.** For $f:\{-1,1\}^n\to\mathbb{R}$ of degree at most $k$ and any $q\ge 2$,
$$\|f\|_q \le (q-1)^{k/2}\,\|f\|_2.$$

<a id="pdf-4ba63c9394e5-p016-b003"></a>
<!-- pdf-source: page=16; block=3; confidence=0.80 -->
**Proof.** $\|f\|_q^2 = \|T_{1/\sqrt{q-1}}\,T_{\sqrt{q-1}}f\|_q^2 \le \|T_{\sqrt{q-1}}f\|_2^2$ by the $(2,q)$-Hypercontractivity Theorem (extending $T_\rho$ to $\rho>1$ via $T_\rho f=\sum_j\rho^j f^{=j}$; cf. Remark 8.29). Then $\|T_{\sqrt{q-1}}f\|_2^2=\sum_{j=0}^k (q-1)^j W^j[f]\le (q-1)^k\sum_{j=0}^k W^j[f]=(q-1)^k\|f\|_2^2$.

<a id="pdf-4ba63c9394e5-p016-b004"></a>
<!-- pdf-source: page=16; block=4; confidence=0.70 -->
**Prose.** A trick like that in the $(4/3,2)$-Hypercontractivity proof yields reverse bounds $\|f\|_2\lesssim\|f\|_p$ for degree-$k$ $f$ and $1\le p\le 2$ (Exercise 9.14); a different trick gives a strictly better result with a finite bound even at $p=1$.

<a id="pdf-4ba63c9394e5-p016-b005"></a>
<!-- pdf-source: page=16; block=5; confidence=0.93 -->
**Theorem 9.22.** For $f:\{-1,1\}^n\to\mathbb{R}$ of degree at most $k$:
$$\|f\|_2 \le e^{k}\,\|f\|_1.$$
More generally, for $1\le p\le 2$,
$$\|f\|_2 \le \big(e^{\,2/p-1}\big)^{k}\,\|f\|_p.$$

<a id="pdf-4ba63c9394e5-p016-b006"></a>
<!-- pdf-source: page=16; block=6; confidence=0.90 -->
**Proof.** Only the $1$-norm case is shown (general $p$: Exercise 9.15). For $\varepsilon>0$ let $0<\theta<1$ solve $\tfrac12=\tfrac{\theta}{1}+\tfrac{1-\theta}{2+\varepsilon}$ (namely $\theta=\tfrac12\cdot\tfrac{\varepsilon}{1+\varepsilon}$). Applying the general Hölder inequality and then Theorem 9.21 gives
$$\|f\|_2\le\|f\|_{2+\varepsilon}^{1-\theta}\|f\|_1^{\theta}\le\sqrt{1+\varepsilon}^{\,k(1-\theta)}\|f\|_2^{1-\theta}\|f\|_1^{\theta}.$$
Dividing by $\|f\|_2^{1-\theta}$ (assumed nonzero) and raising to the power $1/\theta$ yields
$$\|f\|_2\le\big((1+\varepsilon)^{(1-\theta)/(2\theta)}\big)^{k}\|f\|_1=\big((1+\varepsilon)^{1/\varepsilon+1/2}\big)^{k}\|f\|_1.$$
Taking $\varepsilon\to0$ gives $\|f\|_2\le e^k\|f\|_1$. $\square$

<a id="pdf-4ba63c9394e5-p016-b007"></a>
<!-- pdf-source: page=16; block=7; confidence=0.80 -->
**Khintchine's Inequality.** In the linear case $k=1$, Theorems 9.21 and 9.22 together give constants $0<c_p\le C_p<\infty$ depending only on $p\in[1,\infty)$ with
$$c_p\,\Big\|\sum_i a_i x_i\Big\|_2 \le \Big\|\sum_i a_i x_i\Big\|_p \le C_p\,\Big\|\sum_i a_i x_i\Big\|_2.$$

<a id="pdf-4ba63c9394e5-p016-b008"></a>
<!-- pdf-source: page=16; block=8; confidence=0.80 -->
**Prose.** Theorem 9.21 yields strong concentration for degree-$k$ Boolean functions: whereas Chernoff gives $\Pr[\text{linear form exceeds } t \text{ std devs}]\approx\exp(-\Theta(t^2))$, the degree-$k$ analogue decays as $\exp(-\Theta(t^2/k))$.

<a id="pdf-4ba63c9394e5-p017-b001"></a>
<!-- pdf-source: page=17; block=1; confidence=0.95 -->
**Theorem 9.23.** For $f:\{-1,1\}^n\to\mathbb{R}$ of degree at most $k$ and any $t\ge (2e)^{k/2}$ (i.e. $t\ge\sqrt{2e}^{\,k}$),
$$\Pr_{x\sim\{-1,1\}^n}\big[|f(x)|\ge t\|f\|_2\big]\le \exp\!\Big(-\tfrac{k}{2e}\,t^{2/k}\Big).$$

<a id="pdf-4ba63c9394e5-p017-b002"></a>
<!-- pdf-source: page=17; block=2; confidence=0.72 -->
**Proof.** WLOG $\|f\|_2=1$. For $q\ge2$, Markov gives $\Pr[|f(x)|\ge t]=\Pr[|f(x)|^q\ge t^q]\le E[|f(x)|^q]/t^q$. By Theorem 9.21, $E[|f(x)|^q]=\|f\|_q^q\le (q-1)^{(k/2)q}\le q^{(k/2)q}$, so $\Pr[|f(x)|\ge t]\le (q^{k/2}/t)^q$. The minimizing $q$ is just below $t^{2/k}$; choosing $q=t^{2/k}/e\ (\ge2)$ gives $\Pr[|f(x)|\ge t]\le\exp(-\tfrac{k}{2}q)=\exp(-\tfrac{k}{2e}t^{2/k})$.

<a id="pdf-4ba63c9394e5-p017-b003"></a>
<!-- pdf-source: page=17; block=3; confidence=0.80 -->
**Prose.** Theorem 9.22 gives a one-sided analogue of Theorem 9.7: a low-degree nonconstant function exceeds its mean with noticeable probability.

<a id="pdf-4ba63c9394e5-p017-b004"></a>
<!-- pdf-source: page=17; block=4; confidence=0.85 -->
**Theorem 9.24.** For nonconstant $f:\{-1,1\}^n\to\mathbb{R}$ of degree at most $k$,
$$\Pr_{x\sim\{-1,1\}^n}\big[f(x)>E[f]\big]\ge \tfrac14 e^{-2k}.$$

<a id="pdf-4ba63c9394e5-p017-b005"></a>
<!-- pdf-source: page=17; block=5; confidence=0.82 -->
**Proof.** WLOG $E[f]=0$, so $\tfrac12\|f\|_1=E[f\cdot\mathbf{1}_{\{f>0\}}]$. Hence $\tfrac14\|f\|_1^2=E[f\cdot\mathbf{1}_{\{f>0\}}]^2\le E[f^2]\,E[\mathbf{1}^2_{\{f>0\}}]=\|f\|_2^2\,\Pr[f>0]\le e^{2k}\|f\|_1^2\,\Pr[f>0]$ using Cauchy–Schwarz and Theorem 9.22. Therefore $\Pr[f>0]\ge\tfrac14 e^{-2k}$.

<a id="pdf-4ba63c9394e5-p017-b006"></a>
<!-- pdf-source: page=17; block=6; confidence=0.80 -->
**Prose.** Turning to noise stability, the $(p,2)$-Hypercontractivity Theorem immediately gives the following generalization of Corollary 9.8.

<a id="pdf-4ba63c9394e5-p018-b001"></a>
<!-- pdf-source: page=18; block=1; confidence=0.82 -->
**Small-Set Expansion Theorem.** Let $A\subseteq\{-1,1\}^n$ with $1_A:\{-1,1\}^n\to\{0,1\}$ satisfying $E[1_A]=\alpha$. Then for any $0\le\rho\le1$,
$$\mathbf{Stab}_\rho[1_A]=\Pr_{\substack{x\sim\{-1,1\}^n\\ y\sim N_\rho(x)}}[x\in A,\ y\in A]\le \alpha^{2/(1+\rho)}.$$
Equivalently, for $\alpha>0$, $\displaystyle\Pr_{\substack{x\sim A\\ y\sim N_\rho(x)}}[y\in A]\le \alpha^{(1-\rho)/(1+\rho)}$.

<a id="pdf-4ba63c9394e5-p018-b002"></a>
<!-- pdf-source: page=18; block=2; confidence=0.95 -->
**Prose.** Interpretation: the $\delta$-noisy hypercube is a small-set expander for any $\delta>0$—from a random $x\in A$, one noisy step stays in $A$ with probability at most $\alpha^{\delta/(1-\delta)}$. A two-set generalization via the Two-Function Hypercontractivity Theorem (requiring its non-weak form) is deferred to Chapter 10.1.

<a id="pdf-4ba63c9394e5-p018-b003"></a>
<!-- pdf-source: page=18; block=3; confidence=0.95 -->
**Corollary 9.25.** For $f:\{-1,1\}^n\to\{-1,1\}$ and any $0\le\rho\le1$,
$$\mathrm{Inf}_i^{(\rho)}[f]\le \mathrm{Inf}_i[f]^{\,2/(1+\rho)}\quad\text{for all }i.$$

<a id="pdf-4ba63c9394e5-p018-b004"></a>
<!-- pdf-source: page=18; block=4; confidence=0.78 -->
**Prose.** By the Small-Set Expansion Theorem, indicators of small-volume sets are not very noise-stable and hence carry little low-level Fourier weight; hypercontractivity recovers the Level-1 Inequality (Ch 5.4) and generalizes it to higher degrees.

<a id="pdf-4ba63c9394e5-p018-b005"></a>
<!-- pdf-source: page=18; block=5; confidence=0.78 -->
**Level-$k$ Inequalities.** Let $f:\{-1,1\}^n\to\{0,1\}$ have mean $E[f]=\alpha$, and let $k\in\mathbb{N}^+$ satisfy $k\le 2\ln(1/\alpha)$. Then
$$W^{\le k}[f]\le \Big(\tfrac{2e\ln(1/\alpha)}{k}\Big)^{k}\alpha^2.$$

<a id="pdf-4ba63c9394e5-p018-b006"></a>
<!-- pdf-source: page=18; block=6; confidence=0.72 -->
**Proof.** By the Small-Set Expansion Theorem, for $0\le\rho\le1$, $W^{\le k}[f]\le\rho^{-k}\mathbf{Stab}_\rho[f]\le\rho^{-k}\alpha^{2/(1+\rho)}\le\rho^{-k}\alpha^{2(1-\rho)}$. The RHS is minimized at $\rho=\tfrac{k}{2\ln(1/\alpha)}\ (\le1$ by hypothesis$)$; substituting into $\rho^{-k}\alpha^{2(1-\rho)}$ gives the claim. For $k=1$ a sharper argument gives the Level-1 Inequality $W^1[f]\le 2\alpha^2\ln(1/\alpha)$ (Exercise 9.18).

<a id="pdf-4ba63c9394e5-p018-b007"></a>
<!-- pdf-source: page=18; block=7; confidence=0.90 -->
**9.6. Highlight: The Kahn–Kalai–Linial Theorem.**

<a id="pdf-4ba63c9394e5-p018-b008"></a>
<!-- pdf-source: page=18; block=8; confidence=0.70 -->
**Prose.** Setup (social choice, Ch 2.1): a 2-candidate, $n$-voter election with a monotone voting rule $f:\{-1,1\}^n\to\{-1,1\}$ under the impartial-culture assumption (independent uniform votes), with a twist—one candidate $b\in\{-1,1\}$ is able to … [text truncated at page end].

<a id="pdf-4ba63c9394e5-p019-b001"></a>
<!-- pdf-source: page=19; block=1; confidence=0.86 -->
Motivational setup (Ben-Or and Linial, 1985): a candidate secretly bribes k voters to fix their votes to b; for monotone f this is the optimal fixing. For k=1, bribing voter i to vote b (others uniform) shifts the bias of f by b·Inf_i[f] (uses monotonicity, Proposition 2.21). This motivates seeking unbiased f minimizing the maximum influence.

<a id="pdf-4ba63c9394e5-p019-b002"></a>
<!-- pdf-source: page=19; block=2; confidence=0.95 -->
**Definition 9.26.** For $f:\{-1,1\}^n\to\mathbb{R}$, the maximum influence is $\mathrm{MaxInf}[f]=\max\{\mathrm{Inf}_i[f] : i\in[n]\}$.

<a id="pdf-4ba63c9394e5-p019-b003"></a>
<!-- pdf-source: page=19; block=3; confidence=0.90 -->
Ben-Or and Linial's (nearly unbiased) $\mathrm{Tribes}_n:\{-1,1\}^n\to\{-1,1\}$ (Chapter 4.2) has $\mathrm{MaxInf}[\mathrm{Tribes}_n]=O(\tfrac{\log n}{n})$; they conjectured every unbiased $f$ has $\mathrm{MaxInf}[f]=\Omega(\tfrac{\log n}{n})$, proved by Kahn, Kalai, and Linial [KKL88].

<a id="pdf-4ba63c9394e5-p019-b004"></a>
<!-- pdf-source: page=19; block=4; confidence=0.92 -->
**KKL Theorem.** For any $f:\{-1,1\}^n\to\{-1,1\}$, $\mathrm{MaxInf}[f]\ge \mathrm{Var}[f]\cdot\Omega\!\big(\tfrac{\log n}{n}\big)$. The variance is the correct scaling factor: $\tfrac{1}{n}\mathrm{Var}[f]\le \mathrm{MaxInf}[f]\le \mathrm{Var}[f]$ holds trivially (Poincaré inequality and Exercise 2.8).

<a id="pdf-4ba63c9394e5-p019-b005"></a>
<!-- pdf-source: page=19; block=5; confidence=0.90 -->
**Proposition 9.27.** Let $f:\{-1,1\}^n\to\{-1,1\}$ be monotone with $\mathbb{E}[f]\ge .99$. Then there exists $J\subseteq[n]$ with $|J|\le O(n/\log n)$ such that fixing coordinates in $J$ to $1$ forces the outcome to $1$ almost surely:
$$\mathbb{E}[f_{J\to(1,\dots,1)}]\ge .99. \tag{9.14}$$
Symmetrically, if $\mathbb{E}[f]\le -.99$ there exists $J\subseteq[n]$ with $|J|\le O(n/\log n)$ such that $\mathbb{E}[f_{J\to(-1,\dots,-1)}]\le -.99$.

<a id="pdf-4ba63c9394e5-p019-b006"></a>
<!-- pdf-source: page=19; block=6; confidence=0.85 -->
**Proof.** By symmetry, suffices to handle bribery by candidate $+1$. Greedy strategy: bribe the voter $i_1$ of largest influence on $f_0=f$; then $i_2$ of largest influence on $f_1=f_{(i_1\to 1)}$; then $i_3$ of largest influence on $f_2=f_{(i_1,i_2\to 1)}$; etc. (continued on next page).

<a id="pdf-4ba63c9394e5-p020-b001"></a>
<!-- pdf-source: page=20; block=1; confidence=0.86 -->
For each $t\in\mathbb{N}$, $\mathbb{E}[f^{t+1}]\ge \mathbb{E}[f^t]+\mathrm{MaxInf}[f^t]$. If (9.14) is not yet achieved after $t$ bribes, then $\mathbb{E}[f^t]<.99$, so $\mathrm{Var}[f^t]\ge \Omega(1)$ and the KKL Theorem gives $\mathrm{MaxInf}[f^t]\ge \Omega(\tfrac{\log n}{n})$. Hence bias $\ge .99$ is reached after at most $(.99-(-.99))/\Omega(\tfrac{\log n}{n}) = O(n/\log n)$ bribes. $\qquad\square$

<a id="pdf-4ba63c9394e5-p020-b002"></a>
<!-- pdf-source: page=20; block=2; confidence=0.85 -->
Consequence: in any monotone election some candidate can bribe an $o(1)$-fraction of voters to make the outcome 99%-biased; if not too biased initially, both candidates can (see Exercises 9.27, 9.28). $\mathrm{Tribes}_n$ resists a single bribe but a single tribe (~$\log n$ voters) forces the output. Proposition 9.27 is near-sharp: Ajtai and Linial [AL93] built an unbiased monotone $f$ where bribing any $\le \varepsilon n/\log^2 n$ voters changes the expectation by $\le O(\varepsilon)$.

<a id="pdf-4ba63c9394e5-p020-b003"></a>
<!-- pdf-source: page=20; block=3; confidence=0.84 -->
The KKL proof follows from summing Corollary 9.12 over all coordinates. Main case: show $\mathrm{MaxInf}[f]=\Omega(\tfrac{\log n}{n})$ for unbiased $f$ ($\mathrm{Var}[f]=1$). If total influence $I[f]\ge .1\log n$ the average influence is already $\Omega(\tfrac{\log n}{n})$, so assume $I[f]\le .1\log n$. This is the problem of characterizing functions of small total influence: viewing $f$ as indicator of a volume-$1/2$ set $A$, $I[f]\cdot n$ is the number of Hamming-cube edges on $A$'s boundary; the edge-isoperimetric (Poincaré) inequality gives $I[f]\ge 1$ (minimized by dictators/negated-dictators). If $I[f]=K$, KKL show $f$ must resemble a (negated) dictator.

<a id="pdf-4ba63c9394e5-p021-b001"></a>
<!-- pdf-source: page=21; block=1; confidence=0.93 -->
**KKL Edge-Isoperimetric Theorem.** Let $f:\{-1,1\}^n\to\{-1,1\}$ be nonconstant and set $\widetilde{I}[f]=I[f]/\mathrm{Var}[f]\ge 1$ (which is just $I[f]$ if $f$ is unbiased). Then
$$\mathrm{MaxInf}[f]\ge \frac{9}{\widetilde{I}[f]^2}\cdot 9^{-\widetilde{I}[f]}.$$
This theorem is sharp for $\widetilde{I}[f]=1$ (cf. Exercises 1.19, 5.35) and nontrivial (in the unbiased case) for $I[f]$ as large as $\Theta(\log n)$.

<a id="pdf-4ba63c9394e5-p021-b002"></a>
<!-- pdf-source: page=21; block=2; confidence=0.85 -->
**Proof.** Assume $f$ nonconstant. If $\widetilde{I}[f]=I[f]/\mathrm{Var}[f]\ge .1\log n$, done: total influence $\ge .1\,\mathrm{Var}[f]\log n$, so $\mathrm{MaxInf}[f]\ge .1\,\mathrm{Var}[f]\cdot\tfrac{\log n}{n}$. Otherwise the edge-isoperimetric theorem gives
$$\mathrm{MaxInf}[f]\ge \Omega\!\big(\tfrac{1}{\log^2 n}\big)\cdot 9^{-.1\log n}=\Omega(n^{-.1\log 9})=\Omega(n^{-.317})\gg \mathrm{Var}[f]\cdot\Omega\!\big(\tfrac{\log n}{n}\big). \quad\square$$
(Constant factors treated in Exercise 9.30.)

<a id="pdf-4ba63c9394e5-p021-b003"></a>
<!-- pdf-source: page=21; block=3; confidence=0.83 -->
Contrapositive: if all influences are small, total influence must be large. Each derivative $D_if$ is $\{-1,0,1\}$-valued, nonzero on a small set; small-set expansion forces large noise sensitivity of $D_if$ (restating Corollary 9.12), so the Fourier weight of $f$ on coefficients containing $i$ sits high up. Holding for all $i$, all Fourier weight is high up, so $I[f]$ is large.

<a id="pdf-4ba63c9394e5-p021-b004"></a>
<!-- pdf-source: page=21; block=4; confidence=0.92 -->
**Proof.** Only the unbiased case is shown (general case: Exercise 9.29; product-space version in Chapter 10.3). It follows from the chain
$$3\cdot 3^{-I[f]} \overset{(a)}{\le} 3\,\mathrm{Stab}_{1/3}[f] \overset{(b)}{\le} I^{(1/3)}[f] \overset{(c)}{\le} \sum_{i=1}^n \mathrm{Inf}_i[f]^{3/2} \overset{(d)}{\le} \mathrm{MaxInf}[f]^{1/2}\cdot I[f].$$
Key step (c) is Corollary 9.12 summed over all coordinates $i\in[n]$; step (d) is immediate from $\mathrm{Inf}_i[f]^{3/2}\le \mathrm{MaxInf}[f]^{1/2}\cdot\mathrm{Inf}_i[f]$ summed over $i$.

<a id="pdf-4ba63c9394e5-p022-b001"></a>
<!-- pdf-source: page=22; block=1; confidence=0.93 -->
**Proof (concluded).** *Inequality (b)* is trivial from the Fourier formulas (recall Fact 2.53):
$$I^{(1/3)}[f]=\sum_{|S|\ge 1}|S|(1/3)^{|S|-1}\hat f(S)^2 \ge 3\sum_{|S|\ge 1}(1/3)^{|S|}\hat f(S)^2 = 3\,\mathrm{Stab}_{1/3}[f]$$
(the last equality using $\hat f(\emptyset)=0$). Finally, *inequality (a)* is quickly proved using the spectral sample: for $S\sim\mathscr{S}_f$,
$$3\,\mathrm{Stab}_{1/3}[f]=3\sum_{S\subseteq[n]}(1/3)^{|S|}\hat f(S)^2 = 3\,\mathbb{E}[3^{-|S|}]\ge 3\cdot 3^{-\mathbb{E}[|S|]}=3\cdot 3^{-I[f]},\tag{9.15}$$
the inequality following from convexity (Jensen) of $s\mapsto 3^{-s}$ and $\mathbb{E}[|S|]=I[f]$. $\square$

<a id="pdf-4ba63c9394e5-p022-b002"></a>
<!-- pdf-source: page=22; block=2; confidence=0.85 -->
Motivational lead-in: a stronger form of the KKL Edge-Isoperimetric Theorem is derived, from which Friedgut's Junta Theorem (Ch. 3.1) follows. KKL says an unbiased $f$ with $I[f]\le K$ has a coordinate of influence $\ge 2^{-O(K)}$; Friedgut strengthens this to $f$ being essentially a $2^{O(K)}$-junta, obtained by summing Corollary 9.12 over the low-influence coordinates. Stronger conclusions hold under good low-degree Fourier concentration.

<a id="pdf-4ba63c9394e5-p022-b003"></a>
<!-- pdf-source: page=22; block=3; confidence=0.90 -->
**Theorem 9.28.** Let $f:\{-1,1\}^n\to\{-1,1\}$. For $0<\epsilon\le 1$ and $k\ge 0$, define $\tau=\dfrac{\epsilon^2}{I[f]^2}\,9^{-k}$ and $J=\{j\in[n]:\mathrm{Inf}_j[f]\ge\tau\}$, so $|J|\le (I[f]^3/\epsilon^2)\,9^k$. Then $f$'s Fourier spectrum is $\epsilon$-concentrated on $\mathcal{F}=\{S:S\subseteq J\}\cup\{S:|S|>k\}$.

In particular, if $f$'s spectrum is also $\epsilon$-concentrated on degree up to $k$, then it is $2\epsilon$-concentrated on $\mathcal{F}'=\{S:S\subseteq J,\ |S|\le k\}$, and $f$ is $\epsilon$-close to a $|J|$-junta $h:\{-1,1\}^J\to\{-1,1\}$.

<a id="pdf-4ba63c9394e5-p022-b004"></a>
<!-- pdf-source: page=22; block=4; confidence=0.86 -->
**Proof.** Summing Corollary 9.12 over $i\notin J$: $\sum_{i\notin J}\mathrm{Inf}_i^{(1/3)}[f]\le\sum_{i\notin J}\mathrm{Inf}_i[f]^{3/2}\le\big(\max_{i\notin J}\mathrm{Inf}_i[f]^{1/2}\big)\sum_{i\notin J}\mathrm{Inf}_i[f]\le\tau^{1/2}\cdot I[f]\le 3^{-k}\epsilon$, using the definitions of $J$ and $\tau$.

<a id="pdf-4ba63c9394e5-p023-b001"></a>
<!-- pdf-source: page=23; block=1; confidence=0.82 -->
**Proof (concluded).** Conversely, $\sum_{i\notin J}\mathrm{Inf}_i^{(1/3)}[f]=\sum_{i\notin J}\sum_{S\ni i}3^{1-|S|}\hat f(S)^2=\sum_S |S\cap\bar J|\,3^{1-|S|}\hat f(S)^2\ge\sum_{S\notin\mathcal F}3^{1-|S|}\hat f(S)^2\ge 3^{-k}\sum_{S\notin\mathcal F}\hat f(S)^2$, since $S\notin\mathcal F$ implies $|S\cap\bar J|\ge 1$ and $|S|\le k$ so $3^{1-|S|}\ge 3^{-k}$. Combining the two bounds gives $\sum_{S\notin\mathcal F}\hat f(S)^2\le\epsilon$. For the second part, when the spectrum is $2\epsilon$-concentrated on $\mathcal F'$, Proposition 3.31 gives $f$ is $2\epsilon$-close to the Boolean $|J|$-junta $\mathrm{sgn}(f^{\subseteq J})$, and Exercise 3.34 upgrades this to $\epsilon$-close to some $h:\{-1,1\}^J\to\{-1,1\}$. $\square$

<a id="pdf-4ba63c9394e5-p023-b002"></a>
<!-- pdf-source: page=23; block=2; confidence=0.90 -->
**Remark 9.29.** As you are asked to show in Exercise 9.31, by using Corollary 9.25 in place of Corollary 9.12, we can achieve junta size $\big(I[f]^{2+\eta}/\epsilon^{1+\eta}\big)\cdot C(\eta)^{k}$ in Theorem 9.28 for any $\eta>0$, where $C(\eta)=(2/\eta+1)^2$.

<a id="pdf-4ba63c9394e5-p023-b003"></a>
<!-- pdf-source: page=23; block=3; confidence=0.90 -->
In Theorem 9.28 one may always take $k=I[f]/\epsilon$ (by the Markov argument, Proposition 3.2), giving:

**Friedgut's Junta Theorem.** Let $f:\{-1,1\}^n\to\{-1,1\}$ and $0<\epsilon\le 1$. Then $f$ is $\epsilon$-close to an $\exp(O(I[f]/\epsilon))$-junta. Indeed there is $J\subseteq[n]$ with $|J|\le\exp(O(I[f]/\epsilon))$ such that $f$'s Fourier spectrum is $2\epsilon$-concentrated on $\{S\subseteq J:|S|\le I[f]/\epsilon\}$.

<a id="pdf-4ba63c9394e5-p023-b004"></a>
<!-- pdf-source: page=23; block=4; confidence=0.90 -->
Stronger results hold when $f$ is $\epsilon$-concentrated up to degree $\ll I[f]/\epsilon$; e.g. width-$w$ DNFs are $\epsilon$-concentrated on degree up to $O(w\log(1/\epsilon))$ (Theorem 4.22). Hence:

**Corollary 9.30.** Any width-$w$ DNF is $\epsilon$-close to a $(1/\epsilon)^{O(w)}$-junta.

<a id="pdf-4ba63c9394e5-p023-b005"></a>
<!-- pdf-source: page=23; block=5; confidence=0.95 -->
Linear threshold functions are $\epsilon$-concentrated up to degree $O(1/\epsilon^2)$ (Peres's Theorem), so with Theorem 9.28 and Remark 9.29:

**Corollary 9.31.** Let $f:\{-1,1\}^n\to\{-1,1\}$ be a linear threshold function and $0<\epsilon,\eta\le 1/2$. Then $f$ is $\epsilon$-close to a junta on $I[f]^{2+\eta}\cdot(1/\eta)^{O(1/\epsilon^2)}$ coordinates. For $\epsilon$ a small universal constant, taking $\eta=1/\log(O(I[f]))$ shows every LTF is $\epsilon$-close to a junta on $I[f]^2\cdot\mathrm{polylog}(I[f])$ coordinates.

<a id="pdf-4ba63c9394e5-p023-b006"></a>
<!-- pdf-source: page=23; block=6; confidence=0.88 -->
This is essentially best possible: $I[\mathrm{Maj}_n]=\Theta(\sqrt{n})$, yet $\mathrm{Maj}_n$ is not $.1$-close to any $o(n)$-junta. Via Theorem 5.37 (uniform noise stability of PTFs), the same conclusion holds for any constant-degree PTF.

<a id="pdf-4ba63c9394e5-p024-b001"></a>
<!-- pdf-source: page=24; block=1; confidence=0.90 -->
**Corollary 9.32.** Assume $f:\{-1,1\}^n\to\{-1,1\}$ satisfies $\mathrm{Var}[f]\ge 1/2$. Then there exists $S\subseteq[n]$ with $0<|S|\le O(I[f])$ such that $\hat f(S)^2\ge\exp(-O(I[f]^2))$.

<a id="pdf-4ba63c9394e5-p024-b002"></a>
<!-- pdf-source: page=24; block=2; confidence=0.85 -->
**Proof.** Take $\epsilon=1/8$ in Friedgut's Junta Theorem to get $J$ with $|J|\le\exp(O(I[f]))$ such that $f$ has Fourier weight $\ge 1-2\epsilon=3/4$ on $\mathcal F=\{S\subseteq J:|S|\le 8I[f]\}$. Since $\mathrm{Var}[f]\ge 1/2$ (so the $\emptyset$-term contributes $\le 1/2$), $f$ has weight $\ge 1/4$ on $\mathcal F'=\mathcal F\setminus\{\emptyset\}$. As $|\mathcal F'|\le|\mathcal F|\le\exp(O(I[f]^2))$, Pigeonhole gives the claim (using $(1/4)\exp(-O(I[f]^2))=\exp(-O(I[f]^2))$ since $I[f]\ge\mathrm{Var}[f]\ge 1/2$). $\square$

<a id="pdf-4ba63c9394e5-p024-b003"></a>
<!-- pdf-source: page=24; block=3; confidence=0.85 -->
**Remark 9.33.** If $\mathrm{Var}[f]<1/2$ then $\hat f(\emptyset)^2\ge 1/2$ is a large empty coefficient; for a refined version of Corollary 9.32 see Exercise 9.32. It is open whether Corollary 9.32 can be improved to a coefficient with $\hat f(S)^2\ge\exp(-O(I[f]))$ (see Exercise 9.33).

<a id="pdf-4ba63c9394e5-p024-b004"></a>
<!-- pdf-source: page=24; block=4; confidence=0.95 -->
## 9.7. Exercises and notes

<a id="pdf-4ba63c9394e5-p024-b005"></a>
<!-- pdf-source: page=24; block=5; confidence=0.94 -->
**Exercise 9.1.** For every $1<b<B$, show there is a $b$-reasonable random variable $X$ such that $1+X$ is not $B$-reasonable.

<a id="pdf-4ba63c9394e5-p024-b006"></a>
<!-- pdf-source: page=24; block=6; confidence=0.85 -->
**Exercise 9.2.** For $k=1$, improve the constant $9$ in the Bonami Lemma to $3$: suppose $f:\{-1,1\}^n\to\mathbb R$ has degree $\le 1$ and $x_1,\dots,x_n$ are independent $3$-reasonable random variables with $\mathbb E[x_i]=\mathbb E[x_i^3]=0$ (e.g. uniform $\pm 1$ bits). Show $f(x)$ is also $3$-reasonable. (Hint: direct computation, or run the Bonami Lemma proof at $k=1$ more carefully.)

<a id="pdf-4ba63c9394e5-p024-b007"></a>
<!-- pdf-source: page=24; block=7; confidence=0.92 -->
**Exercise 9.3.** Let $k$ be a positive multiple of $3$ and $n\ge 2k$. Define $f:\{-1,1\}^n\to\mathbb R$ by $f(x)=\sum_{S\subseteq[n],\,|S|=k}x^S$.

(a) Show that $\mathbb E[f^4]\ge\dfrac{\binom{n}{k/3,k/3,k/3,k/3,k/3,k/3,\,n-2k}}{\binom{n}{k}^2}\,\mathbb E[f^2]^2$, where the numerator is the multinomial coefficient counting the number of ways of choosing six disjoint size-$k/3$ subsets of $[n]$. (Hint: given such subsets, consider quadruples of size-$k$ subsets that hit each size-$k/3$ subset twice.)

<a id="pdf-4ba63c9394e5-p025-b001"></a>
<!-- pdf-source: page=25; block=1; confidence=0.85 -->
## 9.7. Exercises and notes

<a id="pdf-4ba63c9394e5-p025-b002"></a>
<!-- pdf-source: page=25; block=2; confidence=0.90 -->
**Exercise 9.3 (continued), part (b).** Using Stirling's Formula, show that
$$\lim_{n\to\infty}\frac{\binom{n}{k/3,\,k/3,\,k/3,\,k/3,\,k/3,\,k/3,\,n-2k}}{\binom{n}{k}^2}=\Theta(k^{-2}\,9^k).$$
Deduce the following lower bound for the Bonami Lemma: $\lVert f\rVert_4 \ge \Omega(k^{-1/2})\,\sqrt{3}^{\,k}\,\lVert f\rVert_2$. (In fact $\lVert f\rVert_4 = \Theta(k^{-1/4})\,\sqrt{3}^{\,k}\,\lVert f\rVert_2$, and such an upper bound holds for all $f$ homogeneous of degree $k$; see Exercise 9.38(f).)

<a id="pdf-4ba63c9394e5-p025-b003"></a>
<!-- pdf-source: page=25; block=3; confidence=0.90 -->
**Exercise 9.4.** Prove Corollary 9.6.

<a id="pdf-4ba63c9394e5-p025-b004"></a>
<!-- pdf-source: page=25; block=4; confidence=0.93 -->
**Exercise 9.5.** Let $0\le\delta\le\tfrac{1}{1600}$ and let $f,\ell$ be real numbers satisfying $|\ell^2-1|>39\sqrt{\delta}$ and $|f|=1$. Show that $|f-\ell|^2\ge 169\delta$. (This is a loose estimate; stronger ones are possible.)

<a id="pdf-4ba63c9394e5-p025-b005"></a>
<!-- pdf-source: page=25; block=5; confidence=0.92 -->
**Exercise 9.6.** (Reverse of Theorem 9.21: derive the (2,4)-Hypercontractivity Theorem from the Bonami Lemma.)
- **(a)** For $f:\{-1,1\}^n\to\mathbb{R}$ and fixed $\delta\in(0,1)$, use the Bonami Lemma to show $\big\lVert T_{(1-\delta)/\sqrt{3}}\,f\big\rVert_4 \le \sum_{k=0}^{\infty}(1-\delta)^k\lVert f^{=k}\rVert_2 \le \tfrac{1}{\delta}\lVert f\rVert_2$.
- **(b)** For $g:\{-1,1\}^n\to\mathbb{R}$ and $d\in\mathbb{N}^+$, define $g^{\oplus d}:\{-1,1\}^{dn}\to\mathbb{R}$ by $g^{\oplus d}(x^{(1)},\dots,x^{(d)})=\prod_{i=1}^{d}g(x^{(i)})$. Show $\lVert T_\rho(g^{\oplus d})\rVert_p=\lVert T_\rho g\rVert_p^{\,d}$ for every $p\in\mathbb{R}^+$ and $\rho\in[-1,1]$ (special case $\rho=1$: $\lVert g^{\oplus d}\rVert_p=\lVert g\rVert_p^{\,d}$).
- **(c)** From (a),(b) deduce $\big\lVert T_{(1-\delta)/\sqrt{3}}\,f\big\rVert_4\le\lVert f\rVert_2$ (Hint: apply (a) to $f^{\oplus d}$ for $d\to\infty$).
- **(d)** Deduce $\big\lVert T_{1/\sqrt{3}}\,f\big\rVert_4\le\lVert f\rVert_2$, i.e. the (2,4)-Hypercontractivity Theorem, by taking $\delta\to0^+$.

<a id="pdf-4ba63c9394e5-p025-b006"></a>
<!-- pdf-source: page=25; block=6; confidence=0.75 -->
**Exercise 9.7.** To prove $\lVert T_\rho f\rVert_q\le\lVert f\rVert_p$ for all $f:\{-1,1\}^n\to\mathbb{R}$, show it suffices to prove it for all nonnegative $f$. (Hint: Exercise 2.34.)

<a id="pdf-4ba63c9394e5-p025-b007"></a>
<!-- pdf-source: page=25; block=7; confidence=0.60 -->
**Exercise 9.8.** Fix $k\in\mathbb{N}$; goal: show “projection to degree $\le k-1$” is a bounded operator in all $L^p$ norms, $p>1$. Let $f:\{-1,1\}^n\to\mathbb{R}$.
- **(a)** For $q\ge 2$, show $\lVert f^{\le k-1}\rVert_q\le(\sqrt{q-1})^k\lVert f\rVert_q$. (Hint: use Theorem 9.21 to prove the stronger $\lVert f^{\le k-1}\rVert_q\le(\sqrt{q-1})^k\lVert f\rVert_2$.)
- **(b)** For $1<q<2$, show $\lVert f^{\le k-1}\rVert_q\le(1/\sqrt{q-1})^k\lVert f\rVert_q$. (Hint: either give a direct proof via the (p,2)-Hypercontractivity Theorem, or derive it from (a) using the dual-norm Proposition 9.19.)

<a id="pdf-4ba63c9394e5-p025-b008"></a>
<!-- pdf-source: page=25; block=8; confidence=0.70 -->
**Exercise 9.9.** Let $X$ be $(p,q,\rho)$-hypercontractive. [Parts (a)–(b) continue on the next page.]

<a id="pdf-4ba63c9394e5-p026-b001"></a>
<!-- pdf-source: page=26; block=1; confidence=0.85 -->
## 9. Basics of hypercontractivity

<a id="pdf-4ba63c9394e5-p026-b002"></a>
<!-- pdf-source: page=26; block=2; confidence=0.93 -->
**Exercise 9.9 (cont.).** Let $X$ be $(p,q,\rho)$-hypercontractive.
- **(a)** Show $cX$ is $(p,q,\rho)$-hypercontractive for any $c\in\mathbb{R}$.
- **(b)** Show $\rho\le\lVert X\rVert_p/\lVert X\rVert_q$.

<a id="pdf-4ba63c9394e5-p026-b003"></a>
<!-- pdf-source: page=26; block=3; confidence=0.60 -->
**Exercise 9.10.** Let $X$ be $(p,q,\rho)$-hypercontractive (you may assume $X$ discrete).
- **(a)** Show $\mathbb{E}[X]=0$. (Hint: Taylor-expand a norm term such as $\lVert 1+\rho\varepsilon X\rVert_q$ around $\varepsilon=0$; note $\rho\le1$ by definition.)
- **(b)** Show $\rho\le\sqrt{(p-1)/(q-1)}$. (Hint: Taylor-expand to two terms around $\varepsilon=0$.)

<a id="pdf-4ba63c9394e5-p026-b004"></a>
<!-- pdf-source: page=26; block=4; confidence=0.70 -->
**Exercise 9.11.**
- **(a)** Suppose $\mathbb{E}[X]=0$. Show $X$ is $(q,q,0)$-hypercontractive for all $q\ge1$. (Hint: use monotonicity of norms to reduce to the case $q=1$.)
- **(b)** Show further that $X$ is $(q,q,\rho)$-hypercontractive for all $0\le\rho\le1$. (Hint: write $a+\rho X=(1-\rho)a+\rho(a+X)$ and use the triangle inequality for $\lVert\cdot\rVert_q$.)
- **(c)** Show that if $X$ is $(p,q,\rho)$-hypercontractive, it is also $(p,q,\rho')$-hypercontractive for all $0\le\rho'<\rho$. (Hint: previous exercise together with Exercise 9.10(a).)

<a id="pdf-4ba63c9394e5-p026-b005"></a>
<!-- pdf-source: page=26; block=5; confidence=0.75 -->
**Exercise 9.12.** Let $X$ be a nonconstant $(2,4,\rho)$-hypercontractive random variable. Goal (anticoncentration): for all $\theta\in\mathbb{R}$ and $0<t<1$,
$$\Pr\big[\,|X-\theta|>t\lVert X\rVert_2\,\big]\ge(1-t^2)^2\rho^4.$$
- **(a)** Reduce to the case $\lVert X\rVert_2=1$.
- **(b)** With $Y=(X-\theta)^2$, show $\mathbb{E}[Y]=1+\theta^2$ and $\mathbb{E}[Y^2]\le(\rho^{-2}+\theta^2)^2$.
- **(c)** Using the Paley–Zygmund inequality, show $\Pr[\,|X-\theta|>t\,]\ge\left(\dfrac{\rho^2(1-t^2)+\rho^2\theta^2}{1+\rho^2\theta^2}\right)^2$.
- **(d)** Show the right-hand side is minimized at $\theta=0$, completing the proof.

<a id="pdf-4ba63c9394e5-p026-b006"></a>
<!-- pdf-source: page=26; block=6; confidence=0.93 -->
**Exercise 9.13.** Let $m\in\mathbb{N}^+$ and let $f:\{-1,1\}^n\to[m]$ be “unbiased,” i.e. $\Pr[f(x)=i]=1/m$ for all $i\in[m]$. Let $0\le\rho\le1$ and let $(x,y)$ be a $\rho$-correlated pair. Show that $\Pr[f(x)=f(y)]\le(1/m)^{(1-\rho)/(1+\rho)}$. More generally, this upper-bounds $\mathrm{Stab}_\rho[f]$ for all $f:\{-1,1\}^n\to\triangle_m$ with $\mathbb{E}[f]=(1/m,\dots,1/m)$; cf. Exercise 8.33.

<a id="pdf-4ba63c9394e5-p026-b007"></a>
<!-- pdf-source: page=26; block=7; confidence=0.92 -->
**Exercise 9.14.**
- **(a)** Let $f:\{-1,1\}^n\to\mathbb{R}$ with $\deg(f)\le k$. Prove $\lVert f\rVert_2\le\big(1/\sqrt{p-1}\big)^k\lVert f\rVert_p$ for any $1\le p\le 2$, using the Hölder-inequality strategy from the proof of the (4/3,2)-Hypercontractivity Theorem together with Theorem 9.21.
- **(b)** Verify that $\exp(2/p-1)<1/\sqrt{p-1}$ for all $1\le p<2$; i.e., the trickier Theorem 9.22 strictly improves on the bound from part (a).

<a id="pdf-4ba63c9394e5-p027-b001"></a>
<!-- pdf-source: page=27; block=1; confidence=0.85 -->
## 9.7. Exercises and notes

<a id="pdf-4ba63c9394e5-p027-b002"></a>
<!-- pdf-source: page=27; block=2; confidence=0.90 -->
**Exercise 9.15.** Prove Theorem 9.22 in full generality. (Hint: let $\theta$ be the solution of $\tfrac12=\tfrac{\theta}{p}+\tfrac{1-\theta}{2+\varepsilon}$. You will need to show that $\tfrac{1-\theta}{2\theta}=\big(\tfrac2p-1\big)\tfrac1\varepsilon+\big(\tfrac1p-\tfrac12\big)$.)

<a id="pdf-4ba63c9394e5-p027-b003"></a>
<!-- pdf-source: page=27; block=3; confidence=0.88 -->
**Exercise 9.16.** As mentioned, it's possible to deduce the (2,q)-Hypercontractivity Theorem from the $n=1$ case by induction by derivatives; from this one also obtains the (p,2)-Hypercontractivity Theorem via Proposition 9.19. With notation $x=(x',x_n)$, $T=T_{1/\sqrt{q-1}}$, $d=\mathrm{D}_n f(x')$, and $e=\mathrm{E}_n f(x')$, fill in details and justifications for the proof sketch
$$\lVert T_{1/\sqrt{q-1}}f\rVert_q^2=\mathbb{E}_{x'}\Big[\mathbb{E}_{x_n}\big[\,|Te+\tfrac{1}{\sqrt{q-1}}x_n\,Td|^{q}\,\big]\Big]^{2/q}\le\mathbb{E}_{x'}\big[((Te)^2+(Td)^2)^{q/2}\big]^{2/q}=\big\lVert (Te)^2+(Td)^2\big\rVert_{q/2}\le\lVert (Te)^2\rVert_{q/2}+\lVert (Td)^2\rVert_{q/2}=\lVert Te\rVert_q^2+\lVert Td\rVert_q^2\le\lVert e\rVert_2^2+\lVert d\rVert_2^2=\lVert f\rVert_2^2.$$

<a id="pdf-4ba63c9394e5-p027-b004"></a>
<!-- pdf-source: page=27; block=4; confidence=0.70 -->
**Exercise 9.17.** Deduce the $p<2<q$ cases of the Hypercontractivity Theorem from the (2,q)- and (p,2)-Hypercontractivity Theorems. (Hint: use the semigroup property of $T_\rho$, Exercise 2.32.)

<a id="pdf-4ba63c9394e5-p027-b005"></a>
<!-- pdf-source: page=27; block=5; confidence=0.93 -->
**Exercise 9.18.** Let $f:\{-1,1\}^n\to\{0,1\}$ have $\mathbb{E}[f]=\alpha$.
- **(a)** Show $\mathbf{W}^{1}[f]\le\tfrac{1}{\rho}\big(\alpha^{2/(1+\rho)}-\alpha^2\big)$ for any $0<\rho\le1$.
- **(b)** Deduce the sharp Level-1 Inequality $\mathbf{W}^{1}[f]\le 2\alpha^2\ln(1/\alpha)$. (Hint: take the limit $\rho\to0^+$.)

<a id="pdf-4ba63c9394e5-p027-b006"></a>
<!-- pdf-source: page=27; block=6; confidence=0.80 -->
**Exercise 9.19.** For $f:\{-1,1\}^n\to\{0,1\}$ with $\mathbb{E}[f]=\alpha$, show $\mathbf{W}^{\le k}[f]=o(\alpha)$ (as $\alpha\to0$) provided $k\le .373\,\ln(1/\alpha)$.

<a id="pdf-4ba63c9394e5-p027-b007"></a>
<!-- pdf-source: page=27; block=7; confidence=0.70 -->
**Exercise 9.20.** Show that the KKL Theorem fails for functions $f:\{-1,1\}^n\to[-1,1]$, even under the assumption $\mathrm{Var}[f]=\Omega(1)$. (Hint: $f(x)=\mathrm{trunc}_{[-1,1]}\big((x_1+\cdots+x_n)/\sqrt{n}\big)$.)

<a id="pdf-4ba63c9394e5-p027-b008"></a>
<!-- pdf-source: page=27; block=8; confidence=0.80 -->
**Exercise 9.21.**
- **(a)** Show $\mathcal{C}=\{f:\{-1,1\}^n\to\{-1,1\}: \mathbf{I}[f]\le O(\sqrt{\log n})\}$ is learnable from queries to any constant error $\varepsilon>0$ in time $\mathrm{poly}(n)$. (Hint: Theorem 9.28.)
- **(b)** Show $\mathcal{C}=\{\text{monotone }f:\{-1,1\}^n\to\{-1,1\}: \mathbf{I}[f]\le O(\sqrt{\log n})\}$ is learnable from random examples to any constant error $\varepsilon>0$ in time $\mathrm{poly}(n)$.
- **(c)** Show $\mathcal{C}=\{\text{monotone }f:\{-1,1\}^n\to\{-1,1\}: \mathrm{DTsize}(f)\le\mathrm{poly}(n)\}$ is learnable from random examples to any constant error $\varepsilon>0$ in time $\mathrm{poly}(n)$. (Hint: the OS Inequality and Exercise 8.43.)

<a id="pdf-4ba63c9394e5-p027-b009"></a>
<!-- pdf-source: page=27; block=9; confidence=0.90 -->
**Exercise 9.22.** Deduce this generalization of the (2,q)-Hypercontractivity Theorem: let $f:\{-1,1\}^n\to\mathbb{R}$, $q\ge2$, and assume $0\le\rho\le1$ satisfies $\rho^{\lambda}\le 1/\sqrt{q-1}$ for some $0\le\lambda\le1$. Then
$$\lVert T_\rho f\rVert_q\le\lVert T_\rho f\rVert_2^{\,1-\lambda}\cdot\lVert f\rVert_2^{\lambda}.$$
(Hint: show $\lVert T_\rho f\rVert_q^2\le\textstyle\sum_S (\rho^{2|S|}\hat f(S)^2)^{1-\lambda}(\hat f(S)^2)^{\lambda}$ and apply Hölder.)

<a id="pdf-4ba63c9394e5-p027-b010"></a>
<!-- pdf-source: page=27; block=10; confidence=0.90 -->
**Exercise 9.23.** Let $f:\{-1,1\}^n\to[-1,1]$, let $0\le\varepsilon\le1$, and assume $q\ge2+2\varepsilon$. Show that
$$\lVert T_{1-\varepsilon}f\rVert_q^q\le\big\lVert T_{1/\sqrt{1+2\varepsilon}}f\big\rVert_q^q\le\big(\lVert f\rVert_2^2\big)^{1+\varepsilon}.$$

<a id="pdf-4ba63c9394e5-p028-b001"></a>
<!-- pdf-source: page=28; block=1; confidence=0.90 -->
**§9.7. Exercises and notes.** Exercise set for Chapter 9 (Basics of hypercontractivity), covering Exercises 9.24–9.34.

<a id="pdf-4ba63c9394e5-p028-b002"></a>
<!-- pdf-source: page=28; block=2; confidence=0.86 -->
**Exercise 9.24.** For fixed $0<\rho<1$, show the Gaussian quadrant probability $\Lambda_\rho(\mu)=\Pr[z_1>t,\,z_2>t]$ (from Exercise 5.32; $z_1,z_2$ standard Gaussians with correlation $\mathbf E[z_1z_2]=\rho$, and $t$ defined by $\Pr[z_1>t]=\mu$) satisfies $\Lambda_\rho(\mu)=\widetilde\Theta\!\big(\mu^{2/(1+\rho)}\big)$ as $\mu\to0$ (eq. 9.16), showing the Small-Set Expansion Theorem for the $\rho$-stable hypercube is essentially sharp via Hamming balls of volume $\mu$.

(a) *Heuristic:* since $\Pr[z_1>t]=\mu$ and a Gaussian conditioned to be $\ge t$ is unlikely to exceed $t$ much, pretend $z_1=t$; then $z_2\mid z_1=t$ is distributed as $\rho t+\sqrt{1-\rho^2}\,y$ with $y\sim N(0,1)$ independent. Using $\overline\Phi(u)\sim\varphi(u)/u$ as $u\to\infty$, deduce $\Pr[z_2>t\mid z_1=t]=\widetilde\Theta\!\big(\mu^{(1-\rho)/(1+\rho)}\big)$, and "hence" (9.16).

(b) *Rigorous* (with $\rho$ fixed, $\mu\to0$, $t\to\infty$): let $\varphi_\rho(z_1,z_2)$ be the joint pdf, so $\Lambda_\rho(\mu)=\int_t^\infty\!\int_t^\infty\varphi_\rho\,dz_1dz_2$. Derive (9.17): $\int_t^\infty\!\int_t^\infty (z_2-\rho z_1)(z_1-\rho t)\varphi_\rho(z_1,z_2)\,dz_1dz_2=\frac{(1-\rho^2)^{3/2}}{2\pi}\exp\!\big(-\tfrac{2}{1+\rho}\cdot\tfrac{t^2}{2}\big)$, and show the RHS is $\widetilde\Theta\!\big(\mu^{2/(1+\rho)}\big)$.

(c) Show $\Pr\!\big[z_1>\tfrac{t-1}{\rho}\big]=\int_{(t-1)/\rho}^\infty\varphi(z_1)\,dz_1=\widetilde\Theta\!\big(\mu^{1/\rho^2}\big)$, asymptotically smaller than $\widetilde\Theta(\mu^{2/(1+\rho)})$.

(d) Deduce (9.16). Hint: arrange the extraneous factors $(z_2-\rho z_1),(z_1-\rho t)$ in (9.17) to both be $\ge1$.

<a id="pdf-4ba63c9394e5-p028-b003"></a>
<!-- pdf-source: page=28; block=3; confidence=0.82 -->
**Exercise 9.25.** For $f:\{-1,1\}^n\to\{-1,1\}$, $J\subseteq[n]$, and $\bar J=[n]\setminus J$, define the *coalitional influence* of $J$ on $f$ by $\widetilde{\mathrm{Inf}}_J[f]=\Pr_{z\sim\{-1,1\}^{\bar J}}\big[\,f_{J|z}\text{ is not constant}\,\big]$ (fix the coordinates outside $J$ to a uniform random $z$; the probability the resulting restriction on the $J$-coordinates is non-constant). Continues on next page.

<a id="pdf-4ba63c9394e5-p029-b001"></a>
<!-- pdf-source: page=29; block=1; confidence=0.85 -->
**Exercise 9.25 (continued).** For $b\in\{-1,1\}$, the coalitional influence *toward $b$*: $\widetilde{\mathrm{Inf}}^b_J[f]=\Pr_{z\sim\{-1,1\}^{\bar J}}\big[f_{J|z}\text{ can be made }b\big]-\Pr[f=b]=\Pr_z\big[f_{J|z}\not\equiv -b\big]-\Pr[f=b]$; abbreviated $\widetilde{\mathrm{Inf}}^\pm_J[f]$.

(a) For $|J|=1$: $\mathrm{Inf}_i[f]=\widetilde{\mathrm{Inf}}_{\{i\}}[f]=2\widetilde{\mathrm{Inf}}^\pm_{\{i\}}[f]$.

(b) $0\le\widetilde{\mathrm{Inf}}^+_J[f]\le1$.

(c) $\widetilde{\mathrm{Inf}}_J[f]=\widetilde{\mathrm{Inf}}^+_J[f]+\widetilde{\mathrm{Inf}}^-_J[f]$.

(d) If $f$ is monotone, $\widetilde{\mathrm{Inf}}^b_J[f]=\Pr[f_{\bar J\mid(b,\dots,b)}=b]-\Pr[f=b]$.

(e) $\widetilde{\mathrm{Inf}}_J[\chi_{[n]}]=1$ for all $J\neq\emptyset$.

(f) With $t=|J|/\sqrt n$: $\widetilde{\mathrm{Inf}}^\pm_J[\mathrm{Maj}_n]=\Phi(t)-\tfrac12\pm o(1)$ and $\widetilde{\mathrm{Inf}}_J[\mathrm{Maj}_n]=2\Phi(t)-1\pm o(1)$; hence $\widetilde{\mathrm{Inf}}_J[\mathrm{Maj}_n]=o(1)$ if $|J|=o(\sqrt n)$ and $1-o(1)$ if $|J|=\omega(\sqrt n)$ (Hint: Central Limit Theorem).

(g) $\max\{\widetilde{\mathrm{Inf}}^{\mathrm{True}}_J[\mathrm{Tribes}_n]:|J|\le\log n\}=\tfrac12+\Theta\!\big(\tfrac{\log n}{n}\big)$; $\max\{\widetilde{\mathrm{Inf}}^{\mathrm{False}}_J[\mathrm{Tribes}_n]:|J|\le k\}\le k\cdot O\!\big(\tfrac{\log n}{n}\big)$; deduce $\exists\,c>0$ with $\max\{\widetilde{\mathrm{Inf}}_J[\mathrm{Tribes}_n]:|J|\le cn/\log n\}\le .51$ (Hint: Proposition 4.12).

<a id="pdf-4ba63c9394e5-p029-b002"></a>
<!-- pdf-source: page=29; block=2; confidence=0.90 -->
**Exercise 9.26.** Show the exponential dependence on $I[f]$ in Friedgut's Junta Theorem is necessary (Hint: Exercise 4.15).

<a id="pdf-4ba63c9394e5-p029-b003"></a>
<!-- pdf-source: page=29; block=3; confidence=0.60 -->
**Exercise 9.27.** Let $f:\{-1,1\}^n\to\{-1,1\}$ be a monotone function with $\mathrm{Var}[f]\ge\delta>0$, and let $0<\varepsilon<1/2$ be given.

(a) Improve Proposition 9.27: show there exists $J\subseteq[n]$ with $|J|\le O\!\big(\log\tfrac1{\varepsilon\delta}\big)\cdot\tfrac{n}{\log n}$ such that $\mathbf E[f_{\bar J\mid(1,\dots,1)}]\ge 1-\varepsilon$ (Hint: how many bribes are required to move $f$'s mean outside the interval $[1-2\eta,1-\eta]$?).

(b) Show there exists $J\subseteq[n]$ with $|J|\le O\!\big(\log\tfrac1{\varepsilon\delta}\big)\cdot\tfrac{n}{\log n}$ such that $\widetilde{\mathrm{Inf}}_J[f]\ge 1-\varepsilon$ (Hint: Exercise 9.25(d); take the union of two influential sets).

<a id="pdf-4ba63c9394e5-p029-b004"></a>
<!-- pdf-source: page=29; block=4; confidence=0.85 -->
**Exercise 9.28.** Let $f:\{-1,1\}^n\to\{-1,1\}$.

(a) Let $f^*$ be the monotonization of $f$ (Exercise 2.52). Show $\mathrm{Inf}^b_J[f^*]\le\mathrm{Inf}^b_J[f]$ for all $J\subseteq[n]$ and $b\in\{-1,1\}$, and hence $\mathrm{Inf}_J[f^*]\le\mathrm{Inf}_J[f]$.

<a id="pdf-4ba63c9394e5-p030-b001"></a>
<!-- pdf-source: page=30; block=1; confidence=0.75 -->
**Exercise 9.28 (continued).** (b) Given $\mathrm{Var}[f]>0$, $0<\varepsilon<1/2$, $\delta>0$: there exists $J\subseteq[n]$ with $|J|\le O\!\big(\log\tfrac1{\varepsilon\delta}\big)\cdot\tfrac{n}{\log n}$ such that $\mathrm{Inf}_J[f]\ge 1-\varepsilon^2$ (Hint: combine part (a) with Exercise 9.27(b)).

<a id="pdf-4ba63c9394e5-p030-b002"></a>
<!-- pdf-source: page=30; block=2; confidence=0.90 -->
**Exercise 9.29.** Establish the general-variance case of the KKL Edge-Isoperimetric Theorem. Hint: replace (9.15) with
$$3\sum_{|S|\ge1}(1/3)^{|S|}\,\hat f(S)^2\ge 3\,\mathrm{Var}[f]\cdot 3^{-I[f]/\mathrm{Var}[f]},$$
obtained by the same convexity (Jensen) argument applied to the random set $S$ that takes each outcome $\emptyset\ne S\subseteq[n]$ with probability $\hat f(S)^2/\mathrm{Var}[f]$.

<a id="pdf-4ba63c9394e5-p030-b003"></a>
<!-- pdf-source: page=30; block=3; confidence=0.75 -->
**Exercise 9.30.** Goal: best known constant factor in the KKL Theorem. Write $\tilde I[f]=I[f]/\mathrm{Var}[f]$.

(a) Using Corollary 9.25 in place of Corollary 9.12, generalize the KKL edge-isoperimetric theorem: for nonconstant $f:\{-1,1\}^n\to\{-1,1\}$ and $0<\delta<1$,
$$\mathrm{MaxInf}[f]\ge\Big(\tfrac{1+\delta}{1-\delta}\Big)^{1/\delta}\Big(\tfrac{1}{I[f]}\Big)^{1/\delta}\cdot\Big(\tfrac{1-\delta}{1+\delta}\Big)^{\frac1\delta\tilde I[f]}$$
(Hint: set $\rho=\tfrac{1-\delta}{1+\delta}$). Deduce $\mathrm{MaxInf}[f]\ge\widetilde\Omega\!\big(C^{-\tilde I[f]}\big)$ for any constant $C>e^2$.

(b) More carefully, taking $\delta=\tfrac{1}{2\tilde I[f]^{1/3}}$ gives
$$\mathrm{MaxInf}[f]\ge \exp(-2\tilde I[f])\cdot e^2\cdot\Big(\tfrac{1}{I[f]}\Big)^{2\tilde I[f]^{1/3}}\cdot\exp\!\big(-\tfrac14\tilde I[f]^{1/3}\big)$$
(Hint: establish $\big(\tfrac{1-\delta}{1+\delta}\big)^{1/\delta}\ge\exp(-2-\delta^2)$ for $0<\delta\le1/2$).

(c) By distinguishing whether or not $\tilde I[f]\ge\tfrac12(\ln n-\sqrt{\log n})$, establish the KKL Theorem form: for any $f:\{-1,1\}^n\to\{-1,1\}$, $\mathrm{MaxInf}[f]\ge\tfrac12\mathrm{Var}[f]\cdot\tfrac{\ln n}{n}\cdot(1-o_n(1))$.

<a id="pdf-4ba63c9394e5-p030-b004"></a>
<!-- pdf-source: page=30; block=4; confidence=0.90 -->
**Exercise 9.31.** Establish the claim in Remark 9.29.

<a id="pdf-4ba63c9394e5-p030-b005"></a>
<!-- pdf-source: page=30; block=5; confidence=0.85 -->
**Exercise 9.32.** For nonconstant $f:\{-1,1\}^n\to\{-1,1\}$, show there exists $S\subseteq[n]$ with $0<|S|\le O(I[f]/\mathrm{Var}[f])$ such that $\hat f(S)^2\ge\exp\!\big(-O(I[f]^2/\mathrm{Var}[f]^2)\big)$. Hint: mimic Corollary 9.32's proof for the lower bound $\Omega(\mathrm{Var}[f])\cdot\exp(-O(I[f]^2/\mathrm{Var}[f]^2))$; to show this is also $\exp(-O(I[f]^2/\mathrm{Var}[f]^2))$, use Theorem 2.39.

<a id="pdf-4ba63c9394e5-p030-b006"></a>
<!-- pdf-source: page=30; block=6; confidence=0.80 -->
**Exercise 9.33.** For nonconstant monotone $f:\{-1,1\}^n\to\{-1,1\}$, improve Corollary 9.32: there exists $\emptyset\ne S$ with $|S|\le O(I[f]/\mathrm{Var}[f])$ and $\hat f(S)^2\ge\exp\!\big(-O(I[f]/\mathrm{Var}[f])\big)$. Hint: use the KKL Edge-Isoperimetric Theorem and Proposition 2.21.

<a id="pdf-4ba63c9394e5-p030-b007"></a>
<!-- pdf-source: page=30; block=7; confidence=0.95 -->
**Exercise 9.34.** For $f:\{-1,1\}^n\to\mathbb R$, prove $\|f\|_4\le\mathrm{sparsity}(\hat f)^{1/4}\,\|f\|_2$.

<a id="pdf-4ba63c9394e5-p031-b001"></a>
<!-- pdf-source: page=31; block=1; confidence=1.00 -->
## 9.7. Exercises and notes

<a id="pdf-4ba63c9394e5-p031-b002"></a>
<!-- pdf-source: page=31; block=2; confidence=0.95 -->
**Exercise 9.35.** Let $q=2r$ be a positive even integer, $\rho = 1/\sqrt{q-1}$, and $f_1,\dots,f_r:\{-1,1\}^n\to\mathbb{R}$. Generalize the $(2,q)$-Hypercontractivity Theorem by showing $\mathbb{E}\big[\prod_{i=1}^r (T_\rho f_i)^2\big] \le \prod_{i=1}^r \mathbb{E}[f_i^2]$. Hint: Hölder's inequality.

<a id="pdf-4ba63c9394e5-p031-b003"></a>
<!-- pdf-source: page=31; block=3; confidence=0.95 -->
**Exercise 9.36.** Simpler, stronger version of Theorem 9.17, assuming $q=2r$ is a positive even integer.

(a) Using the idea of Proposition 9.16, show a uniformly random $\pm1$ bit $x$ is $(2,q,\rho)$-hypercontractive iff $\rho \le 1/\sqrt{q-1}$.

(b) Show the same for any random variable $x$ with $\mathbb{E}[x^2]=1$, $\mathbb{E}[x^{2j-1}]=0$, and $\mathbb{E}[x^{2j}] \le (2r-1)^j\,\binom{r}{j}/\binom{2r}{2j}$ for all integers $1\le j\le r$.

(c) Show that none of the even-moment conditions in (b) can be relaxed.

<a id="pdf-4ba63c9394e5-p031-b004"></a>
<!-- pdf-source: page=31; block=4; confidence=0.78 -->
**Exercise 9.37.** Let $q=2r$ be a positive even integer and $f:\{-1,1\}^n\to\mathbb{R}$ homogeneous of degree $k\ge1$ (i.e. $f=f^{=k}$); goal is to improve slightly on the generalized Bonami Lemma (Theorem 9.21).

(a) Show $\mathbb{E}[f^q]=\sum \hat f(S_1)\cdots\hat f(S_q) \le \sum |\hat f(S_1)|\cdots|\hat f(S_q)|$ &nbsp;(9.18), where the sum is over all tuples $S_1,\dots,S_q$ with $S_1\triangle\cdots\triangle S_q=\emptyset$.

(b) Let $G$ be the complete $q$-partite graph on vertex sets $V_1,\dots,V_q$ each of cardinality $k$, and $\mathcal M$ its set of perfect matchings. Show the RHS of (9.18) equals $\frac{1}{(k!)^q}\sum_{M\in\mathcal M}\sum_{\ell:M\to[n]}|\hat f(T_1(M,\ell))|\cdots|\hat f(T_q(M,\ell))|$ &nbsp;(9.19), where $T_j(M,\ell)=\{\ell(e): e\in M,\ e\cap V_j\ne\emptyset\}$.

(c) Show (9.19) equals $\frac{(rk)!}{(k!)^q}\sum_{M}\sum_{i_1=1}^n\cdots\sum_{i_{rk}=1}^n |\hat f(U_1(M,i_1,\dots,i_{rk}))|\cdots|\hat f(U_q(M,i_1,\dots,i_{rk}))|$ &nbsp;(9.20), where now $M$ ranges over the ordered perfect matchings of $G$ and $U_j(M,i_1,\dots,i_{rk})=\{i_t: M(t)\cap V_j\ne\emptyset\}$.

<a id="pdf-4ba63c9394e5-p032-b001"></a>
<!-- pdf-source: page=32; block=1; confidence=0.85 -->
**Exercise 9.37 (continued).**

(d) For any ordered matching $\overline M\in\overline{\mathcal M}$, $\sum_{i_1,\dots,i_{rk}=1}^n |\hat f(U_1(\overline M,i_1,\dots,i_{rk}))|\cdots|\hat f(U_q(\overline M,i_1,\dots,i_{rk}))| \le \big(\sum_{j_1,\dots,j_k=1}^n \hat f(\{j_1,\dots,j_k\})^2\big)^r$. Hint: apply Cauchy–Schwarz $rk$ times.

(e) Deduce $\|f\|_q^q \le \dfrac{1}{(rk)!\,(k!)^q}\cdot|\overline{\mathcal M}|\cdot(k!)^r\,\|f\|_2^{2r}$, and hence $\|f\|_q \le \dfrac{|\mathcal M|^{1/q}}{\sqrt{k!}}\,\|f\|_2$.

<a id="pdf-4ba63c9394e5-p032-b002"></a>
<!-- pdf-source: page=32; block=2; confidence=0.90 -->
**Exercise 9.38.** Estimate $|\mathcal M|$ to give a concrete improvement on Theorem 9.21.

(a) For $q=4,\ k=2$: $|\mathcal M|=60$.

(b) $|\mathcal M|\le(qk-1)!!$ (the number of perfect matchings of the complete graph on $qk$ vertices); deduce $\|f\|_q\le\sqrt{q}^{\,k}\|f\|_2$.

(c) Show $|\overline{\mathcal M}| \le \big(\tfrac{2r-1}{r}\big)^{rk}(rk)!^{2}$, and thereby deduce $\|f\|_q \le C_{q,k}\,\sqrt{q-1}^{\,k}\|f\|_2$ with $C_{q,k}=\big(\tfrac{(rk)!}{(k!)^r\,r^{rk}}\big)^{1/q}$. Hint: after $t$ edges of the matching are chosen there are $\tfrac{2r-1}{r}(rk-t)^2$ choices for the next edge; worst case is if the vertices used so far are spread equally among the $q$ parts.

(d) Give a simple proof that $C_{q,k}\le1$, thereby obtaining Theorem 9.21.

(e) Show in fact $C_{q,k}=\Theta(1)\,k^{-1/4+1/(2q)}$. Hint: Stirling's Formula.

(f) Can one obtain the improved estimate $\tfrac{|\mathcal M|^{1/q}}{\sqrt{k!}}=\Theta_q(1)\,k^{-1/4}\sqrt{q-1}^{\,k}$? Hint: exactly count then estimate the matchings with exactly $e_{ij}$ edges between parts $i,j$, then sum over the most likely values of $e_{ij}$.

<a id="pdf-4ba63c9394e5-p032-b003"></a>
<!-- pdf-source: page=32; block=3; confidence=0.85 -->
**Notes.** History of the Hypercontractivity Theorem. Earliest roots: Paley [Pal32] (1932) showed that for $1<p<\infty$ there exist constants $0<c_p\le C_p<\infty$ with $c_p\|Sf\|_p \le \|f\|_p \le C_p\|Sf\|_p$ for all $f:\{-1,1\}^n\to\mathbb{R}$, where $Sf=\sqrt{\sum_{t=1}^n (d_tf)^2}$ is the "square function" and $d_tf=\sum_{S:\max(S)=t}\hat f(S)\chi_S$ the martingale-difference sequence (Exercise 8.17). Main task is the even-integer $p$ case; other $p$ follow…

<a id="pdf-4ba63c9394e5-p033-b001"></a>
<!-- pdf-source: page=33; block=1; confidence=0.93 -->
**Notes (cont.).** …by the Riesz(–Thorin) interpolation theorem. Using this result, Paley showed a hypercontractivity result: if $f:\{-1,1\}^n\to\mathbb{R}$ is homogeneous of degree 2, then $c'_p\|f\|_2 \le \|f\|_p \le C'_p\|f\|_2$ for any $p\in\mathbb{R}^+$. Some extensions of Paley's work are in [Wat64].

<a id="pdf-4ba63c9394e5-p033-b002"></a>
<!-- pdf-source: page=33; block=2; confidence=0.83 -->
**Notes.** Bonami [Bon68] (1968) stated a variant of Theorem 9.21: for $f$ homogeneous of degree $k$ and all $q\ge2$, $\|f\|_q \le c_k\,(\sqrt q)^{\,k}\|f\|_2$, with $c_k$ allowed to be $1$ when $q$ is an even integer. She noted it is deducible from Paley's result but with much worse (exponential) $q$-dependence; her combinatorial proof handles only $k=2$, $q$ even (similar to Exercise 9.37).

<a id="pdf-4ba63c9394e5-p033-b003"></a>
<!-- pdf-source: page=33; block=3; confidence=0.87 -->
**Notes.** Independently, Kiener [Kie69] (1969 Ph.D. thesis) extended Paley: for $f$ homogeneous of degree $k$, $c_{p,k}\|f\|_2 \le \|f\|_p \le C_{p,k}\|f\|_2$ for any $p\in\mathbb{R}^+$; proof by induction on $k$, bulk being even-integer $p$. He also gave a combinatorial proof that degree-2 $f$ satisfies $\mathbb{E}[f^4]\le 51\,\mathbb{E}[f^2]^2$ (Exercise 9.38(a) improves 51 to 15).

<a id="pdf-4ba63c9394e5-p033-b004"></a>
<!-- pdf-source: page=33; block=4; confidence=0.87 -->
**Notes.** Also independently, Schreiber [Sch69] (1969) treated multilinear polynomials $f$ over a general orthonormal sequence $x_1,\dots,x_n$ of centered real/complex random variables: if $\deg f\le k$ then for any even integer $q\ge4$, $\|f\|_q\le C\|f\|_2$ with $C$ depending only on $k$, $q$, and the $q$-norms of the $x_i$. Proof similar to Exercise 9.37; he does not estimate his analogue of $|\mathcal M|$, only notes it is finite. Mainly interested in Gaussian $x_i$, generalizing [Sch67].

<a id="pdf-4ba63c9394e5-p033-b005"></a>
<!-- pdf-source: page=33; block=5; confidence=0.88 -->
**Notes.** Bonami [Bon70] (1970 Ph.D. thesis) proved the full Hypercontractivity Theorem. Standard template: elementary $n=1$ case, then induction to general $n$. She gives the sharper combinatorial result of Exercises 9.37 and 9.38(c); the stronger bound of 9.38(f) is due to Janson [Jan97, Rmk 5.20]. As in Corollary 9.6, her combinatorial proof extends to general symmetric orthonormal sequences, at the cost of factors $\|x_i\|_q$ in the bound — including the Gaussian case studied by Schreiber.

<a id="pdf-4ba63c9394e5-p033-b006"></a>
<!-- pdf-source: page=33; block=6; confidence=0.85 -->
**Notes.** Bonami's French-language work stayed largely unknown to English-language mathematicians for about a decade. In the late 1960s–early 1970s, quantum field theory researchers developed the theory… (continues beyond supplied pages).

<a id="pdf-4ba63c9394e5-p034-b001"></a>
<!-- pdf-source: page=34; block=1; confidence=0.90 -->
Historical notes (§9.7) on hypercontractivity for the Ornstein–Uhlenbeck operator $U_\rho$, the Gaussian analogue of $T_\rho$; recognized as essentially a special case of the Boolean case since $(x_1+\cdots+x_n)/\sqrt{n}\to$ Gaussian by the CLT (cf. Ch. 11.1). Attributions: Nelson 1966 [Nel66] proved $\lVert U_{1/\sqrt{q-1}}f\rVert_q\le C_q\lVert f\rVert_2$ for all $q\ge2$; Glimm 1968 [Gli68] showed that for each $q\ge 2$ there is a sufficiently small $\rho_q>0$ with $\lVert U_{\rho_q} f\rVert_q\le\lVert f\rVert_2$; Segal 1970 [Seg70] observed such results follow by induction on the dimension $n$; Nelson 1973 [Nel73] gave the full Gaussian Hypercontractivity Theorem, $\lVert U_{\sqrt{(p-1)/(q-1)}}\,f\rVert_q\le\lVert f\rVert_p$ for all $1\le p<q\le\infty$, and proved combinatorial Exercise 9.37. Equivalence to the Two-Function Hypercontractivity Theorem is due to Neveu 1976 [Nev76].

<a id="pdf-4ba63c9394e5-p034-b002"></a>
<!-- pdf-source: page=34; block=2; confidence=0.85 -->
Gross 1975 [Gro75] introduced Log-Sobolev Inequalities (Exercise 10.23) and deduced hypercontractivity from them: proved the 1-bit log-Sobolev inequality, extended to $n$ bits by induction (citing Segal), then transferred to the Gaussian setting via the CLT (earlier related work [Fed69, Gro72]); this gave a new proof of Nelson's result and independently reestablished Bonami's full Hypercontractivity Theorem. Beckner 1975 [Bec75] proved a sharp hypercontractive inequality for purely complex $\rho$ (noted: [KKL88] miscredited the Hypercontractivity Theorem to Beckner). General complex $\rho$ was treated by Weissler 1979 [Wei79], sharpened by Epperson 1989 [Epp89]; Weissler 1980 [Wei80] first connected this work to Bonami's thesis.

<a id="pdf-4ba63c9394e5-p034-b003"></a>
<!-- pdf-source: page=34; block=3; confidence=0.88 -->
The $(q,2)$-Hypercontractivity Theorem was independently reproved (without sharp constant) in the Banach-spaces community by Rosenthal 1975 [Ros76], using methods akin to Paley and Kiener; further early references in Müller [Mül05, Ch. 1].

<a id="pdf-4ba63c9394e5-p034-b004"></a>
<!-- pdf-source: page=34; block=4; confidence=0.85 -->
The term "hypercontractivity" is due to Simon and Høegh-Krohn 1972 [SHK72]; Definition 9.13 (hypercontractive random variable) is due to Krakowiak and Szulga [KS88]. The short inductive proof of the Bonami Lemma may first appear in Mossel, O'Donnell, Oleszkiewicz [MOO05a]. Theorems 9.22 and 9.24 appear in Janson 1997 [Jan97]; Theorem 9.23 traces to Pisier–Zinn and Borell [PZ78, Bor79]. The Small-Set Expansion Theorem originates with Ahlswede and Gács [AG76]. The Level-$k$ Inequalities appear in several places, credited (continuing to p. 281) to Kahn, Kalai, and Linial [KKL88].

<a id="pdf-4ba63c9394e5-p035-b001"></a>
<!-- pdf-source: page=35; block=1; confidence=0.82 -->
Continuation crediting the Level-$k$ Inequalities to Kahn, Kalai, Linial [KKL88]. Optimal constants for Khintchine's Inequality were established by Haagerup [Haa82] (see also Nazarov–Podkorytov [NP00]); extremizers occur either when $\sum_i a_i x_i$ is $\pm x_1$ (i.e. a single $\pm1$ coordinate) or in the limiting Gaussian case $a_i\equiv 1/\sqrt n$, $n\to\infty$. Ben-Or–Linial [BL85, BL90] were motivated by game theory and the Byzantine Generals problem [LSP82]; Exercise 9.25 is theirs and motivated KKL [KKL88] (cf. Chor–Geréb-Graus [CGG87]). The "KKL Edge-Isoperimetric Theorem" (strengthening the basic KKL Theorem) was first explicitly proved by Talagrand [Tal94], who also handled the $p$-biased case. No combinatorial proof of the KKL Theorem is known; analytic proofs appear in Falik–Samorodnitsky [FS07], Rossignol [Ros06], O'Donnell–Wimmer [OW13]. The lower bound on the "KKL constant" in Exercise 9.30 (best known, from [FS07]) is a factor of 2 from the best known upper bound (achieved by the tribes function).

<a id="pdf-4ba63c9394e5-p035-b002"></a>
<!-- pdf-source: page=35; block=2; confidence=0.80 -->
Friedgut's Junta Theorem is from 1998 [Fri98]. Li-Yang Tan (2011) independently observed the junta size improves for functions with $W^{k}[f]\le\varepsilon$ for $k\ll I[f]/\varepsilon$, giving Corollary 9.31 and its extension to constant-degree PTFs. A stronger result than Corollary 9.31: Diakonikolas–Servedio [DS09] showed every LTF is $\varepsilon$-close to an $I[f]^{2}\,\mathrm{poly}(1/\varepsilon)$-junta. Corollary 9.30 is incomparable with Gopalan–Meka–Reingold [GMR12], which shows every width-$w$ DNF is $\varepsilon$-close to a $(w\log(1/\varepsilon))^{O(w)}$-junta.

<a id="pdf-4ba63c9394e5-p035-b003"></a>
<!-- pdf-source: page=35; block=3; confidence=0.90 -->
Exercise attributions: 9.3 suggested by Krzysztof Oleszkiewicz; 9.12 from Gopalan et al. [GOWZ10]; 9.21 from O'Donnell–Servedio [OS07]; 9.22 from O'Donnell–Wu [OW09]; the estimate in 9.24 from de Klerk–Pasechnik–Warners [dKPW04] (see also [RR01], [KKMO07]); 9.27 and 9.28 due to Kahn–Kalai–Linial [KKL88]; 9.34 suggested by John Wright; 9.36 from Kauers et al. [KOTZ16].
