<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: 9d1751394783984d0665eeac7d363a555809c0c07e3a27b4df65efd6df4dd555 -->

<a id="pdf-9d1751394783-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.97 -->
# Chapter 10. Advanced hypercontractivity

<a id="pdf-9d1751394783-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.90 -->
Completes the proof of the Hypercontractivity Theorem for uniform $\pm 1$ bits, then generalizes the $(p,2)$ and $(2,q)$ statements to arbitrary product probability spaces.

<a id="pdf-9d1751394783-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.96 -->
**The General Hypercontractivity Theorem.** Let $(\Omega_1,\pi_1),\dots,(\Omega_n,\pi_n)$ be finite probability spaces in each of which every outcome has probability at least $\lambda$. Let $f\in L^2(\Omega_1\times\cdots\times\Omega_n,\ \pi_1\otimes\cdots\otimes\pi_n)$. Then for any $q>2$ and $0\le\rho\le \frac{1}{\sqrt{q-1}}\,\lambda^{1/2-1/q}$:

- $\lVert T_\rho f\rVert_q \le \lVert f\rVert_2$, and
- $\lVert T_\rho f\rVert_2 \le \lVert f\rVert_{q'}$.

The upper bound on $\rho$ can be slightly relaxed to the value stated in Theorem 10.18.

<a id="pdf-9d1751394783-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.88 -->
The theorem extends the consequences of the basic Hypercontractivity Theorem from $f:\{-1,1\}^n\to\mathbb{R}$ to $f\in L^2(\Omega^n,\pi^{\otimes n})$ with parameters degraded by $\lambda$. Introduces randomization/symmetrization, which can remove the $\lambda$-dependence; e.g. used to prove Bourgain's Sharp Threshold Theorem characterizing Boolean $f\in L^2(\Omega^n,\pi^{\otimes n})$ of low total influence with no dependence on $\pi$.

<a id="pdf-9d1751394783-p001-b005"></a>
<!-- pdf-source: page=1; block=5; confidence=0.95 -->
## 10.1. The Hypercontractivity Theorem for uniformly random bits

Proves the full Hypercontractivity Theorem for uniform $\pm 1$ bits stated at the start of Chapter 9.

<a id="pdf-9d1751394783-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.92 -->
**The Hypercontractivity Theorem.** Let $f:\{-1,1\}^n\to\mathbb{R}$ and let $1\le p\le q\le\infty$. Then $\lVert T_\rho f\rVert_q \le \lVert f\rVert_p$ for $0\le\rho\le\sqrt{\dfrac{p-1}{q-1}}$.

<a id="pdf-9d1751394783-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.95 -->
**Two-Function Hypercontractivity Theorem.** Let $f,g:\{-1,1\}^n\to\mathbb{R}$, let $r,s\ge 0$, and assume $0\le\rho\le\sqrt{rs}\le 1$. Then
$$\mathop{\mathbb{E}}_{(x,y)\ \rho\text{-correlated}}[f(x)g(y)] \le \lVert f\rVert_{1+r}\,\lVert g\rVert_{1+s}.$$
Equivalent form of the Hypercontractivity Theorem; the difference from the weak form (Chapter 9.4) is that $r,s\le 1$ is not assumed.

<a id="pdf-9d1751394783-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.90 -->
The two theorems are equivalent via Hölder's inequality. Combined with the Two-Function Hypercontractivity Induction Theorem (Chapter 9.4), proving the general-$n$ Hypercontractivity Theorem reduces to the case $n=1$, an elementary technical inequality deferred to the section's end.

<a id="pdf-9d1751394783-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.82 -->
In the fully correlated case $\rho=1$ the theorem reduces to Hölder's inequality:
$$\mathbb{E}[f(x)g(x)] \le \lVert f\rVert_{1+r}\,\lVert g\rVert_{1+1/r}. \tag{10.1}$$
Here $\rho=\sqrt{rs}=1$ forces $s=1/r$, so $1+s=(1+r)'$. For $\rho$-correlated $x,y$ with $\rho<1$ one may use smaller norms on the right-hand side; the independent case $\rho=0$ gives $\mathbb{E}[f(x)g(y)]=\mathbb{E}[f]\,\mathbb{E}[g]\le\lVert f\rVert_1\lVert g\rVert_1$. The theorem interpolates between these extremes.

<a id="pdf-9d1751394783-p002-b005"></a>
<!-- pdf-source: page=2; block=5; confidence=0.90 -->
When $f,g$ have range $\{0,1\}$, the Two-Function Hypercontractivity Theorem yields a two-set generalization of the Small-Set Expansion Theorem.

<a id="pdf-9d1751394783-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.85 -->
**Generalized Small-Set Expansion Theorem.** Let $0\le\rho\le 1$. Let $A,B\subseteq\{-1,1\}^n$ have volumes $\exp(-a^2/2)$ and $\exp(-b^2/2)$, and assume $0\le\rho a\le b\le a$. Then
$$\Pr_{(x,y)\ \rho\text{-correlated}}[x\in A,\ y\in B] \le \exp\!\left(-\tfrac12\,\frac{a^2-2\rho ab+b^2}{1-\rho^2}\right).$$

<a id="pdf-9d1751394783-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.93 -->
**Proof.** Apply the Two-Function Hypercontractivity Theorem with $f=1_A$, $g=1_B$ and minimize the right-hand side by selecting $r=\rho\,\dfrac{b-\rho a}{a-\rho b}$ and $s=\rho\,\dfrac{a-\rho b}{b-\rho a}$. $\square$

<a id="pdf-9d1751394783-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.88 -->
**Remark 10.1.** When $a,b$ are not too close, the optimal $s$ exceeds $1$, so the theorem genuinely needs the full (non-weak) Two-Function Hypercontractivity Theorem. The assumption $b\ge\rho a$ prevents $r<0$.

<a id="pdf-9d1751394783-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.82 -->
**Remark 10.2.** Essentially sharp for concentric Hamming balls (Exercise 10.5). The case $b=a$ recovers the Small-Set Expansion Theorem; the case $b=\rho a$ gives only the trivial bound $\Pr[x\in A,y\in B]\le\Pr[x\in A]=\exp(-a^2/2)$, which cannot be improved much (it holds with equality for concentric Hamming balls when $b\lesssim\rho a$).

<a id="pdf-9d1751394783-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.90 -->
**Remark 10.3.** There is a reverse form of the Hypercontractivity Theorem and its Two-Function version (Exercises 10.6–10.9), which directly implies the Reverse Small-Set Expansion Theorem below.

<a id="pdf-9d1751394783-p003-b006"></a>
<!-- pdf-source: page=3; block=6; confidence=0.88 -->
**Reverse Small-Set Expansion Theorem.** Let $0\le\rho\le 1$. Let $A,B\subseteq\{-1,1\}^n$ have volumes $\exp(-a^2/2)$ and $\exp(-b^2/2)$, where $a,b\ge 0$. Then
$$\Pr_{(x,y)\ \rho\text{-correlated}}[x\in A,\ y\in B] \ge \exp\!\left(-\tfrac12\,\frac{a^2+2\rho ab+b^2}{1-\rho^2}\right).$$

<a id="pdf-9d1751394783-p003-b007"></a>
<!-- pdf-source: page=3; block=7; confidence=0.92 -->
**Proposition 10.4.** Let $T$ be an operator on $L^2(\Omega,\pi)$ and let $1\le p,q\le\infty$. Then
$$\lVert Tf\rVert_q \le \lVert f\rVert_p \quad\text{for all } f\in L^2(\Omega,\pi) \tag{10.2}$$
if and only if
$$\langle Tf, g\rangle \le \lVert f\rVert_p\,\lVert g\rVert_{q'} \quad\text{for all } f,g\in L^2(\Omega,\pi). \tag{10.3}$$
Used to prove the equivalence of the Hypercontractivity Theorem and its Two-Function form (take $T=T_\rho$, $p=1+r$, $q=1+1/s$).

<a id="pdf-9d1751394783-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.93 -->
**Proof.** For the "only if" statement, $\langle Tf,g\rangle \le \lVert Tf\rVert_q\,\lVert g\rVert_{q'} \le \lVert f\rVert_p\,\lVert g\rVert_{q'}$ by Hölder's inequality and (10.2). As for the "if" statement, by Hölder's inequality and (10.3) we have
$$\lVert Tf\rVert_q = \sup_{\lVert g\rVert_{q'}=1}\langle Tf,g\rangle \le \sup_{\lVert g\rVert_{q'}=1}\lVert f\rVert_p\,\lVert g\rVert_{q'} = \lVert f\rVert_p.$$
$\square$

<a id="pdf-9d1751394783-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.83 -->
Proving the Hypercontractivity Theorem for n=1 gives (via the preceding proposition) the Two-Function version for n=1; the Two-Function Hypercontractivity Induction Theorem (Ch. 9.4) then yields the general-n Two-Function theorem, and the proposition again gives the general-n Hypercontractivity Theorem. These arguments hold for general product spaces.

<a id="pdf-9d1751394783-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.86 -->
**Hypercontractivity Induction Theorem.** Let 0 ≤ ρ ≤ 1 and 1 ≤ p, q ≤ ∞. Assume ‖T_ρ f‖_q ≤ ‖f‖_p holds for every f in each of L²(Ω_1,π_1), …, L²(Ω_n,π_n). Then it also holds for every f ∈ L²(Ω_1×···×Ω_n, π_1⊗···⊗π_n).

<a id="pdf-9d1751394783-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.85 -->
**Remark 10.5.** For ±1 bits this theorem is traditionally proven directly by a slightly tricky induction on derivatives (Exercise 10.3); the same strategy works for general product spaces but with more complicated notation.

<a id="pdf-9d1751394783-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.78 -->
Remaining task: prove the Hypercontractivity Theorem for n=1 — that a uniformly random ±1 bit is (p, q, √((p−1)/(q−1)))-hypercontractive. This is the 'Two-Point Inequality', an elementary inequality about two real variables (for fixed p, q, ρ).

<a id="pdf-9d1751394783-p004-b006"></a>
<!-- pdf-source: page=4; block=6; confidence=0.82 -->
**Two-Point Inequality.** Let 1 ≤ p ≤ q ≤ ∞ and 0 ≤ ρ ≤ √((p−1)/(q−1)). Then ‖T_ρ f‖_q ≤ ‖f‖_p for any f : {−1,1} → ℝ. Equivalently (for ρ = √((p−1)/(q−1))), a uniformly random bit x ∼ {−1,1} is (p,q,ρ)-hypercontractive: ‖a + ρbx‖_q ≤ ‖a + bx‖_p for all a, b ∈ ℝ.

<a id="pdf-9d1751394783-p004-b007"></a>
<!-- pdf-source: page=4; block=7; confidence=0.70 -->
**Proof.** As in Section 9.3, the main task is to prove the inequality for 1 < p ≤ q < 2. Given that: the 2 ≤ p, q cases follow from Proposition 9.19; the p = q cases from the semigroup property of T_ρ (Exercise 9.17); and the remaining p < q cases from Exercise 2.33 (or continuity). The 1 < p ≤ q < 2 argument mirrors Theorem 9.18 (the p = q = 2 case): reduce to ρ = √((p−1)/(q−1)), a = 1, b = ε. (continued on next page)

<a id="pdf-9d1751394783-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.90 -->
**Proof (continued).** With $a=1$, $b=\varepsilon$ where $|\varepsilon|<1$, it then suffices to show $\lVert 1+\rho\varepsilon x\rVert_q^p \le \lVert 1+\varepsilon x\rVert_p^p$, i.e.
$$\left(\tfrac12(1+\rho\varepsilon)^q + \tfrac12(1-\rho\varepsilon)^q\right)^{p/q} \le \tfrac12(1+\varepsilon)^p + \tfrac12(1-\varepsilon)^p.$$
Again using $|\varepsilon|<1$ to drop the absolute-value signs and justify the Generalized Binomial Theorem, this is equivalent to

$$\left(1 + \sum_{k=1}^{\infty} \binom{q}{2k}\rho^{2k}\varepsilon^{2k}\right)^{p/q} \le 1 + \sum_{k=1}^{\infty}\binom{p}{2k}\varepsilon^{2k}. \quad (10.4)$$

<a id="pdf-9d1751394783-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.90 -->
**Proof (continued).** Each left coefficient is nonnegative: C(q,2k) = q(q−1)(q−2)···(q−(2k−1))/(2k)! = q(q−1)(2−q)(3−q)···((2k−1)−q)/(2k)! ≥ 0, reversing an even number of signs (valid since 1 ≤ q ≤ 2). Using (1+t)^θ ≤ 1 + θt (t ≥ 0, 0 ≤ θ ≤ 1) with θ = p/q, the LHS of (10.4) is at most 1 + (p/q)Σ_{k≥1} C(q,2k) ρ^{2k} ε^{2k}. With ρ^{2k} = ((p−1)/(q−1))^k, it suffices to prove term-by-term, for all k ≥ 1,

$$\frac{p}{q}\left(\frac{p-1}{q-1}\right)^{k}\binom{q}{2k} \le \binom{p}{2k},$$

which reduces to the factor-by-factor inequality

$$\prod_{j=2}^{2k-1}\frac{j-q}{\sqrt{q-1}} \le \prod_{j=2}^{2k-1}\frac{j-p}{\sqrt{p-1}}.$$

This holds factor-by-factor because p < q and r ↦ (j−r)/√(r−1) is a decreasing function of r ≥ 1 for all j ≥ 2 (derivative −(j−2+r)/(2(r−1)^{3/2}) < 0). ∎

<a id="pdf-9d1751394783-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.85 -->
**Remark 10.6.** The upper bound ρ ≤ √((p−1)/(q−1)) in this theorem is best possible (Exercise 9.10(b)).

<a id="pdf-9d1751394783-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.85 -->
**10.2. Hypercontractivity of general random variables.** Studies hypercontractivity for general random variables; the section culminates in a proof of the General Hypercontractivity Theorem stated at the chapter's start.

<a id="pdf-9d1751394783-p005-b005"></a>
<!-- pdf-source: page=5; block=5; confidence=0.85 -->
**Definition 9.13 (recalled).** A random variable X is (p,q,ρ)-hypercontractive if E[|X|^q] < ∞ and ‖a + ρbX‖_q ≤ ‖a + bX‖_p for all constants a, b ∈ ℝ.

<a id="pdf-9d1751394783-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.85 -->
By homogeneity it suffices to check the defining inequality either with a fixed to 1 or with b fixed to 1.

<a id="pdf-9d1751394783-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.78 -->
**Fact 10.7.** Suppose X is (p,q,ρ)-hypercontractive (1 ≤ p ≤ q ≤ ∞, 0 ≤ ρ < 1). Then: (1) E[X] = 0 (Exercise 9.10); (2) cX is (p,q,ρ)-hypercontractive for any c ∈ ℝ (Exercises 9.10, 9.9); (3) X is (p,q,ρ')-hypercontractive for any 0 ≤ ρ' ≤ ρ (Exercise 9.11); (4) ρ ≤ √((p−1)/(q−1)) and ρ ≤ ‖X‖_p/‖X‖_q (Exercises 9.10, 9.9).

<a id="pdf-9d1751394783-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.87 -->
**Proposition 10.8.** If X is (2,q,ρ)-hypercontractive, then X is also (q',2,ρ)-hypercontractive, where q' is the conjugate Hölder index of q.

<a id="pdf-9d1751394783-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.74 -->
**Proof.** Essentially the same deduction as (9.6) in Ch. 9.2. Since E[X] = 0 (Fact 10.7(1)),

$$\|a+\rho bX\|_2^2 = E[a^2 + 2\rho abX + \rho^2 b^2 X^2] = E[(a+bX)(a+\rho^2 bX)].$$

By Hölder's inequality and then (2,q,ρ)-hypercontractivity (applied with b ↦ ρb), this is at most ‖a+bX‖_{q'} ‖a+ρ²bX‖_q ≤ ‖a+bX‖_{q'} ‖a+ρbX‖_2. Dividing through by ‖a+ρbX‖_2 (nonzero unless X ≡ 0) gives ‖a+ρbX‖_2 ≤ ‖a+bX‖_{q'}, as needed. ∎

<a id="pdf-9d1751394783-p006-b005"></a>
<!-- pdf-source: page=6; block=5; confidence=0.86 -->
**Remark 10.9.** The converse of Proposition 10.8 does not hold (Exercise 10.4).

<a id="pdf-9d1751394783-p006-b006"></a>
<!-- pdf-source: page=6; block=6; confidence=0.85 -->
**Remark 10.10.** Sums of independent hypercontractive random variables are equally hypercontractive (Prop. 9.15), and low-degree polynomials of independent hypercontractive random variables are 'reasonable' (Exercises 10.2, 10.3).

<a id="pdf-9d1751394783-p006-b007"></a>
<!-- pdf-source: page=6; block=7; confidence=0.80 -->
Computing the exact largest ρ can be laborious, but up to constant factors it is easy. Focus on the case p = 2, q > 2; by Fact 10.7(2) one may assume ‖X‖_2 = 1.

<a id="pdf-9d1751394783-p006-b008"></a>
<!-- pdf-source: page=6; block=8; confidence=0.85 -->
**Question 10.11.** Given E[X] = 0, ‖X‖_2 = 1, and ‖X‖_q < ∞, for which ρ is X (2,q,ρ)-hypercontractive?

<a id="pdf-9d1751394783-p006-b009"></a>
<!-- pdf-source: page=6; block=9; confidence=0.94 -->
The section shows ρ = Θ_q(1/‖X‖_q) is sufficient; by the second part of Fact 10.7(4), ρ ≤ ‖X‖_p/‖X‖_q = 1/‖X‖_q is necessary. Hence for a mean-zero X the largest ρ making X (2,q,ρ)-hypercontractive is always within a constant (depending only on q) of ‖X‖_2/‖X‖_q = 1/‖X‖_q.

<a id="pdf-9d1751394783-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.90 -->
## 10.2. Hypercontractivity of general random variables (cont.)

<a id="pdf-9d1751394783-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.85 -->
Introduces symmetrization/randomization. A random variable $X$ is **symmetric** if $X$ has the same distribution as $-X$; consequently $E[X^k]=0$ for all odd $k\in\mathbb{N}$, which yields the next result (analogue of Corollary 9.6, proof like Proposition 9.16).

<a id="pdf-9d1751394783-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.82 -->
**Proposition 10.12.** Let $X$ be symmetric with $\|X\|_2=1$ and $\|X\|_4=C$ (so $X$ is "$C$-4-reasonable"). Then $X$ is $(2,4,\rho)$-hypercontractive if and only if $\rho\le\min\!\left(\tfrac{1}{\sqrt3},\tfrac{1}{C}\right)$.

<a id="pdf-9d1751394783-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.90 -->
**Randomization trick:** for symmetric $X$, replace $X$ by the identically distributed $rX$, where $r\sim\{-1,1\}$ is an independent uniform bit; this can reduce a statement about $X$ to one about $r$.

<a id="pdf-9d1751394783-p007-b005"></a>
<!-- pdf-source: page=7; block=5; confidence=0.85 -->
**Theorem 10.13.** Let $X$ be symmetric with $\|X\|_2=1$ and $\|X\|_q=C$, where $q>2$. Then $X$ is $(2,q,\rho)$-hypercontractive for $\rho=\dfrac{1}{C\sqrt{q-1}}$.

<a id="pdf-9d1751394783-p007-b006"></a>
<!-- pdf-source: page=7; block=6; confidence=0.78 -->
**Proof.** Let $r\sim\{-1,1\}$ be uniform and $\tilde X=X/C$. For any $a\in\mathbb{R}$, estimate $\|a+\rho rX\|_q^2=\big(E_X\,E_r\,|a+\rho rX|^q\big)^{2/q}$ using: symmetry of $X$; the $(2,q,\tfrac{1}{\sqrt{q-1}})$-hypercontractivity of $r$; Parseval; the norm $\|\cdot\|_{q/2}$ taken with respect to $X$; and the triangle inequality for $\|\cdot\|_{q/2}$. This bounds it by $a^2+\|X\|_2^2=a^2+1=\|a+X\|_2^2$, using $E[X]=0$. $\square$

<a id="pdf-9d1751394783-p007-b007"></a>
<!-- pdf-source: page=7; block=7; confidence=0.85 -->
**Symmetrization trick:** if $X$ is not symmetric, replace it by the symmetric $X-X'$ ($X'$ an independent copy), which has similar properties; when $E[X]=0$ norms are compared via a one-sided bound (Lemma 10.14).

<a id="pdf-9d1751394783-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.88 -->
**Lemma 10.14.** Let $X$ satisfy $E[X]=0$ and $\|X\|_q<\infty$ with $q\ge1$. Then for any $a\in\mathbb{R}$, $\|a+X\|_q\le\|a+X-X'\|_q$, where $X'$ is an independent copy of $X$.

<a id="pdf-9d1751394783-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.78 -->
**Proof.** Since $E[X'\mid X]=E[X']=0$, we have $\|a+X\|_q^q=E\big[|a+X+E[X']|^q\big]$. By convexity of $t\mapsto|t|^q$ (Jensen over $X'$), $E\big[|a+X+E[X']|^q\big]\le E\big[|a+X-X'|^q\big]=\|a+X-X'\|_q^q$. $\square$

<a id="pdf-9d1751394783-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.88 -->
Combining the two tricks: replace arbitrary $X$ by $rX$ ($r\sim\{-1,1\}$ independent uniform bit) to extend symmetric-case results to general mean-zero $X$, at the cost of a factor $\tfrac12$, as in the next lemma.

<a id="pdf-9d1751394783-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.85 -->
**Lemma 10.15.** Let $X$ satisfy $E[X]=0$ and $\|X\|_q<\infty$ with $q\ge1$. Then for any $a\in\mathbb{R}$, $\big\|a+\tfrac12 X\big\|_q\le\|a+rX\|_q$, where $r\sim\{-1,1\}$ is an independent uniform bit.

<a id="pdf-9d1751394783-p008-b005"></a>
<!-- pdf-source: page=8; block=5; confidence=0.88 -->
**Proof.** With $X'$ an independent copy: $\big\|a+\tfrac12X\big\|_q\le\big\|a+\tfrac12X-\tfrac12X'\big\|_q$ (Lemma 10.14 applied to $\tfrac12X$) $=\big\|a+\tfrac12 rX-\tfrac12 rX'\big\|_q$ (since $\tfrac12X-\tfrac12X'$ is symmetric). Writing $a=\tfrac12a+\tfrac12a$ and applying the triangle inequality for $\|\cdot\|_q$, then using $-r\sim r$ and $X'\sim X$, this equals $\|a+rX\|_q$. $\square$

<a id="pdf-9d1751394783-p008-b006"></a>
<!-- pdf-source: page=8; block=6; confidence=0.85 -->
These randomization/symmetrization techniques give a $(2,q)$-hypercontractivity statement for all mean-zero $X$ with $\|X\|_q/\|X\|_2$ bounded, answering Question 10.11.

<a id="pdf-9d1751394783-p008-b007"></a>
<!-- pdf-source: page=8; block=7; confidence=0.82 -->
**Theorem 10.16.** Let $X$ satisfy $E[X]=0$, and let $q>2$ with $\|X\|_q/\|X\|_2=C$. Then $X$ is $(2,q,\tfrac12\rho)$-hypercontractive for $\rho=\dfrac{1}{C\sqrt{q-1}}$. If $X$ is symmetric, the factor $\tfrac12$ may be omitted.

<a id="pdf-9d1751394783-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.72 -->
**Proof.** By Lemma 10.15, $\big\|a+\tfrac12\rho X\big\|_q^2\le\|a+\rho rX\|_q^2$. Since $rX$ is symmetric with $\|rX\|_2=1$ and $\|rX\|_q=C$, Theorem 10.13 gives $\|a+\rho rX\|_q^2\le\|a+rX\|_2^2=a^2+1=\|a+X\|_2^2$. $\square$

<a id="pdf-9d1751394783-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.85 -->
For discrete $X$, one can bound $\|X\|_q/\|X\|_2$ using the minimum probability-mass value instead of computing the ratio directly (generalizing Proposition 9.5; proof in Exercise 10.17).

<a id="pdf-9d1751394783-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.80 -->
**Proposition 10.17.** Let $X$ be discrete with pmf $\pi$ and set $\lambda=\min(\pi)=\min_{x\in\mathrm{range}(X)}\Pr[X=x]$. Then for $q>2$, $\|X\|_q\le(1/\lambda)^{1/2-1/q}\|X\|_2$. Consequently, if also $E[X]=0$, then $X$ is $(2,q,\tfrac12\rho)$- and $(q',2,\tfrac12\rho)$-hypercontractive for $\rho=\dfrac{1}{\sqrt{q-1}}\cdot\lambda^{1/2-1/q}$ (by Proposition 10.8). If $X$ is symmetric, the factor $\tfrac12$ may be omitted.

<a id="pdf-9d1751394783-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.82 -->
For each $q>2$, $\rho=\Theta_q(\lambda^{1/2-1/q})$ has optimal $\lambda$-dependence up to a constant. A sharp version is known: the key case $X\sim\pi_\lambda$ (a $\lambda$-biased bit, $X=\phi(x_i)$, Definition 8.39) is due to Latała–Oleszkiewicz [LO00]; the general discrete case reduces to the two-valued case via Wolff [Wol07].

<a id="pdf-9d1751394783-p009-b005"></a>
<!-- pdf-source: page=9; block=5; confidence=0.85 -->
**Theorem 10.18.** Let $X$ be mean-zero discrete with least pmf value $\lambda<1/2$ (as in Proposition 10.17). Then for $q>2$, $X$ is $(2,q,\rho)$- and $(q',2,\rho)$-hypercontractive for
$$\rho=\sqrt{\frac{\exp(u/q)-\exp(-u/q)}{\exp(u/q')-\exp(-u/q')}}=\sqrt{\frac{\sinh(u/q)}{\sinh(u/q')}},\qquad\text{with }u\text{ defined by }\exp(-u)=\frac{\lambda}{1-\lambda}.\tag{10.5}$$
This value of $\rho$ is optimal, even under the assumption that $X$ is two-valued.

<a id="pdf-9d1751394783-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.90 -->
**Remark 10.19.** Examines limiting behavior of $\rho$ from (10.5). As $\lambda\to\tfrac12$ ($u\to0$), $\rho\to\dfrac{1}{\sqrt{q-1}}$, consistent with the Two-Point Inequality of Section 10.1. As $\lambda\to0$ ($u\to\infty$), $\rho\sim\lambda^{1/2-1/q}$, showing Proposition 10.17 is sharp up to a $q$-dependent constant. Exercise 10.18 studies $\rho$ further; in particular $\rho\ge\dfrac{1}{\sqrt{q-1}}\,\lambda^{1/2-1/q}$ holds for all $\lambda$, so the factor $\tfrac12$ in the simpler bound of Proposition 10.17 can be omitted even for nonsymmetric random variables.

<a id="pdf-9d1751394783-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.80 -->
**Corollary 10.20.** Let $(\Omega,\pi)$ be a finite probability space with $|\Omega|\ge2$ in which every outcome has probability at least $\lambda$, and $f\in L^2(\Omega,\pi)$. Then for any $q\ge2$ and $0\le\rho\le\frac{1}{\sqrt{q-1}}\,\lambda^{1/2-1/q}$,
$$\|T_\rho f\|_q\le\|f\|_2\quad\text{and}\quad\|T_\rho f\|_2\le\|f\|_{q'},$$
where $q'$ is the conjugate exponent of $q$.

<a id="pdf-9d1751394783-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.70 -->
**Proof.** By Chapter 8.3, reduce via the decomposition $f=f^{=\varnothing}+f^{=\{1\}}$, under which $T_\rho f=f^{=\varnothing}+\rho\,f^{=\{1\}}$. For $x\sim\pi$ the variable $f^{=\{1\}}(x)$ has mean zero and its probability mass function has minimum value at least $\lambda$. $\square$

<a id="pdf-9d1751394783-p010-b004"></a>
<!-- pdf-source: page=10; block=4; confidence=0.90 -->
The General Hypercontractivity Theorem (stated at the start of the chapter) now follows by applying the Hypercontractivity Induction Theorem of Section 10.1.

<a id="pdf-9d1751394783-p010-b005"></a>
<!-- pdf-source: page=10; block=5; confidence=0.95 -->
## 10.3. Applications of general hypercontractivity

Collects applications of the General Hypercontractivity Theorem generalizing Section 9.5, beginning with $q$-norm bounds on low-degree functions (proof essentially as Theorem 9.21; Exercise 10.28).

<a id="pdf-9d1751394783-p010-b006"></a>
<!-- pdf-source: page=10; block=6; confidence=0.95 -->
**Theorem 10.21.** In the setting of the General Hypercontractivity Theorem, if $f$ has degree at most $k$, then
$$\|f\|_q\le\big(\sqrt{q-1}\,\lambda^{1/q-1/2}\big)^k\,\|f\|_2.$$

<a id="pdf-9d1751394783-p010-b007"></a>
<!-- pdf-source: page=10; block=7; confidence=0.85 -->
An analogue of Theorem 9.22 relating the 2-norm and 1-norm of low-degree functions follows; the proof (Exercise 10.31) uses $(2,q,\rho)$-hypercontractivity with $q\to2$, appealing to the sharp bound of Theorem 10.18.

<a id="pdf-9d1751394783-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.95 -->
**Theorem 10.22.** In the General Hypercontractivity setting, if $f$ has degree at most $k$, then $\|f\|_2\le c(\lambda)^k\,\|f\|_1$, where $c(\lambda)=\big(\tfrac{1-\lambda}{\lambda}\big)^{1/(2(1-2\lambda))}$. Asymptotics: $c(\lambda)\sim1/\sqrt\lambda$ as $\lambda\to0$; $c(\lambda)\to e$ as $\lambda\to\tfrac12$; and in general $c(\lambda)\le e/\sqrt{2\lambda}$.

<a id="pdf-9d1751394783-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.90 -->
**Theorem 10.23.** (Corollary of the above; Exercise 10.32.) In the General Hypercontractivity setting, if $f$ is a nonconstant function of degree at most $k$, then
$$\Pr_{x\sim\pi^{\otimes n}}\big[f(x)>\mathbf{E}[f]\big]\ge\tfrac14\,(e^2/2\lambda)^{-k}\ge(15/\lambda)^{-k}.$$

<a id="pdf-9d1751394783-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.80 -->
**Theorem 10.24.** (Extends the degree-$k$ concentration bound Theorem 9.23; Exercise 10.33.) In the General Hypercontractivity setting, if $f$ has degree at most $k$, then for any $t\ge(2e/\lambda)^{k/2}$,
$$\Pr_{x\sim\pi^{\otimes n}}\big[|f(x)|\ge t\|f\|_2\big]\le\lambda^k\exp\!\Big(-\tfrac{k}{2e}\,\lambda\,t^{2/k}\Big).$$
Thus the probability of exceeding $t$ standard deviations decays like $\exp(-\Theta(t^2/k))$, with the constant linear in $\lambda$.

<a id="pdf-9d1751394783-p011-b004"></a>
<!-- pdf-source: page=11; block=4; confidence=0.88 -->
**Theorem 10.25.** (Generalizes the Small-Set Expansion Theorem; Exercise 10.34.) Let $(\Omega,\pi)$ be a finite probability space with $|\Omega|\ge2$ in which every outcome has probability at least $\lambda$. Let $A\subseteq\Omega^n$ have volume $\alpha$, i.e. $\Pr_{x\sim\pi^{\otimes n}}[x\in A]=\alpha$, and let $q\ge2$. Then for any $0\le\rho\le\frac{1}{q-1}\lambda^{1-2/q}$ (or even $\rho$ up to the square of the quantity in Theorem 10.18),
$$\mathrm{Stab}_\rho[1_A]=\Pr_{\substack{x\sim\pi^{\otimes n}\\ y\sim N_\rho(x)}}[x\in A,\ y\in A]\le\alpha^{2-2/q}.$$

<a id="pdf-9d1751394783-p011-b005"></a>
<!-- pdf-source: page=11; block=5; confidence=0.82 -->
**Theorem 10.26.** (Generalizes Corollary 9.25, bounding stable influence by a power of ordinary influence.) In the setting of Theorem 10.25, if $f:\Omega^n\to\{-1,1\}$, then for all $i\in[n]$,
$$\rho\,\mathrm{Inf}_i^{(\rho)}[f]\le\mathrm{Inf}_i[f]^{2-2/q}.$$
Taking $q=4$ (so $\rho=\sqrt\lambda/3$) yields equation **(10.6)**:
$$\sum_{S\ni i}(\sqrt\lambda/3)^{|S|}\,\|f^{=S}\|_2^2\le\mathrm{Inf}_i[f]^{3/2}.$$

<a id="pdf-9d1751394783-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.78 -->
**Proof.** Apply the General Hypercontractivity Theorem to $L_i f$ and square:
$$\rho\,\mathrm{Inf}_i^{(\rho)}[f]=\|T_{\sqrt\rho}L_i f\|_2^2\le\|L_i f\|_{q'}^2=\big(\|L_i f\|_{q'}^{q'}\big)^{2/q'}=\mathrm{Inf}_i[f]^{2-2/q},$$
using $2/q'=2-2/q$ and $\|L_i f\|_{q'}^{q'}=\mathrm{Inf}_i[f]$ (Exercise 8.10(b)). $\square$

<a id="pdf-9d1751394783-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.95 -->
**KKL Isoperimetric Theorem for general product space domains.** In the General Hypercontractivity setting, let $f$ have range $\{-1,1\}$ and be nonconstant, and write $\tilde I[f]=I[f]/\mathrm{Var}[f]\ge1$. Then
$$\mathrm{MaxInf}[f]\ge\frac{1}{\tilde I[f]^2}\,(9/\lambda)^{-\tilde I[f]}.$$
As a consequence, $\mathrm{MaxInf}[f]\ge\Omega\!\big(\tfrac{1}{\log(1/\lambda)}\big)\,\mathrm{Var}[f]\,\tfrac{\log n}{n}.$

<a id="pdf-9d1751394783-p012-b003"></a>
<!-- pdf-source: page=12; block=3; confidence=0.85 -->
**Proof.** (Cf. Exercise 9.29; essentially the Chapter 9.6 proof, now using (10.6).) Summing (10.6) over $i\in[n]$:
$$\sum_{S\subseteq[n]}|S|(\sqrt\lambda/3)^{|S|}\|f^{=S}\|_2^2\le\sum_{i=1}^n\mathrm{Inf}_i[f]^{3/2}\le\mathrm{MaxInf}[f]^{1/2}\,I[f].\tag{10.7}$$
Drop the factor $|S|>0$ on the left and introduce a set-valued random variable $\mathbf S$ with $\Pr[\mathbf S=S]=\|f^{=S}\|_2^2/\mathrm{Var}[f]$ for $S\ne\varnothing$, so $\mathbf E[|\mathbf S|]=\tilde I[f]$. Then, by convexity of $s\mapsto(\sqrt\lambda/3)^s$ (Jensen),
$$\mathrm{LHS}(10.7)\ge\mathrm{Var}[f]\,\mathbf E\big[(\sqrt\lambda/3)^{|\mathbf S|}\big]\ge\mathrm{Var}[f]\,(\sqrt\lambda/3)^{\tilde I[f]}.$$
Rearranging gives the first statement. The second follows from a case split on whether $\tilde I[f]$ is below or above $c\,\tfrac{\log n}{\log(1/\lambda)}$ (universal $c>0$): for small $\tilde I[f]$ the first statement gives $\mathrm{MaxInf}[f]\gtrsim1/\sqrt n\gg(\log n)/n$; for large $\tilde I[f]$, $I[f]\ge\Omega\!\big(\tfrac{1}{\log(1/\lambda)}\big)\mathrm{Var}[f]\log n$, so the average influence $I[f]/n$ already exceeds $\Omega\!\big(\tfrac{1}{\log(1/\lambda)}\big)\mathrm{Var}[f]\tfrac{\log n}{n}$. $\square$

<a id="pdf-9d1751394783-p012-b004"></a>
<!-- pdf-source: page=12; block=4; confidence=0.90 -->
Theorem 9.28 and Friedgut's Junta Theorem generalize to general product space domains with essentially no extra work (Exercise 10.35); an example is stated (continuing beyond these pages).

<a id="pdf-9d1751394783-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.95 -->
**Friedgut's Junta Theorem (general product spaces).** In the setting of the General Hypercontractivity Theorem, if $f$ has range $\{-1,1\}$ and $0<\epsilon\le 1$, then $f$ is $\epsilon$-close to a $(1/\lambda)^{O(I[f]/\epsilon)}$-junta $h:\Omega^n\to\{-1,1\}$; i.e. $\Pr_{x\sim\pi^{\otimes n}}[f(x)\ne h(x)]\le\epsilon$.

<a id="pdf-9d1751394783-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.83 -->
**Setup (sharp thresholds).** For a nonconstant monotone $f:\{-1,1\}^n\to\{-1,1\}$, define the strictly increasing curve $F:[0,1]\to[0,1]$ by $F(p)=\Pr_{x\sim\pi_p^{\otimes n}}[f(x)=-1]$. The critical probability $p_c$ satisfies $F(p_c)=1/2$, equivalently $\mathrm{Var}[f(p_c)]=1$. Margulis–Russo Formula: $\dfrac{d}{dp}F(p)=\dfrac{1}{\sigma^2}\,I[f(p)]$, where $\sigma^2=\sigma^2(p)=\mathrm{Var}_{\pi_p}[x_i]=4p(1-p)=\Theta(\min(p,1-p))$. Objective: establish sharp thresholds for monotone transitive-symmetric $f$ with $p_c\in[1/n^{o(1)},\,1-1/n^{o(1)}]$.

<a id="pdf-9d1751394783-p013-b003"></a>
<!-- pdf-source: page=13; block=3; confidence=0.92 -->
**Remark 10.27.** Ignoring constant factors, one may replace $\sigma^2$ by $\min(p,1-p)$; more conveniently, assume $p\le 1/2$ and replace $\sigma^2$ by $p$.

<a id="pdf-9d1751394783-p013-b004"></a>
<!-- pdf-source: page=13; block=4; confidence=0.85 -->
**KKL corollary.** For a transitive-symmetric $f$ all influences coincide: $\mathrm{Inf}_i[f(p)]=\mathrm{MaxInf}[f(p)]=\tfrac1n I[f(p)]$ for all $i$. The KKL Theorem for general product spaces then gives $I[f(p)]\ge\Omega\!\big(\mathrm{Var}[f(p)]\cdot\frac{\log n}{\log(1/\min(p,1-p))}\big)$, hence $\dfrac{d}{dp}F(p)\ge\Omega\!\big(\mathrm{Var}[f(p)]\cdot\frac{\log n}{\sigma^2\ln(e/\sigma^2)}\big)$ (10.8). For $p\le 1/2$ one reads $\sigma^2\ln(e/\sigma^2)=p\log(1/p)$.

<a id="pdf-9d1751394783-p013-b005"></a>
<!-- pdf-source: page=13; block=5; confidence=0.86 -->
**Discussion.** Taking $p=p_c$ in (10.8) (with $p_c\le 1/2$) gives a large derivative at criticality: $F'(p_c)\ge\Omega\!\big(\frac{\log n}{p_c\log(1/p_c)}\big)$. If $\log(1/p_c)\ll\log n$ (i.e. $p_c\gg 1/n^{o(1)}$) then $F'(p_c)=\omega(1/p_c)$, suggesting a sharp threshold where $F$ jumps from near $0$ to near $1$ over an interval $p_c(1\pm o(1))$. Largeness of $F'(p_c)$ alone is insufficient (Exercise 8.30); one needs $F'(p)$ large throughout the range near $p_c$ where $\mathrm{Var}[f(p)]$ is large, which (10.8) provides.

<a id="pdf-9d1751394783-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.90 -->
**Remark 10.28.** Even for monotone $f$ with $p_c=1/2$, establishing a sharp threshold requires the KKL Theorem for general product spaces: $F'(1/2)=\Omega(\log n)$ follows from the uniform-distribution KKL Theorem (Chapter 9.6), but one also needs $F'(p)=\Omega(\log n)$ to persist for $p=1/2\pm O(1/\log n)$.

<a id="pdf-9d1751394783-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.88 -->
**Theorem 10.29 (Friedgut–Kalai).** Let $f:\{-1,1\}^n\to\{-1,1\}$ be nonconstant, monotone, and transitive-symmetric, with strictly increasing $F:[0,1]\to[0,1]$ given by $F(p)=\Pr_{x\sim\pi_p^{\otimes n}}[f(x)=-1]$ and critical $p_c$ with $F(p_c)=1/2$. Fix $0<\epsilon<1/4$, assume WLOG $p_c\le 1/2$, and set $\eta=B\log(1/\epsilon)\cdot\dfrac{\log(1/p_c)}{\log n}$ for a universal constant $B>0$. Then, assuming $\eta\le 1/2$, $F(p_c(1-\eta))\le\epsilon$ and $F(p_c(1+\eta))\ge 1-\epsilon$.

<a id="pdf-9d1751394783-p014-b003"></a>
<!-- pdf-source: page=14; block=3; confidence=0.85 -->
**Proof.** For $p$ in the range $p_c(1\pm\eta)$, since $\eta\le 1/2$ we have $\tfrac12 p_c\le p\le\tfrac32 p_c\le\tfrac34$, so the quantity $\sigma^2\ln(e/\sigma^2)$ in the KKL corollary (10.8) is within a universal constant factor of $p_c\log(1/p_c)$. Thus for all such $p$, $F'(p)\ge\Omega\!\big(\mathrm{Var}[f(p)]\cdot\frac{\log n}{p_c\log(1/p_c)}\big)$. Using $\mathrm{Var}[f(p)]=4F(p)(1-F(p))$, the definition of $\eta$, and a suitable $B$, this is equivalent to $F'(p)\ge\dfrac{2\ln(1/2\epsilon)}{\eta p_c}F(p)(1-F(p))$ (10.9). We show (10.9) implies $F(p_c-\eta p_c)\le\epsilon$, leaving $F(p_c+\eta p_c)\ge 1-\epsilon$ to Exercise 10.36. For $p\le p_c$, $1-F(p)\ge 1/2$, so $F'(p)\ge\dfrac{\ln(1/2\epsilon)}{\eta p_c}F(p)\Rightarrow\dfrac{d}{dp}\ln F(p)=\dfrac{F'(p)}{F(p)}\ge\dfrac{\ln(1/2\epsilon)}{\eta p_c}$. Hence $\ln F(p_c-\eta p_c)\le\ln F(p_c)-\ln(1/2\epsilon)=\ln(1/2)-\ln(1/2\epsilon)=\ln\epsilon$, i.e. $F(p_c-\eta p_c)\le\epsilon$. $\square$

<a id="pdf-9d1751394783-p014-b004"></a>
<!-- pdf-source: page=14; block=4; confidence=0.90 -->
**Discussion.** The proof shows every monotone transitive-symmetric function with critical probability in $[1/n^{o(1)},\,1-1/n^{o(1)}]$ has a sharp threshold. The restriction on $p_c$ cannot be removed; the simplest illustrating counterexample is logical OR.

<a id="pdf-9d1751394783-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.93 -->
**OR counterexample.** $\mathrm{OR}_n:\{\mathrm{True,False}\}^n\to\{\mathrm{True,False}\}$ (equivalently, the graph property of containing an edge) has critical probability $p_c\sim\frac{\ln 2}{n}$. Even though transitive-symmetric, it has constant total influence at its critical probability, $I[\mathrm{OR}_n^{(p_c)}]\sim 2\ln 2$, and hence no sharp threshold: it is not the case that $\Pr_{\pi_p}[\mathrm{OR}_n(x)=\mathrm{True}]=1-o(1)$ for $p=p_c(1+o(1))$. E.g. if $x$ is drawn from the $(2p_c)$-biased distribution we still just have $\Pr[\mathrm{OR}_n(x)=\mathrm{True}]\approx \tfrac34$. Most interesting monotone transitive-symmetric functions do have sharp thresholds (a more sophisticated method appears in Section 10.5).

<a id="pdf-9d1751394783-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.97 -->
## 10.4. More on randomization/symmetrization

<a id="pdf-9d1751394783-p015-b003"></a>
<!-- pdf-source: page=15; block=3; confidence=0.85 -->
**Motivation.** The Section 10.3 consequences of the General Hypercontractivity Theorem for $f\in L^2(\Omega^n,\pi^{\otimes n})$ all depend on $\lambda$, the least probability of an outcome under $\pi$, which is expensive: KKL and Theorem 10.29 are trivialized when $\lambda=1/n^{\Theta(1)}$. For symmetric random variables the randomization trick reduces to uniformly random $\pm1$ bits ($\lambda=1/2$), and Lemma 10.15 symmetrizes general mean-zero variables (at the cost of applying $T_{1/2}$). This section develops the technique and applies it to bound the $L^p\to L^p$ norm of the low-degree projection operator.

<a id="pdf-9d1751394783-p015-b004"></a>
<!-- pdf-source: page=15; block=4; confidence=0.88 -->
**Informal description.** Applying randomization/symmetrization to $f\in L^2(\Omega^n,\pi^{\otimes n})$ means introducing $n$ independent uniform bits $r=(r_1,\dots,r_n)\sim\{-1,1\}^n$ and "multiplying the $i$th input by $r_i$"—precisely, multiplying $L_if$, the $i$th part of $f$'s Fourier/orthogonal decomposition, by $r_i$.

<a id="pdf-9d1751394783-p015-b005"></a>
<!-- pdf-source: page=15; block=5; confidence=0.90 -->
**Example 10.30.** For a Boolean $f:\{-1,1\}^n\to\mathbb{R}$ with Fourier expansion $f(x)=\sum_{S\subseteq[n]}\hat f(S)\,x^S$ (where $x^S=\prod_{i\in S}x_i$), its randomization/symmetrization is $\tilde f(r,x)=\sum_{S\subseteq[n]}\hat f(S)\prod_{i\in S}r_ix_i=\sum_{S\subseteq[n]}\hat f(S)\,x^S r^S$. Key observation: for random $x,r\sim\{-1,1\}^n$, the variables $f(x)$ and $\tilde f(r,x)$ are identically distributed, because $x^S$ is a symmetric random variable and so has the same distribution as $r^S x^S$.

<a id="pdf-9d1751394783-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.70 -->
**Example 10.31.** Revisiting Examples 8.10/8.15: $\Omega=\{a,b,c\}$, $\pi$ uniform, Fourier basis $\{\varphi_0\equiv1,\varphi_1,\varphi_2\}$. A typical $f:\Omega^3\to\mathbb R$ is a linear combination of tensor monomials in $\varphi_1,\varphi_2$ (constant $\tfrac13$, plus terms such as $-\tfrac14\varphi_1(x_i)$, $\tfrac32\varphi_2(x_i)$, etc., with various rational coefficients). Its randomization/symmetrization $\tilde f\in L^2(\{-1,1\}^3\times\Omega^3,\ \pi_{1/2}^{\otimes3}\otimes\pi^{\otimes3})$ multiplies each degree-$|S|$ monomial by $r_S$. Key point: $\varphi_2(x_i)$ is a symmetric real random variable when $x_i\sim\pi$, so $r_i\varphi_2(x_i)$ has the same distribution as $\varphi_2(x_i)$; hence if $g$'s Fourier expansion uses only $\varphi_2$ (never $\varphi_1$), then $g(x)$ and $\tilde g(r,x)$ are identically distributed. In general there is no obvious way to compare the distributions of $f(x)$ and $\tilde f(r,x)$.

<a id="pdf-9d1751394783-p016-b002"></a>
<!-- pdf-source: page=16; block=2; confidence=0.80 -->
**Definition 10.32.** For $f\in L^2(\Omega^n,\pi^{\otimes n})$, its randomization/symmetrization is $\tilde f\in L^2(\{-1,1\}^n\times\Omega^n,\ \pi_{1/2}^{\otimes n}\otimes\pi^{\otimes n})$ defined by
$$\tilde f(r,x)=\sum_{S\subseteq[n]} r_S\, f^{=S}(x),\qquad r_S=\prod_{i\in S} r_i. \tag{10.10}$$

<a id="pdf-9d1751394783-p016-b003"></a>
<!-- pdf-source: page=16; block=3; confidence=0.85 -->
**Remark 10.33.** Equivalently, for each $x\in\Omega^n$, $\tilde f|_x:\{-1,1\}^n\to\mathbb R$ is the Boolean function whose Fourier coefficient on $S$ equals $f^{=S}(x)$ (this is the same as (10.10) with the roles of $r_S$ and $f^{=S}(x)$ swapped).

<a id="pdf-9d1751394783-p016-b004"></a>
<!-- pdf-source: page=16; block=4; confidence=0.85 -->
By Parseval for Boolean functions, for all $x\in\Omega^n$, $\|\tilde f|_x\|_{2,r}^2=\sum_{S\subseteq[n]} f^{=S}(x)^2$. Taking $\mathbb E_{x\sim\pi^{\otimes n}}$: the left side becomes $\|\tilde f\|_{2,r,x}^2$ and the right side becomes $\|f\|_{2,x}^2$ by Parseval for $L^2(\Omega^n,\pi^{\otimes n})$; hence $\|\tilde f\|_2^2=\|f\|_2^2$.

<a id="pdf-9d1751394783-p017-b001"></a>
<!-- pdf-source: page=17; block=1; confidence=0.95 -->
**10.4. More on randomization/symmetrization**

<a id="pdf-9d1751394783-p017-b002"></a>
<!-- pdf-source: page=17; block=2; confidence=0.90 -->
**Proposition 10.34.** For $f\in L^2(\Omega^n,\pi^{\otimes n})$, $\|\tilde f\|_2=\|f\|_2$; randomization/symmetrization does not change $2$-norms.

<a id="pdf-9d1751394783-p017-b003"></a>
<!-- pdf-source: page=17; block=3; confidence=0.90 -->
**Theorem 10.35.** For $f\in L^2(\Omega^n,\pi^{\otimes n})$ and $q>1$,
$$\|\mathrm T_{1/2} f\|_q\le\|\tilde f\|_q\le\|\mathrm T_{c_q^{-1}} f\|_q. \tag{10.11}$$
Equivalently, $\|\widetilde{\mathrm T_{c_q} f}\|_q\le\|f\|_q\le\|\widetilde{\mathrm T_2 f}\|_q$. Here $0<c_q\le1$ is a constant depending only on $q$; one may take $c_4=c_{4/3}=\tfrac25$. The two inequalities in (10.11) are not too difficult to prove; e.g. the left-hand inequality follows from randomization/symmetrization Lemma 10.15 plus induction.

<a id="pdf-9d1751394783-p017-b004"></a>
<!-- pdf-source: page=17; block=4; confidence=0.85 -->
**Question 10.36.** For $k\in\mathbb N$, $1\le q<\infty$, $f\in L^2(\Omega^n,\pi^{\otimes n})$: can the low-degree projection norm $\|f^{\le k}\|_q$ be much larger than $\|f\|_q$? Equivalently, can adding degree-$>k$ terms to a degree-$\le k$ function $g$ greatly decrease its $q$-norm? For $q\le2$ the answer is easy via Parseval:
$$\|f^{\le k}\|_q\le\|f^{\le k}\|_2,\quad \|f^{\le k}\|_2^2=\sum_{j=0}^k W^j[f]\le\sum_{j=0}^n W^j[f]=\|f\|_2^2, \tag{10.12}$$
so $\|f^{\le k}\|_q\le\|f\|_2$. For $q>2$ it is harder; first specialize to $\Omega=\{-1,1\}$, $\pi=\pi_{1/2}$ and use hypercontractivity.

<a id="pdf-9d1751394783-p017-b005"></a>
<!-- pdf-source: page=17; block=5; confidence=0.65 -->
**Proposition 10.37.** For $k\in\mathbb N$ and $g:\{-1,1\}^n\to\mathbb R$: for $q\ge2$, $\|g^{\le k}\|_q\le(\sqrt{q-1})^{k}\|g\|_q$; and for $1\le q\le2$, $\|g^{\le k}\|_q\ge(\sqrt{q-1})^{k}\|g\|_q$. This is a consequence of the Hypercontractivity Theorem (Exercise 9.8).

<a id="pdf-9d1751394783-p018-b001"></a>
<!-- pdf-source: page=18; block=1; confidence=0.75 -->
The simplest case $q=4$ of Prop 10.37 follows from the Bonami Lemma alone: $\|g^{\le k}\|_4\le(\sqrt3)^{k}\|g^{\le k}\|_2\le(\sqrt3)^{k}\|g\|_2\le(\sqrt3)^{k}\|g\|_4$, i.e.
$$\|g^{\le k}\|_4\le(\sqrt3)^{k}\|g\|_4. \tag{10.13}$$
For general $f\in L^2(\Omega^n,\pi^{\otimes n})$ (focusing on $q=4$): repeating the proof via the General Hypercontractivity Theorem (Theorem 10.21) gives $\|f^{\le k}\|_4\le(\sqrt{3/\lambda})^{k}\|f\|_4$, but randomization/symmetrization instead yields a bound independent of $\lambda$, i.e. of $(\Omega,\pi)$.

<a id="pdf-9d1751394783-p018-b002"></a>
<!-- pdf-source: page=18; block=2; confidence=0.90 -->
For the lucky case (Example 10.31) where $f$'s spectrum uses only symmetric basis functions, $f^{\le k}(x)$ and $\tilde f^{\le k}(r,x)$ share a distribution, so
$$\|f^{\le k}\|_4=\|\tilde f^{\le k}\|_4=\big\|\,\|\tilde f^{\le k}|_x\|_{4,r}\,\big\|_{4,x}.$$
For each $x$, $g(r)=\tilde f^{\le k}|_x(r)$ is a degree-$k$ function of $r\in\{-1,1\}^n$; applying (10.13) gives $\big\|\,\|\tilde f^{\le k}|_x\|_{4,r}\,\big\|_{4,x}\le(\sqrt3)^{k}\|\tilde f\|_4=(\sqrt3)^{k}\|f\|_4$. Thus (10.13) holds automatically for luckily-symmetric $f$ with no $\lambda$-dependence. For general $f$, using Theorem 10.35 gives a similar bound but loses a factor of $(2\cdot\tfrac52)^k$ from applying $T_2$ and $T_{5/2}$.

<a id="pdf-9d1751394783-p018-b003"></a>
<!-- pdf-source: page=18; block=3; confidence=0.85 -->
**Lemma 10.38.** For $k\in\mathbb N$, $g:\{-1,1\}^n\to\mathbb R$, and any $0<\rho\le1$,
$$\|g^{\le k}\|_4\le(\sqrt3/\rho)^{k}\,\|T_\rho g\|_4.$$

<a id="pdf-9d1751394783-p018-b004"></a>
<!-- pdf-source: page=18; block=4; confidence=0.85 -->
**Proof.** $\|g^{\le k}\|_4\le(\sqrt3)^{k}\|g^{\le k}\|_2\le(\sqrt3/\rho)^{k}\|T_\rho g\|_2\le(\sqrt3/\rho)^{k}\|T_\rho g\|_4$. The first inequality is Bonami's Lemma; the second holds since
$$\|g^{\le k}\|_2^2=\sum_{j=0}^k W^j[g]\le(1/\rho^2)^{k}\sum_{j=0}^k \rho^{2j}W^j[g]\le(1/\rho^2)^{k}\sum_{j=0}^n \rho^{2j}W^j[g]=(1/\rho^2)^{k}\|T_\rho g\|_2^2. \qquad\square$$

<a id="pdf-9d1751394783-p018-b005"></a>
<!-- pdf-source: page=18; block=5; confidence=0.80 -->
We can now give a good answer to Question 10.36, showing that low-degree projection does not substantially increase any $q$-norm.

<a id="pdf-9d1751394783-p019-b001"></a>
<!-- pdf-source: page=19; block=1; confidence=0.60 -->
## 10.4. More on randomization/symmetrization

<a id="pdf-9d1751394783-p019-b002"></a>
<!-- pdf-source: page=19; block=2; confidence=0.95 -->
**Theorem 10.39.** Let $k\in\mathbb{N}$ and let $f\in L^2(\Omega^n,\pi^{\otimes n})$. Then for any $q>1$ we have $\|f^{\le k}\|_q \le C_q^{k}\,\|f\|_q$, where $C_q$ depends only on $q$; in particular one may take $C_4=C_{4/3}=5\sqrt{3}\le 9$.

<a id="pdf-9d1751394783-p019-b003"></a>
<!-- pdf-source: page=19; block=3; confidence=0.88 -->
**Proof.** We give the proof for $q=4$; the other cases are left for Exercise 10.16. By the randomization/symmetrization Theorem 10.35,
$$\|f^{\le k}\|_4 \le \big\|\widetilde{\mathrm T_2 f^{\le k}}\big\|_4 = \big\|\,\|\widetilde{\mathrm T_2 f^{\le k}}|_x(r)\|_{4,r}\,\big\|_{4,x}.$$
For a given outcome $x$, write $g=\widetilde{\mathrm T_2 f}|_x:\{-1,1\}^n\to\mathbb R$, so $\|g^{\le k}(r)\|_4$ appears on the inside above; $g$ is the Boolean function whose Fourier coefficient on $S$ is $2^{|S|}\,f^{=S}(x)$. Applying Lemma 10.38 to this $g$ with $\rho=\tfrac15$ (so $\mathrm T_\rho g$ has Fourier coefficient $(\tfrac25)^{|S|}f^{=S}(x)$, i.e. it is $\widetilde{\mathrm T_{2/5}f}|_x$) yields
$$\big\|\,\|\widetilde{\mathrm T_2 f^{\le k}}|_x(r)\|_{4,r}\,\big\|_{4,x}\le(5\sqrt3)^k\,\big\|\,\|\widetilde{\mathrm T_{2/5}f}|_x(r)\|_{4,r}\,\big\|_{4,x}=(5\sqrt3)^k\,\|\widetilde{\mathrm T_{2/5}f}\|_4\le (5\sqrt3)^k\,\|f\|_4,$$
the last step being the un-randomization/symmetrization inequality from Theorem 10.35. $\square$

<a id="pdf-9d1751394783-p019-b004"></a>
<!-- pdf-source: page=19; block=4; confidence=0.85 -->
The remainder of the section proves Theorem 10.35 (comparing norms of a function and its randomization/symmetrization) via an operator perspective that extends the $T_\rho$ notation to allow different noise rates on different coordinates.

<a id="pdf-9d1751394783-p019-b005"></a>
<!-- pdf-source: page=19; block=5; confidence=0.85 -->
**Definition 10.40.** For $i\in[n]$ and $\rho\in\mathbb{R}$, define $T^i_\rho$ on $L^2(\Omega^n,\pi^{\otimes n})$ by
$$T^i_\rho f = \rho f + (1-\rho)\,\mathrm{E}_i f = \mathrm{E}_i f + \rho\,\mathrm{L}_i f = \sum_{S\not\ni i} f^{=S} + \rho\sum_{S\ni i} f^{=S}. \tag{10.14}$$
For $r=(r_1,\dots,r_n)\in\mathbb{R}^n$, define $T_r = T^1_{r_1}T^2_{r_2}\cdots T^n_{r_n}$; by the third formula in (10.14),
$$T_r f = \sum_{S\subseteq[n]} r^S f^{=S}, \qquad r^S=\prod_{i\in S} r_i. \tag{10.15}$$
In particular $T_{(\rho,\dots,\rho)}=T_\rho$, and for $r\in[0,1]^n$, $T_r f(x)=\mathbb{E}_{y_1\sim N_{r_1}(x_1),\dots,y_n\sim N_{r_n}(x_n)}[f(y_1,\dots,y_n)]$.

<a id="pdf-9d1751394783-p019-b006"></a>
<!-- pdf-source: page=19; block=6; confidence=0.85 -->
These generalized noise operators satisfy the expected basic properties (Exercise 8.11); comparing (10.15) with (10.10) reveals the connection to randomization/symmetrization.

<a id="pdf-9d1751394783-p020-b001"></a>
<!-- pdf-source: page=20; block=1; confidence=0.90 -->
**Fact 10.41.** For $f\in L^2(\Omega^n,\pi^{\otimes n})$, $x\in\Omega^n$, $r\in\{-1,1\}^n$: $\tilde f(r,x)=T_r f(x)$. I.e., randomization/symmetrization of $f$ is applying $T_{(\pm1,\dots,\pm1)}$ for a random choice of signs.

<a id="pdf-9d1751394783-p020-b002"></a>
<!-- pdf-source: page=20; block=2; confidence=0.85 -->
Theorem 10.35 is proved in two steps (Theorems 10.42 and 10.44).

<a id="pdf-9d1751394783-p020-b003"></a>
<!-- pdf-source: page=20; block=3; confidence=0.90 -->
**Theorem 10.42.** For $f\in L^2(\Omega^n,\pi^{\otimes n})$ and any $q\ge1$, with $x\sim\pi^{\otimes n}$ and $r\sim\{-1,1\}^n$: $\|T_{1/2}f(x)\|_{q,x}\le \|T_r f(x)\|_{q,r,x}$, i.e. $\|T_{1/2}f\|_q\le\|\tilde f\|_q$. $\tag{10.16}$

<a id="pdf-9d1751394783-p020-b004"></a>
<!-- pdf-source: page=20; block=4; confidence=0.80 -->
**Proof.** By induction from Lemma 10.15.

(i) One-input case: for $h\in L^2(\Omega,\pi)$, $\omega\sim\pi$, $b\sim\{-1,1\}$,
$$\|T_{1/2}h(\omega)\|_{q,\omega}\le\|T_b h(\omega)\|_{q,b,\omega}, \tag{10.17}$$
since $h^{=\{1\}}$ is mean-zero (Lemma 10.15; cf. proof of Corollary 10.20).

(ii) Single-coordinate case: for $g\in L^2(\Omega^n)$, $i\in[n]$,
$$\|T^i_{1/2}g\|_{q,x}\le\|T^i_{r_i}g\|_{q,r_i,x}. \tag{10.18}$$
With $i=1$, $x=(x_1,x')$, $x'=(x_2,\dots,x_n)$: $\|T^1_{1/2}g(x)\|_{q,x}=\big\|\,\|(T_{1/2}g|_{x'})(x_1)\|_{q,x_1}\big\|_{q,x'}$ (Exercise 10.10), then apply (10.17) with $h=g|_{x'}$.

(iii) First induction step: for distinct $i,j$, since $T^i_{\rho_i}$ and $T^j_{\rho_j}$ commute, applying (10.18) twice gives $\|T^j_{1/2}f\|_{q,x}\le\|T^i_{r_i}T^j_{1/2}f\|_{q,r_i,x}=\|T^j_{1/2}T^i_{r_i}f\|\le\|T^j_{r_j}T^i_{r_i}f\|_{q,r_i,r_j,x}$.

<a id="pdf-9d1751394783-p021-b001"></a>
<!-- pdf-source: page=21; block=1; confidence=0.85 -->
**Proof (continued).** Thus $\|T^i_{1/2}T^j_{1/2}f\|_{q,x}\le\|T^i_{r_i}T^j_{r_j}f\|_{q,r_i,r_j,x}$. Continuing the induction over all coordinates completes the proof. $\square$

<a id="pdf-9d1751394783-p021-b002"></a>
<!-- pdf-source: page=21; block=2; confidence=0.90 -->
**Lemma 10.43.** For $q\ge2$ there is a small enough $0<c_q\le1$ such that $\|a-c_q X\|_q\le\|a+X\|_q$ for every $a\in\mathbb{R}$ and every random variable $X$ with $\mathbb{E}[X]=0$ and $\|X\|_q<\infty$. In particular one may take $c_4=2/5$. (Used to establish the un-randomization/symmetrization direction of Theorem 10.35.)

<a id="pdf-9d1751394783-p021-b003"></a>
<!-- pdf-source: page=21; block=3; confidence=0.85 -->
**Proof.** Shown for $q=4$ (general $q$: Exercise 10.13). By homogeneity take $a=1$; raising to the 4th power, it suffices that $\mathbb{E}[(1-cX)^4]\le\mathbb{E}[(1+X)^4]$. Expanding and using $\mathbb{E}[X]=0$, this is equivalent to
$$\mathbb{E}\big[(1-c^4)X^4+(4+4c^3)X^3+(6-6c^2)X^2\big]\ge0. \tag{10.19}$$
It suffices to find $c$ with
$$(1-c^4)x^2+(4+4c^3)x+(6-6c^2)\ge0\quad\forall x\in\mathbb{R}, \tag{10.20}$$
since multiplying (10.20) by $x^2$ and taking expectations gives (10.19). The largest working $c$ is $\approx0.435$ (Exercise 10.14); to verify $c=2/5$ suffices, an elementary lower bound on the linear term reduces (10.20) to a manifestly nonnegative expression (e.g. a term $\tfrac{63}{250}\ge0$). $\square$

<a id="pdf-9d1751394783-p021-b004"></a>
<!-- pdf-source: page=21; block=4; confidence=0.85 -->
**Theorem 10.44.** For $f\in L^2(\Omega^n,\pi^{\otimes n})$ and any $q>1$, with $x\sim\pi^{\otimes n}$ and $r\sim\{-1,1\}^n$: $\|T_{c_q r}f(x)\|_{q,r,x}\le\|f(x)\|_{q,x}$, i.e. $\|T_{c_q}\tilde f\|_q\le\|f\|_q$, where $0<c_q\le1$ depends only on $q$; in particular one may take $c_4=c_{4/3}=2/5$.

<a id="pdf-9d1751394783-p022-b001"></a>
<!-- pdf-source: page=22; block=1; confidence=0.90 -->
**Proof.** Shows that for every outcome $r\in\{-1,1\}^n$, $\|T_{c_q r} f(x)\|_{q,x}\le\|f(x)\|_{q,x}$ for sufficiently small $c_q>0$, where the left side is $T^1_{\pm c_q}T^2_{\pm c_q}\cdots T^n_{\pm c_q}f(x)$. Since $T^i_\rho$ is a contraction in $L^q$ for any $\rho\ge 0$ (Exercise 8.11), it suffices to show each $T^i_{-c_q}$ is a contraction: $\|T^i_{-c_q} g(x)\|_{q,x}\le\|g(x)\|_{q,x}$ for all $g\in L^2(\Omega^n,\pi^{\otimes n})$ (10.21). As in the proof of Theorem 10.42, it suffices to prove $\|T_{-c_q} h\|_q\le\|h\|_q$ (10.22) for all one-input $h\in L^2(\Omega,\pi)$, since (10.21) then holds pointwise over the outcomes of $x_1,\dots,x_{i-1},x_{i+1},\dots,x_n$. By Proposition 9.19, proving (10.22) for one $q$ gives the same constant $c_q$ for the conjugate Hölder index $q'$, so one may restrict to $q\ge 2$. The result follows from Lemma 10.43 (taking $a=h^{=\varnothing}$ and $X=h^{=\{1\}}(x)$). $\square$

<a id="pdf-9d1751394783-p022-b002"></a>
<!-- pdf-source: page=22; block=2; confidence=0.98 -->
**10.5. Highlight: General sharp threshold theorems**

<a id="pdf-9d1751394783-p022-b003"></a>
<!-- pdf-source: page=22; block=3; confidence=0.90 -->
Recalls threshold phenomena (Ch. 8.4): for monotone $f:\{-1,1\}^n\to\{-1,1\}$, as $p$ increases from $0$ to $1$ one asks whether $\Pr_{x\sim\pi_p^{\otimes n}}[f(x)=1]$ has a sharp threshold jumping quickly from near $0$ to near $1$ around the critical probability $p=p_c$. The sharp threshold principle: this occurs (roughly) iff the total influence at the critical distribution $I[f^{(p_c)}]=\omega(1)$ (Exercise 8.28), motivating a characterization of functions with small total influence. For the uniform distribution, Friedgut's Junta Theorem gives one: $O(1)$ total influence $\Rightarrow$ close to an $O(1)$-junta; the general-product-space version (Sec 10.3) extends this to Boolean $f\in L^2(\{-1,1\}^n,\pi_p^{\otimes n})$ provided $p$ is not too close to $0$ or $1$. But for $p$ as small as $1/n^{\Theta(1)}$ the junta size promised may exceed $n$ (cf. breakdown of the Friedgut–Kalai result Theorem 10.29 for $p\le 1/n^{\Theta(1)}$); many natural graph properties (e.g. (non-)3-colorability) have $p=1/n^{\Theta(1)}$. The breakdown for very small $p$ traces to the dependence on the [continued next page].

<a id="pdf-9d1751394783-p023-b001"></a>
<!-- pdf-source: page=23; block=1; confidence=0.92 -->
The dependence is on the "$\lambda$" parameter in the General Hypercontractivity Theorem; more fundamentally, Friedgut's Junta Theorem is simply not true for such small $p$.

<a id="pdf-9d1751394783-p023-b002"></a>
<!-- pdf-source: page=23; block=2; confidence=0.90 -->
**Example 10.45.** Cases where Friedgut's Junta Theorem fails for small $p$:
- The logical OR $\mathrm{OR}_n:\{-1,1\}^n\to\{-1,1\}$ has critical probability $p_c\sim\tfrac{\ln 2}{n}$, and $I[\mathrm{OR}^{(p_c)}_n]\to 2\ln 2$, a small constant. Yet under the $p_c$-biased distribution $\mathrm{OR}_n$ is not $.1$-close to any junta on $o(n)$ coordinates (for every $o(n)$-junta $h$, $\Pr_{x\sim\pi_{p_c}^{\otimes n}}[f(x)\ne h(x)]>.1$).
- The $f:\{-1,1\}^n\to\{-1,1\}$ that is True ($-1$) iff there is a run of three consecutive $-1$'s (runs wrap around, making $f$ transitive-symmetric): $p_c=\Theta(1/n^{1/3})$; since $f$ is computable by a width-3 DNF, Exercise 8.26(b) gives $I[f^{(p_c)}]\le 12$; still $f$ is not close to any $o(n)$-junta under the $p_c$-biased distribution.
- Similarly $\mathrm{Clique}_3:\{\text{True,False}\}^{\binom{v}{2}}\to\{\text{True,False}\}$, the property of containing a triangle.

<a id="pdf-9d1751394783-p023-b003"></a>
<!-- pdf-source: page=23; block=3; confidence=0.93 -->
For very small $p$ one cannot hope that low-influence functions are close to juntas, but the counterexamples still have low complexity in a weaker sense: they are computable by narrow DNFs. Friedgut [Fri99] proposes this as a characterization.

<a id="pdf-9d1751394783-p023-b004"></a>
<!-- pdf-source: page=23; block=4; confidence=0.95 -->
**Friedgut's Conjecture.** There is a function $w:\mathbb{R}^+\times(0,1)\to\mathbb{R}^+$ such that: if $f:\{\text{True,False}\}^n\to\{\text{True,False}\}$ is monotone, $0<p\le 1/2$, and $I[f^{(p)}]\le K$, then $f$ is $\varepsilon$-close under $\pi_p^{\otimes n}$ to a monotone DNF of width at most $w(K,\varepsilon)$. Monotonicity is essential (Exercise 10.38).

<a id="pdf-9d1751394783-p023-b005"></a>
<!-- pdf-source: page=23; block=5; confidence=0.95 -->
**Friedgut's Sharp Threshold Theorem.** The above conjecture holds when $f$ is a graph property. This characterizes monotone graph properties of low total influence for arbitrarily small $p$.

<a id="pdf-9d1751394783-p023-b006"></a>
<!-- pdf-source: page=23; block=6; confidence=0.88 -->
Friedgut extended the result to monotone hypergraph properties, sufficient to show several hypergraph(-like) properties have sharp thresholds — e.g. the property of a random [continued next page].

<a id="pdf-9d1751394783-p024-b001"></a>
<!-- pdf-source: page=24; block=1; confidence=0.90 -->
Examples of sharp thresholds: a random 3-uniform hypergraph containing a perfect matching, and a random width-3 DNF being a tautology (for neither is $p_c$ known precisely, yet a sharp threshold exists around it). Roughly, at $p_c$ these properties cannot be well-approximated by narrow DNFs because they are almost surely not determined by "local" information; the deduction takes effort in random graph theory (Exercise 10.42; survey [Fri05]). Friedgut's proof is long and relies on $f$ being a graph/hypergraph property. Bourgain [Bou99] gave a shorter proof of an alternative characterization — weaker than Friedgut's for monotone graph properties, but valid for low-influence functions on any product probability space, with no monotonicity assumption (the domain need not be $\{\text{True,False}\}^n$).

<a id="pdf-9d1751394783-p024-b002"></a>
<!-- pdf-source: page=24; block=2; confidence=0.90 -->
**Definition 10.46.** Let $f\in L^2(\Omega^n,\pi^{\otimes n})$ be $\{-1,1\}$-valued. For $T\subseteq[n]$, $y\in\Omega^T$, and $\tau>0$, the restriction $y_T$ is a $\tau$-booster if $f^{\subseteq}_T(y)-\mathbf{E}[f]\ge\tau$, where $f^{\subseteq}_T(y)=\mathbf{E}[f_{T\to y}]$. For $\tau<0$, $y_T$ is a $\tau$-booster if $f^{\subseteq}_T(y)-\mathbf{E}[f]\le\tau$.

<a id="pdf-9d1751394783-p024-b003"></a>
<!-- pdf-source: page=24; block=3; confidence=0.93 -->
**Bourgain's Sharp Threshold Theorem.** Let $f\in L^2(\Omega^n,\pi^{\otimes n})$ be $\{-1,1\}$-valued with $I[f]\le K$ and $\mathrm{Var}[f]\ge .01$. Then there is some $\tau$ (positive or negative) with $|\tau|\ge\exp(-O(K^2))$ such that
$$\Pr_{x\sim\pi^{\otimes n}}\big[\exists\, T\subseteq[n],\ |T|\le O(K)\ \text{such that } x_T \text{ is a } \tau\text{-booster}\big]\ \ge\ |\tau|.$$
The constants hidden in $O(\cdot)$ are absolute and do not depend on $\Omega$ or $\pi$.

<a id="pdf-9d1751394783-p024-b004"></a>
<!-- pdf-source: page=24; block=4; confidence=0.90 -->
For $K$ an absolute constant, a typical input $x$ has a large chance of containing a constant-sized substring that is an $\Omega(1)$-booster for $f$. For monotone $f\in L^2(\{\text{True,False}\}^n,\pi_p^{\otimes n})$ with $p$ small, one deduces (Exercise 10.40) a $T$ with $|T|\le O(K)$ such that fixing all coordinates in $T$ to True increases $\Pr_{\pi_p^{\otimes n}}[f=\text{True}]$ by $\exp(-O(K^2))$. This is qualitatively weaker than Friedgut's theorem for a graph property with $I[f]=O(1)$ (where a width-$O(1)$ DNF term raises the probability up to almost $1$), but still suffices to deduce any sharp-threshold results obtainable from Friedgut's theorem [Fri05].

<a id="pdf-9d1751394783-p025-b001"></a>
<!-- pdf-source: page=25; block=1; confidence=0.90 -->
Continues §10.5. References Exercise 10.42 for how Bourgain's theorem applies to 3-colorability of random graphs. Notes that Hatami [Hat12] generalized Bourgain's work, giving a characterization of Boolean-valued functions of low total influence, stated next.

<a id="pdf-9d1751394783-p025-b002"></a>
<!-- pdf-source: page=25; block=2; confidence=0.90 -->
**Hatami's Theorem.** Let $f\in L^2(\Omega^n,\pi^{\otimes n})$ be a $\{-1,1\}$-valued function with $I[f]\le K$. Then for every $\varepsilon>0$, $f$ is $\varepsilon$-close (under $\pi^{\otimes n}$) to an $\exp(O(K^3/\varepsilon^3))$-"pseudo-junta" $h:\Omega^n\to\{-1,1\}$.

<a id="pdf-9d1751394783-p025-b003"></a>
<!-- pdf-source: page=25; block=3; confidence=0.90 -->
"Pseudo-junta" is defined in Exercise 10.39. A $K$-pseudo-junta $h$ satisfies $I[h]\le 4K$, so having $O(1)$ total influence is essentially equivalent to being an $O(1)$-pseudo-junta. Downside: being a $K$-pseudo-junta is not a syntactic property — it depends on $\pi^{\otimes n}$.

<a id="pdf-9d1751394783-p025-b004"></a>
<!-- pdf-source: page=25; block=4; confidence=0.86 -->
Bourgain's Sharp Threshold Theorem is a corollary of:

**Theorem 10.47.** Let $(\Omega,\pi)$ be a finite probability space and $f:\Omega^n\to\{-1,1\}$. Let $0<\varepsilon<1/2$ and write $k=I[f]/\varepsilon$. For each $x\in\Omega^n$ one can define a set of "notable coordinates" $J_x\subseteq[n]$ with $|J_x|\le\exp(O(k))$ such that
$$\operatorname*{E}_{x\sim\pi^{\otimes n}}\Big[\sum_{S\notin\mathcal F_x} f^{=S}(x)^2\Big]\le 2\varepsilon,$$
where $\mathcal F_x=\{S:S\subseteq J_x,\ |S|\le k\}$, a collection always satisfying $|\mathcal F_x|\le\exp(O(k^2))$.

<a id="pdf-9d1751394783-p025-b005"></a>
<!-- pdf-source: page=25; block=5; confidence=0.85 -->
Theorem 10.47 closely parallels Friedgut's Junta Theorem (Ch. 9.6) and Corollary 9.32. The only difference: in Friedgut's theorem the notable coordinates $J$ can be named in advance — the coordinates $j$ with $\mathrm{Inf}_j[f]=\sum_{S\ni j}\widehat f(S)^2$ large. In Theorem 10.47 the notable coordinates depend on $x$: they are the coordinates $j$ with $\sum_{S\ni j} f^{=S}(x)^2$ large. For $f:\{-1,1\}^n\to\{-1,1\}$ one has $f^{=S}(x)^2=\widehat f(S)^2$ for all $x$, so the definitions coincide; in the general product-space setting one must wait until $x$ is chosen. Example (ORn, Example 10.45): no notable coordinates in advance, but once $x$ is chosen the coordinates where $x$ is True (if any) are notable.

<a id="pdf-9d1751394783-p026-b001"></a>
<!-- pdf-source: page=26; block=1; confidence=0.85 -->
Proof of Theorem 10.47 mainly adds randomization/symmetrization to the proof of Friedgut's Junta Theorem (Theorem 9.28) to remove dependence on the minimum probability of $\pi$. The key inequalities being modified:
$$\|T_{1/\sqrt3}L_i f\|_2^2\le\|L_i f\|_{4/3}^2=\|L_i f\|_{4/3}^{2/3}\,\|L_i f\|_{4/3}^{4/3}\le\|L_i f\|_{4/3}^{2/3}\,\mathrm{Inf}_i[f],$$
last inequality by Exercise 8.10(b). An extra twist is needed because, working per-$x$ rather than in expectation, the set of notable coordinates can be improbably large (as in ORn under $\pi^{\otimes n}_{1/n}$); this is handled using that low-degree functions are "reasonable" together with randomization/symmetrization.

<a id="pdf-9d1751394783-p026-b002"></a>
<!-- pdf-source: page=26; block=2; confidence=0.90 -->
**Proof of Theorem 10.47.** By the Markov argument (Proposition 3.2),
$$\operatorname*{E}_{x\sim\pi^{\otimes n}}\Big[\sum_{|S|>k} f^{=S}(x)^2\Big]=\sum_{|S|>k}\|f^{=S}\|_2^2\le I[f]/k=\varepsilon.$$
Hence it suffices to define $J_x$ so that
$$\operatorname*{E}_{x\sim\pi^{\otimes n}}\Big[\sum_{|S|\le k,\ S\not\subseteq J_x} f^{=S}(x)^2\Big]\le\varepsilon.\quad(10.23)$$
Define near-working sets
$$J'_x=\Big\{j\in[n]:\sum_{S\ni j} f^{=S}(x)^2\ge\tau\Big\},\qquad \tau=c^{-k},$$
with $c>1$ a universal constant. The main effort is to show
$$\operatorname*{E}_{x\sim\pi^{\otimes n}}\Big[\sum_{|S|\le k,\ S\not\subseteq J'_x} f^{=S}(x)^2\Big]\le\varepsilon/2.\quad(10.24)$$
Problem: $J'_x$ need not satisfy $|J'_x|\le\exp(O(k))$, though in expectation it should not much exceed $1/\tau=c^k$. Introduce the event "$J'_x$ is too big" $\iff |J'_x|\ge C^k$ (with $C>c$ another universal constant), and define
$$J_x=\begin{cases}J'_x,&\text{if }J'_x\text{ is not too big},\\ \varnothing,&\text{if }J'_x\text{ is too big.}\end{cases}$$

<a id="pdf-9d1751394783-p027-b001"></a>
<!-- pdf-source: page=27; block=1; confidence=0.82 -->
The final part shows
$$\operatorname*{E}_{x\sim\pi^{\otimes n}}\Big[\mathbf 1[J^0_x\text{ is too big}]\cdot\sum_{0<|S|\le k} f^{=S}(x)^2\Big]\le\varepsilon/2.\quad(10.25)$$
Together (10.25) and (10.24) give (10.23). One proves (10.24) first, then (10.25); both could actually be bounded well below $\varepsilon/2$. To prove (10.24) one mimics the proof of Theorem 9.28 with added randomization/symmetrization, the key step being Lemma 10.48. The lemma also holds with the more natural choice $g=L_i f$; the extra $T_{2/5}$ is included to facilitate later un-randomization/symmetrization.

<a id="pdf-9d1751394783-p027-b002"></a>
<!-- pdf-source: page=27; block=2; confidence=0.85 -->
**Lemma 10.48.** Fix $x\in\Omega^n$ and $i\notin J^0_x$. Writing $g=T_{2/5}L_i f$,
$$\|T_{1/\sqrt3}\,\widetilde{g_x}\|_2^2\le\tau^{1/3}\,\|\widetilde{g_x}\|_{4/3}^{4/3},$$
where $\widetilde{g_x}$ is the randomization/symmetrization of $g$ (a function on the uniform hypercube).

<a id="pdf-9d1751394783-p027-b003"></a>
<!-- pdf-source: page=27; block=3; confidence=0.85 -->
**Proof.** $\widetilde{g_x}(r)$ is the randomization/symmetrization of $g$, a function on the uniform hypercube. By the basic $(4/3,2)$-Hypercontractivity Theorem,
$$\|T_{1/\sqrt3}\widetilde{g_x}\|_2^2\le\|\widetilde{g_x}\|_{4/3}^2=\big(\|\widetilde{g_x}\|_{4/3}^2\big)^{1/3}\|\widetilde{g_x}\|_{4/3}^{4/3}\le\big(\|\widetilde{g_x}\|_2^2\big)^{1/3}\|\widetilde{g_x}\|_{4/3}^{4/3}.$$
By Parseval,
$$\|\widetilde{g_x}\|_2^2=\sum_{S\subseteq[n]} g^{=S}(x)^2=\sum_{S\ni i}(2/5)^{2|S|} f^{=S}(x)^2\le\sum_{S\ni i} f^{=S}(x)^2\le\tau,$$
the last inequality because $i\notin J^0_x$. Combining yields $\|T_{1/\sqrt3}\widetilde{g_x}\|_2^2\le\tau^{1/3}\|\widetilde{g_x}\|_{4/3}^{4/3}$. $\square$

<a id="pdf-9d1751394783-p028-b001"></a>
<!-- pdf-source: page=28; block=1; confidence=0.85 -->
**Proof (cont.), establishing (10.24).** We have
$$\operatorname*{E}_x\Big[\sum_{|S|\le k,\ S\not\subseteq J'_x} f^{=S}(x)^2\Big]\le(5\sqrt3/2)^{2k}\operatorname*{E}_x\Big[\sum_{S\not\subseteq J'_x}(\mathrm T_{2/(5\sqrt3)}f^{=S})(x)^2\Big]$$
$$\le 20^k\operatorname*{E}_x\Big[\sum_{i\notin J'_x}\sum_{S\ni i}(\mathrm T_{2/(5\sqrt3)}f^{=S})(x)^2\Big]=20^k\operatorname*{E}_x\Big[\sum_{i\notin J'_x}\|\mathrm T_{1/\sqrt3}\widetilde{g^i}|_x\|_2^2\Big]\quad(\text{for }g^i=\mathrm T_{2/5}\mathrm L_i f)$$
$$\le 20^k\tau^{1/3}\operatorname*{E}_x\Big[\sum_{i\notin J'_x}\|\widetilde{g^i}|_x\|_{4/3}^{4/3}\Big]\le 20^k\tau^{1/3}\sum_{i=1}^n\|\mathrm L_i f\|_{4/3}^{4/3}\le 20^k\tau^{1/3}\sum_{i=1}^n\mathrm{Inf}_i[f]$$
$$=20^k\tau^{1/3}\,I[f]=(20c^{-1/3})^k k\varepsilon\le\varepsilon/2,$$
using Lemma 10.48, Theorem 10.35, and Exercise 8.10(b); the last inequality holds because $(20c^{-1/3})^k k\le 1/2$ for all $k\ge 0$ once $c$ is a large enough constant.

<a id="pdf-9d1751394783-p028-b002"></a>
<!-- pdf-source: page=28; block=2; confidence=0.88 -->
**Proof (cont.), establishing (10.25).** By Cauchy–Schwarz,
$$\operatorname*{E}_{x\sim\pi^{\otimes n}}\Big[\mathbf{1}[J'_x\text{ too big}]\cdot\sum_{0<|S|\le k}f^{=S}(x)^2\Big] \le \sqrt{\operatorname*{E}_x[\mathbf{1}[J'_x\text{ too big}]^2]}\cdot\sqrt{\operatorname*{E}_x\Big[\Big(\sum_{0<|S|\le k}f^{=S}(x)^2\Big)^2\Big]}\quad(10.26).$$
For the first factor, Markov's inequality gives
$$\operatorname*{E}_x[\mathbf{1}[J'_x\text{ too big}]^2] = \Pr_x[|J'_x|\ge C^k] \le C^{-k}\,\operatorname*{E}_x[|J'_x|] \le C^{-k} c^k\, I[f]\quad(10.27),$$
using $|J'_x| = \big(\sum_{i=1}^n \sum_{S\ni i} f^{=S}(x)^2\big)/\tau$ and $I[f]=\sum_i \mathrm{Inf}_i[f]$.

<a id="pdf-9d1751394783-p029-b001"></a>
<!-- pdf-source: page=29; block=1; confidence=0.88 -->
**Proof (cont.).** Let $h = \mathrm T_{2/5}(f - f^{=\varnothing})$. Then the second factor of (10.26) satisfies
$$\operatorname*{E}_x\Big[\Big(\sum_{0<|S|\le k}f^{=S}(x)^2\Big)^2\Big] \le (5/2)^{4k}\operatorname*{E}_x\Big[\Big(\sum_{S\ne\varnothing}(\mathrm T_{2/5}f^{=S})(x)^2\Big)^2\Big]=(5/2)^{4k}\operatorname*{E}_x[\|\tilde h|_x\|_2^4]$$
$$\le 40^k\operatorname*{E}_x[\|\tilde h|_x\|_4^4]\le 40^k\|f-f^{=\varnothing}\|_4^4\le 40^k\cdot 2^2\operatorname*{E}_x[(f-f^{=\varnothing})^2]=4\cdot 40^k\,\mathrm{Var}[f]\le 4\cdot 40^k\, I[f],\quad(10.28)$$
using Theorem 10.35 and $|f-f^{=\varnothing}|\le 2$ always.

<a id="pdf-9d1751394783-p029-b002"></a>
<!-- pdf-source: page=29; block=2; confidence=0.88 -->
**Proof (cont.).** Substituting (10.27) and (10.28) into (10.26) gives
$$\operatorname*{E}_{x\sim\pi^{\otimes n}}\Big[\mathbf{1}[J'_x\text{ too big}]\cdot\sum_{0<|S|\le k}f^{=S}(x)^2\Big] \le \sqrt{C^{-k}c^k\cdot 4\cdot 40^k}\cdot I[f] = 2\Big(\tfrac{40c}{C}\Big)^{k/2} k\varepsilon \le \varepsilon/2,$$
the last inequality holding for all $k\ge 0$ once $C$ is chosen large enough compared to $c$. $\square$

<a id="pdf-9d1751394783-p029-b003"></a>
<!-- pdf-source: page=29; block=3; confidence=0.90 -->
We end the chapter by deducing Bourgain's Sharp Threshold Theorem from Theorem 10.47.

<a id="pdf-9d1751394783-p029-b004"></a>
<!-- pdf-source: page=29; block=4; confidence=0.70 -->
**Proof of Bourgain's Sharp Threshold Theorem.** Take $\varepsilon = .001$ in Theorem 10.47, obtaining collections $\mathcal{F}_x$ with $|\mathcal{F}_x|\le \exp(O(K^2))$, each $S\in\mathcal{F}_x$ satisfying $|S|\le O(K)$. Using $\mathrm{Var}[f]\ge .99$ and $\widehat{f}{=}\varnothing(x)^2\le 1-.99$ for each $x$: $\mathbb{E}_{S\sim\pi^{\otimes n},\,S\in\mathcal{F}_x\setminus\{\varnothing\}}[\widehat{f}{=}S(x)^2] \ge 1 - 2\varepsilon - .99 = .008$. Since $|\mathcal{F}_x\setminus\{\varnothing\}|\le \exp(O(K^2))$ (assume it is $>0$), $\max_{S\in\mathcal{F}_x\setminus\{\varnothing\}}\widehat{f}{=}S(x)^2 \ge .008/\exp(O(K^2)) = \exp(-O(K^2))$. Hence for each $x$ define $S_x$ with $0<|S_x|\le O(K)$ so that $\mathbb{E}_{S\sim\pi^{\otimes n},x}[\widehat{f}{=}S_x(x)^2] \ge \exp(-O(K^2))$. By Exercise 8.19, $|\widehat{f}{=}S_x(x)|\le 2^{|S_x|} \le \exp(O(K))$, so $\widehat{f}{=}S_x(x)^2 \le \exp(O(K))$. It follows that $\Pr_{\pi^{\otimes n},x}[\widehat{f}{=}S_x(x)^2 \ge \exp(-O(K^2))] \ge \exp(-O(K^2))$ (10.29).

<a id="pdf-9d1751394783-p030-b001"></a>
<!-- pdf-source: page=30; block=1; confidence=0.80 -->
**Proof (cont.).** Complete the proof by showing that whenever $\widehat{f}{=}S_x(x)^2 \ge \exp(-O(K^2))$ occurs, there exists $T\subseteq S_x$ such that $x_T$ is a $\pm\exp(-O(K^2))$-booster for $f$; then a $\pm\exp(-O(K^2))$-booster exists with probability $\ge 1 - 2\exp(-O(K^2))$, completing the proof. Assume $\widehat{f}{=}S_x(x)^2 \ge \exp(-O(K^2))$, i.e. $|\widehat{f}{=}S_x(x)| \ge \exp(-O(K^2))$. Work with $g = f - \mathbb{E}[f]$; then $\widehat{g}{=}T = \widehat{f}{=}T$ for all $T\ne\varnothing$ and $\widehat{g}{=}\varnothing = 0$, so (since $S_x\ne\varnothing$) $\widehat{g}{=}S_x(x)=\widehat{f}{=}S_x(x)$ and $|\widehat{g}{=}S_x(x)| \ge \exp(-O(K^2))$. By the formula $\widehat{g}{=}S_x(x) = \sum_{\varnothing\ne T\subseteq S_x}(-1)^{|S_x|-|T|}\, g^{\subseteq T}(x)$ (the $T=\varnothing$ term is $0$) and since there are at most $2^{|S_x|}\le \exp(O(K))$ terms, there exists $T\subseteq S_x$ with $0<|T|\le O(K)$ such that $|g^{\subseteq T}(x)| \ge \exp(-O(K^2))/\exp(O(K)) = \exp(-O(K^2))$. But $g^{\subseteq T}(x) = f^{\subseteq T}(x) - \mathbb{E}[f]$, so $|f^{\subseteq T}(x) - \mathbb{E}[f]| \ge \exp(-O(K^2))$, meaning $x_T$ is a $\pm\exp(-O(K^2))$-booster. $\square$

<a id="pdf-9d1751394783-p030-b002"></a>
<!-- pdf-source: page=30; block=2; confidence=0.90 -->
For a relaxation of the assumption $\mathrm{Var}[f]\ge .01$ in this theorem, see Exercise 10.41.

<a id="pdf-9d1751394783-p030-b003"></a>
<!-- pdf-source: page=30; block=3; confidence=0.95 -->
## 10.6. Exercises and notes

<a id="pdf-9d1751394783-p030-b004"></a>
<!-- pdf-source: page=30; block=4; confidence=0.85 -->
**Exercise 10.1.** Let $X$ be a random variable and $1\le r\le\infty$. The triangle (Minkowski) inequality gives, for real-valued $f_1,f_2$: $\|f_1(X)+f_2(X)\|_r \le \|f_1(X)\|_r + \|f_2(X)\|_r$. More generally, for nonnegative reals $w_1,\dots,w_m$ and real functions $f_1,\dots,f_m$: $\|w_1 f_1(X)+\cdots+w_m f_m(X)\|_r \le w_1\|f_1(X)\|_r + \cdots + w_m\|f_m(X)\|_r$. Still more generally, if $Y$ is independent of $X$ and $f(X,Y)$ is measurable real-valued, then $\|\mathbb{E}_Y[f(X,Y)]\|_{r,X} \le \mathbb{E}_Y[\|f(X,Y)\|_{r,X}]$. Using this last fact, show that whenever $0<p\le q\le\infty$: $\big\|\,\|f(X,Y)\|_{q,X}\,\big\|_{p,Y} \le \big\|\,\|f(X,Y)\|_{p,Y}\,\big\|_{q,X}$. (Hint: raise the inequality to the power $p$ and use $r = q/p$.)

<a id="pdf-9d1751394783-p031-b001"></a>
<!-- pdf-source: page=31; block=1; confidence=0.98 -->
## 10.6. Exercises and notes

<a id="pdf-9d1751394783-p031-b002"></a>
<!-- pdf-source: page=31; block=2; confidence=0.55 -->
**Exercise 10.2.** Goal: prove Proposition 9.15 — if $X$ and $Y$ are independent $(p,q,\rho)$-hypercontractive random variables, then so is $X+Y$. Let $a,b \in \mathbb{R}$.

(a) Obtain $\lVert a + \rho b(X+Y)\rVert_{q,X,Y} \le \big\lVert\, \lVert a + \rho bX + bY\rVert_{p,Y}\,\big\rVert_{q,X}$.

(b) Upper-bound this by $\big\lVert\, \lVert a + \rho bX + bY\rVert_{q,X}\,\big\rVert_{p,Y}$ (Hint: Exercise 10.1).

(c) Upper-bound this by $\big\lVert\, \lVert a + bX + bY\rVert_{p,X}\,\big\rVert_{p,Y} = \lVert a + b(X+Y)\rVert_{p,X,Y}$.

<a id="pdf-9d1751394783-p031-b003"></a>
<!-- pdf-source: page=31; block=3; confidence=0.90 -->
**Exercise 10.2.** Goal: prove Proposition 9.15 — if $X$ and $Y$ are independent $(p,q,\rho)$-hypercontractive random variables, then so is $X+Y$. Let $a,b \in \mathbb{R}$.

(a) Obtain $\lVert a + \rho b(X+Y)\rVert_{q,X,Y} \le \big\lVert\, \lVert a + \rho bX + bY\rVert_{p,Y}\,\big\rVert_{q,X}$.

(b) Upper-bound this by $\big\lVert\, \lVert a + \rho bX + bY\rVert_{q,X}\,\big\rVert_{p,Y}$ (Hint: Exercise 10.1).

(c) Upper-bound this by $\big\lVert\, \lVert a + bX + bY\rVert_{p,X}\,\big\rVert_{p,Y} = \lVert a + b(X+Y)\rVert_{p,X,Y}$.

<a id="pdf-9d1751394783-p031-b004"></a>
<!-- pdf-source: page=31; block=4; confidence=0.85 -->
**Exercise 10.4.** Concerns a possible converse to Proposition 10.8.

(a) In the proof of the Two-Point Inequality, Proposition 9.19 was used to deduce that a uniform bit $x\sim\{-1,1\}$ is $(p,q,\rho)$-hypercontractive if it is $(q',p',\rho)$-hypercontractive. Explain why Proposition 9.19 cannot be used to deduce this for a general random variable $X$.

<a id="pdf-9d1751394783-p032-b001"></a>
<!-- pdf-source: page=32; block=1; confidence=0.85 -->
**Exercise 10.4 (cont.).** (b) For each $1<p<2$, exhibit a random variable $X$ that is $(p,2,\rho)$-hypercontractive (for some $\rho$) but not $(2,p',\rho)$-hypercontractive.

<a id="pdf-9d1751394783-p032-b002"></a>
<!-- pdf-source: page=32; block=2; confidence=0.70 -->
**Exercise 10.5.** (a) Regarding Remark 10.2, heuristically justify (as in Exercise 9.24(a)): if $A,B\subseteq\{-1,1\}^n$ are concentric Hamming balls with volumes $\exp(-a^2/2)$ and $\exp(-b^2/2)$ and $\rho a \le b$ (with $0\le\rho\le 1$), then
$$\Pr_{(x,y)\ \rho\text{-correlated}}[x\in A,\ y\in B] \;\approx\; \exp\!\left(-\tfrac12\cdot\frac{a^2 - 2\rho ab + b^2}{1-\rho^2}\right);$$
and further, if $b<\rho a$, then $\Pr[x\in A,\ y\in B]\sim\Pr[x\in A]$. Treat $\rho$ as fixed and $a,b\to\infty$.

(b) Similarly justify that the Reverse Small-Set Expansion Theorem is essentially sharp, using diametrically opposed Hamming balls.

<a id="pdf-9d1751394783-p032-b003"></a>
<!-- pdf-source: page=32; block=3; confidence=0.90 -->
**Exercise 10.6.** Goal (together with Exercise 10.7): prove the Reverse Hypercontractivity Theorem and its equivalent Two-Function version, stated below.

<a id="pdf-9d1751394783-p032-b004"></a>
<!-- pdf-source: page=32; block=4; confidence=0.94 -->
**Reverse Hypercontractivity Theorem.** Let $f:\{-1,1\}^n\to\mathbb{R}_{\ge 0}$ be nonnegative and let $-\infty\le q< p\le 1$. Then $\lVert T_\rho f\rVert_q \ge \lVert f\rVert_p$ for $0\le\rho\le \sqrt{(1-p)/(1-q)}$.

<a id="pdf-9d1751394783-p032-b005"></a>
<!-- pdf-source: page=32; block=5; confidence=0.93 -->
**Reverse Two-Function Hypercontractivity Theorem.** Let $f,g:\{-1,1\}^n\to\mathbb{R}_{\ge 0}$ be nonnegative, let $r,s\le 0$, and assume $0\le\rho\le\sqrt{rs}\le 1$. Then
$$\operatorname*{\mathbb{E}}_{(x,y)\ \rho\text{-correlated}}[f(x)g(y)] \;\ge\; \lVert f\rVert_{1+r}\,\lVert g\rVert_{1+s}.$$

<a id="pdf-9d1751394783-p032-b006"></a>
<!-- pdf-source: page=32; block=6; confidence=0.82 -->
**Norm conventions.** For $-\infty<p<0$ and positive $f\in L^2(\Omega,\pi)$, the "norm" $\lVert f\rVert_p$ retains the definition $\operatorname{E}[f^p]^{1/p}$; the cases $p=-\infty$, $p=0$, and nonnegative functions are defined by appropriate limits. In particular $\lVert f\rVert_{-\infty}$ is the minimum of $f$'s values, $\lVert f\rVert_0$ is the geometric mean of $f$'s values, and $\lVert f\rVert_p=0$ whenever $f$ is not everywhere positive. Define $p'$ by $1/p + 1/p' = 1$, with $0'=0$.

<a id="pdf-9d1751394783-p032-b007"></a>
<!-- pdf-source: page=32; block=7; confidence=0.80 -->
**Reverse Hölder inequality.** Let $f\in L^2(\Omega,\pi)$ be positive. Then for any $p<1$,
$$\lVert f\rVert_p = \inf\{\operatorname{E}[fg] : g>0,\ \lVert g\rVert_{p'} = 1\}.$$
In particular, for $r<0$ and positive $f,g$, $\operatorname{E}[fg] \ge \lVert f\rVert_{1+r}\,\lVert g\rVert_{1+1/r}$.

<a id="pdf-9d1751394783-p033-b001"></a>
<!-- pdf-source: page=33; block=1; confidence=0.85 -->
**Exercise 10.6 (cont.).** (a) Show that to prove the two Reverse Hypercontractivity Theorems it suffices to consider strictly positive $f,g:\{-1,1\}^n\to\mathbb{R}^+$.

(b) Show the Reverse Two-Function Hypercontractivity Theorem is equivalent (via the reverse Hölder inequality) to the Reverse Hypercontractivity Theorem.

(c) Reduce the Reverse Two-Function Hypercontractivity Theorem to the $n=1$ case (Hint: virtually identical to the Two-Function Hypercontractivity Induction), and further reduce to the Reverse Two-Point Inequality.

<a id="pdf-9d1751394783-p033-b002"></a>
<!-- pdf-source: page=33; block=2; confidence=0.62 -->
**Reverse Two-Point Inequality.** Let $-\infty\le p\le q\le 1$ and $0\le\rho\le (1-p)/(1-q)$. Then $\lVert T_\rho f\rVert_q \ge \lVert f\rVert_p$ for any $f:\{-1,1\}\to\mathbb{R}^+$.

<a id="pdf-9d1751394783-p033-b003"></a>
<!-- pdf-source: page=33; block=3; confidence=0.90 -->
**Exercise 10.7.** Goal: prove the Reverse Two-Point Inequality.

(a) Main effort: prove the inequality assuming $0<q<p\le1$ with $\rho=\sqrt{(1-p)/(1-q)}$, by mimicking the proof of the Two-Point Inequality. Hint: use $(1+t)^\theta \ge 1+\theta t$ for $\theta\ge 1$, and show that $(j-r)/\sqrt{1-r}$ is an increasing function of $r$ on $[0,1)$ for all $j\ge 2$.

(b) Extend to $0\le\rho\le \sqrt{(1-p)/(1-q)}$. Hint: use that $\lVert f\rVert_q \ge \lVert f\rVert_p$ for $-\infty\le p\le q\le\infty$ and nonnegative $f$; this generalization of Exercise 1.13 is proved by reducing negative $p,q$ to positive $p,q$.

(c) Establish the $q=-\infty$ case.

(d) Show that the cases $-\infty<q<p<0$ follow by "duality" (Hint: like Proposition 9.19 but with the reverse Hölder inequality).

(e) Show that the cases $q<0<p$ follow by the semigroup property of $T_\rho$.

(f) Treat the cases $p=0$ or $q=0$.

<a id="pdf-9d1751394783-p033-b004"></a>
<!-- pdf-source: page=33; block=4; confidence=0.85 -->
**Exercise 10.8.** Give a simple proof of the $n=1$ case of the Reverse Two-Function Hypercontractivity Theorem when $r=s=-1/2$ (Hint: replace $f,g$ by $f^2$ and $g^2$; then $f,g$ need not be assumed nonnegative). Can you also give a simple proof when $r=s=-2$?

<a id="pdf-9d1751394783-p033-b005"></a>
<!-- pdf-source: page=33; block=5; confidence=0.86 -->
**Exercise 10.9.** By selecting the negative values $r=-\rho\,\dfrac{\rho a+b}{a+\rho b}$ and $s=-\rho\,\dfrac{a+\rho b}{\rho a+b}$, prove the Reverse Small-Set Expansion Theorem of Remark 10.3. Hint: the negative norm of a 0-1 indicator is 0, so verify that no negative norms arise.

<a id="pdf-9d1751394783-p033-b006"></a>
<!-- pdf-source: page=33; block=6; confidence=0.60 -->
**Exercise 10.10.** Let $g\in L^2(\Omega^n,\pi^{\otimes n})$. Writing $x=(x_1,x')$ with $x'=(x_2,\dots,x_n)$, carefully justify the identity of one-input functions $(T_\rho g)|_{x'} = T_\rho(g|_{x'})$. Hint: refer to Exercise 8.21.

<a id="pdf-9d1751394783-p033-b007"></a>
<!-- pdf-source: page=33; block=7; confidence=0.95 -->
**Exercise 10.11.** Prove Proposition 10.12.

<a id="pdf-9d1751394783-p033-b008"></a>
<!-- pdf-source: page=33; block=8; confidence=0.95 -->
**Exercise 10.12.** Let $X$ be a random variable and $Y=X-X'$ its symmetrization, where $X'$ is an independent copy of $X$. Show that for any $t,\theta\in\mathbb{R}$, $\Pr[|Y|\ge t] \le 2\Pr[|X-\theta|\ge t/2]$.

<a id="pdf-9d1751394783-p034-b001"></a>
<!-- pdf-source: page=34; block=1; confidence=0.60 -->
# 10. Advanced hypercontractivity

(p. 316; continuation of the chapter's exercise set.)

<a id="pdf-9d1751394783-p034-b002"></a>
<!-- pdf-source: page=34; block=2; confidence=0.90 -->
**Exercise 10.13.** Goal: establish Lemma 10.43.

- **(a)** Show one may take $c_2 = 1$ (equality holds); henceforth assume $q > 2$.
- **(b)** Following the $q=4$ proof, reduce to showing there exists $0 < c_q < 1$ such that $|1-c_q x|^q + c_q q x - 1 \le |1+x|^q - qx - 1$ for all $x \in \mathbb{R}$.
- **(c)** Further reduce to showing there exists $0<c_q<1$ such that
$$\frac{|1-c_q x|^q + c_q q x - 1}{x^2} \le \frac{|1+x|^q - qx - 1}{x^2}\quad\forall x\in\mathbb{R}. \tag{10.31}$$
Also establish that both sides are continuous functions of $x\in\mathbb{R}$ once the value at $x=0$ is defined appropriately.
- **(d)** Show there exists $M>0$ such that for every $0<c_q<1/2$, (10.31) holds once $|x|\ge M$ (via the limit of both sides as $|x|\to\infty$).
- **(e)** Argue it suffices to show
$$\frac{|1+x|^q - qx - 1}{x^2}\ge\eta \tag{10.32}$$
for some universal positive constant $\eta>0$ — via a uniform-continuity argument over $(x,c_q)\in[-M,M]\times[0,\tfrac12]$.
- **(f)** Establish (10.32): the best possible $\eta$ is $1$; for merely some positive $\eta$, use Bernoulli's inequality to show $(|1+x|^q - qx - 1)/x^2$ is everywhere positive and tends to $\infty$ as $|x|\to\infty$.
- **(g)** Best asymptotic bound achievable for $c_q$; is $c_q\ge\Omega\!\big(\tfrac{\log q}{q}\big)$ possible?

<a id="pdf-9d1751394783-p034-b003"></a>
<!-- pdf-source: page=34; block=3; confidence=0.94 -->
**Exercise 10.14.** Show the largest $c$ for which inequality (10.20) holds is the smaller real root of $c^4 - 2c^3 - 2c + 1 = 0$, namely $c \approx 0.435$.

<a id="pdf-9d1751394783-p034-b004"></a>
<!-- pdf-source: page=34; block=4; confidence=0.90 -->
**Exercise 10.15.**

- **(a)** Show $1 + 6c^2 x^2 + c^4 x^4 \le 1 + 6x^2 + 4x^3 + x^4$ holds for all $x \in \mathbb{R}$ when $c = 1/2$. (Also for $c \approx 0.5269$?)
- **(b)** Show that if $X$ is a random variable with $\mathbb{E}[X] = 0$ and $\mathbb{E}[X^4] < \infty$, then $\lVert a + \tfrac12 r X \rVert_4 \le \lVert a + X \rVert_4$ for all $a \in \mathbb{R}$, where $r \sim \{-1,1\}$ is a uniformly random bit independent of $X$. (Cf. Lemma 10.15.)
- **(c)** Establish the following improvement of Theorem 10.44 for $q = 4$: for all $f \in L^2(\Omega^n, \pi^{\otimes n})$,
$$\big\lVert T_{\frac12 r} f(x) \big\rVert_{4,r,x} \le \lVert f(x) \rVert_{4,x},$$
where $x \sim \pi^{\otimes n}$ and $r \sim \{-1,1\}^n$.

<a id="pdf-9d1751394783-p034-b005"></a>
<!-- pdf-source: page=34; block=5; confidence=0.90 -->
**Exercise 10.16.** Complete the proof of Theorem 10.39. (Hint: rework Exercise 9.8 as in Lemma 10.38.)

<a id="pdf-9d1751394783-p034-b006"></a>
<!-- pdf-source: page=34; block=6; confidence=0.95 -->
**Exercise 10.17.** Prove Proposition 10.17.

<a id="pdf-9d1751394783-p035-b001"></a>
<!-- pdf-source: page=35; block=1; confidence=0.90 -->
## 10.6. Exercises and notes

<a id="pdf-9d1751394783-p035-b002"></a>
<!-- pdf-source: page=35; block=2; confidence=0.80 -->
**Exercise 10.18.** Recall from (10.5), for fixed $q > 2$ and $\lambda \in (0, 1/2)$, the function
$$\rho = \rho(\lambda) = \sqrt{\frac{\exp(u/q) - \exp(-u/q)}{\exp(u/q') - \exp(-u/q')}} = \sqrt{\frac{\sinh(u/q)}{\sinh(u/q')}},$$
where $u = u(\lambda)$ is defined by $\exp(-u) = \lambda/(1-\lambda)$.

- **(a)** Show $\rho$ is increasing in $\lambda$. (Hint chain: reduce to $\rho^2$ decreasing in $u\in(0,\infty)$; to $q\tanh(u/q)$ increasing in $q\in(1,\infty)$; to $\tanh(r)/r$ decreasing in $r \in (0,\infty)$; to $\sinh(2r) \ge 2r$ for $r \ge 0$.)
- **(b)** Verify the Remark 10.19 statements: for fixed $q$, as $\lambda \to 1/2$, $\rho \to 1/\sqrt{q-1}$; as $\lambda \to 0$, $\rho \sim \lambda^{1/2 - 1/q}$. Also show: for fixed $\lambda$, as $q \to \infty$, $\rho \sim \sqrt{u/\sinh u}\,\sqrt{1/q}$, and $\sqrt{u/\sinh u} \sim \sqrt{2\lambda \ln(1/\lambda)}$ for $\lambda \to 0$.
- **(c)** Show that $\rho \ge \frac{1}{\sqrt{q-1}}\,\lambda^{1/2 - 1/q}$ holds for all $\lambda$.

<a id="pdf-9d1751394783-p035-b003"></a>
<!-- pdf-source: page=35; block=3; confidence=0.70 -->
**Exercise 10.19.** Let $(\Omega, \pi)$ be a finite probability space with $|\Omega| \ge 2$ in which every outcome has probability at least $\lambda$. Let $1 < p < 2$ and $0 < \rho \le 1$. Goal: prove Wolff's result [Wol07] that, subject to $\lVert f \rVert_p = 1$, every $f \in L^2(\Omega, \pi)$ minimizing $\lVert T_\rho f \rVert_2$ takes on at most two values (and a minimizer exists).

- **(a)** Consider the equivalent problem of minimizing $F(f) = \lVert T_\rho f \rVert_2^2$ subject to $G(f) = \lVert f \rVert_p^p = 1$. Show $F$ and $G$ are $C^1$ functionals (identifying $f$ with points in $\mathbb{R}^\Omega$).
- **(b)** Argue from continuity that the minimum is attained; write $f_0$ for any minimizer; goal is to show $f_0$ takes at most two values.
- **(c)** Show $f_0$ is everywhere nonnegative or everywhere nonpositive (Hint: by homogeneity, equivalent to maximizing $\lVert T_\rho f \rVert_2$ subject to $\lVert f \rVert_p = 1$; use Exercise 2.34). Replacing $f_0$ by $|f_0|$, assume $f_0 \ge 0$.
- **(d)** Show $\nabla F(f_0) = 2\,T_{\rho^2} f_0$ and $\nabla G(f_0) = p\, f_0^{\,p-1} \cdot \pi$, where $\pi \cdot g$ is the pointwise product with $\pi$ regarded as a function $\Omega \to \mathbb{R}_{\ge 0}$ (Hint: $F(f) = \langle T_{\rho^2} f, f\rangle$).

<a id="pdf-9d1751394783-p036-b001"></a>
<!-- pdf-source: page=36; block=1; confidence=0.75 -->
**Exercise 10.19 (continued).**

- **(e)** By Lagrange multipliers, show $T_{\rho^2} f_0 = c\, f_0^{\,p-1}$ for some $c \in \mathbb{R}^+$ (Hint: note $\nabla G(f_0) \ne 0$).
- **(f)** Writing $\mu = \mathbb{E}[f_0]$, argue each value $y = f_0(\omega)$ satisfies
$$c\, y^{p-1} - \rho^2 y = (1 - \rho^2)\mu. \tag{10.33}$$
- **(g)** Show (10.33) has at most two solutions for $y \in \mathbb{R}^+$, completing the proof that $f_0$ takes at most two values (Hint: strict concavity of $y^{p-1}$).
- **(h)** Suppose $q > 2$. By modifying the argument, show that subject to $\lVert T_\rho g \rVert_2 = 1$, every $g \in L^2(\Omega, \pi)$ maximizing $\lVert g \rVert_q$ takes at most two values (and a maximizer exists) (Hint: substitute $g = T_\rho f$; $g$ is two-valued if $f$ is).

<a id="pdf-9d1751394783-p036-b002"></a>
<!-- pdf-source: page=36; block=2; confidence=0.82 -->
**Exercise 10.20.** Fix $1 < p < 2$ and $0 < \lambda < 1/2$. Let $\Omega = \{-1,1\}$ and $\pi = \pi_\lambda$ with $\pi(-1) = \lambda$, $\pi(1) = 1-\lambda$. Goal: show the Latała–Oleszkiewicz result [LO00] that the largest $\rho$ for which $\lVert T_\rho f \rVert_2 \le \lVert f \rVert_p$ holds for all $f \in L^2(\Omega,\pi)$ is as in Theorem 10.18; it satisfies
$$\rho^2 = r^* = \frac{\exp(u/p') - \exp(-u/p')}{\exp(u/p) - \exp(-u/p)}, \tag{10.34}$$
where $u$ is defined by $\exp(-u) = \lambda/(1-\lambda)$. (Here we are using $p = q'$ to facilitate the proof; the $(2,q)$-hypercontractivity statement then follows via Proposition 9.19.)

- **(a)** With $\alpha = \lambda^{1/p}$, $\beta = (1-\lambda)^{1/p}$, show that $r^* = \dfrac{\alpha^p\beta^{2-p} - \alpha^{2-p}\beta^p}{\alpha^2 - \beta^2}$.
- **(b)** For $f \in L^2(\Omega,\pi)$ with $\mu = \mathbb{E}[f]$ and $\delta = D_1 f = \hat f(1)$, show
$$\mu^2 + \delta^2 r^* = \lVert T_{\sqrt{r^*}} f \rVert_2^2 \le \lVert f \rVert_p^2, \tag{10.35}$$
and exhibit a nonconstant $f$ making it sharp (showing no larger $\rho$ is possible).
- **(c)** Show WLOG one may take $f(-1) = (1+y)/\alpha$, $f(1) = (1-y)/\beta$ for some $-1 < y < 1$ (Hint: Exercise 2.34 plus continuity to assume $f > 0$, then homogeneity of (10.35)).

<a id="pdf-9d1751394783-p037-b001"></a>
<!-- pdf-source: page=37; block=1; confidence=0.95 -->
## 10.6. Exercises and notes (book p. 319)

<a id="pdf-9d1751394783-p037-b002"></a>
<!-- pdf-source: page=37; block=2; confidence=0.82 -->
**Exercise 10.20 (continued), parts (d)–(j).** Analysis of inequality (10.35) in the $\alpha,\beta$ notation, recalling Definition 8.44 that $\delta^2 = \lambda(1-\lambda)(f(1)-f(-1))^2 = \alpha^p\beta^p(f(1)-f(-1))^2$.

- **(d)** LHS(10.35) is a quadratic in $y$; show the chosen $r^*$ makes the linear term vanish, so $\mathrm{LHS}(10.35)=A y^2 + C$ for constants $A,C$.
- **(e)** Compute $A = 2\,\dfrac{\beta^{p-1}-\alpha^{p-1}}{\beta-\alpha}$ (10.36). Hint: multiply the expression by $\alpha^p+\beta^p=1$.
- **(f)** Show $\mathrm{RHS}(10.35) = ((1+y)^p + (1-y)^p)^{2/p}$, and argue it suffices to prove (10.35) only for $0\le y<1$.
- **(g)** Let $y^*=\dfrac{\beta-\alpha}{\beta+\alpha}>0$; show that if $y=-y^*$, then $f$ is a constant function and both sides of (10.35) equal $\dfrac{4}{(\alpha+\beta)^2}$.
- **(h)** Deduce both sides of (10.35) equal $\dfrac{4}{(\alpha+\beta)^2}$ for $y=y^*$; after scaling this gives the sharp nonconstant function $f(x)=\exp(-x\,u/p)$.
- **(i)** Write $y=\sqrt z$, $0\le z<1$; we have reduced to showing $Az+C\le((1+\sqrt z)^p+(1-\sqrt z)^p)^{2/p}$, with both sides equal when $\sqrt z=y^*$. Calling the right side $\varphi(z)$, show $\frac{d}{dz}\varphi(z)\big|_{\sqrt z=y^*}=A$ (using $\alpha^p+\beta^p=1$ and $\varphi=\tfrac{4}{(\alpha+\beta)^2}$ at $\sqrt z=y^*$). The proof then reduces to convexity of $\varphi$ on $[0,1)$.
- **(j)** Show $\varphi$ is convex on $[0,1)$ by showing its derivative is nondecreasing; hint: the Generalized Binomial Theorem with $1<p<2$ gives $(1+\sqrt z)^p+(1-\sqrt z)^p=\sum_{j\ge 0} b_j z^j$ with every $b_j>0$.

<a id="pdf-9d1751394783-p037-b003"></a>
<!-- pdf-source: page=37; block=3; confidence=0.90 -->
**Exercise 10.21.** Complete the proof of Theorem 10.18. Hint: besides Exercises 10.19 and 10.20, use Exercise 10.18(a).

<a id="pdf-9d1751394783-p037-b004"></a>
<!-- pdf-source: page=37; block=4; confidence=0.90 -->
**Exercise 10.22.** (a) Define $\Phi:[0,\infty)\to\mathbb{R}$ by $\Phi(x)=x\ln x$, with $0\ln 0=0$; verify $\Phi$ is smooth and strictly convex. (b) [Introduces the entropy definition continued on the next page.]

<a id="pdf-9d1751394783-p038-b001"></a>
<!-- pdf-source: page=38; block=1; confidence=0.95 -->
## 10. Advanced hypercontractivity (book p. 320)

<a id="pdf-9d1751394783-p038-b002"></a>
<!-- pdf-source: page=38; block=2; confidence=0.90 -->
**Definition 10.49.** For a nonnegative $g\in L^2(\Omega,\pi)$, the entropy of $g$ is $\mathrm{Ent}[g]=\mathbf{E}_{x\sim\pi}[\Phi(g(x))]-\Phi\big(\mathbf{E}_{x\sim\pi}[g(x)]\big)$, where $\Phi(x)=x\ln x$.

<a id="pdf-9d1751394783-p038-b003"></a>
<!-- pdf-source: page=38; block=3; confidence=0.90 -->
**Exercise 10.22 (continued).** (b) Verify $\mathrm{Ent}[g]\ge 0$ always, that $\mathrm{Ent}[g]=0$ iff $g$ is constant, and $\mathrm{Ent}[cg]=c\,\mathrm{Ent}[g]$ for any constant $c\ge 0$. (c) For a probability density $\phi$ on $\{-1,1\}^n$ (Def. 1.20), show $\mathrm{Ent}[\phi]=D_{\mathrm{KL}}(\phi\,\|\,\pi_{1/2}^{\otimes n})$, the Kullback–Leibler divergence of the uniform distribution from $\phi$ (more precisely, the distribution with density $\phi$).

<a id="pdf-9d1751394783-p038-b004"></a>
<!-- pdf-source: page=38; block=4; confidence=0.92 -->
**The Log-Sobolev Inequality.** For $f:\{-1,1\}^n\to\mathbb{R}$, $\tfrac{1}{2}\mathrm{Ent}[f^2]\le \mathbf{I}[f]$.

<a id="pdf-9d1751394783-p038-b005"></a>
<!-- pdf-source: page=38; block=5; confidence=0.90 -->
**Exercise 10.23, parts (a)–(c)** (establishing the Log-Sobolev Inequality).

- **(a)** Writing $\rho=e^{-t}$, the $(p,2)$-Hypercontractivity Theorem gives $\|\mathrm{T}_{e^{-t}}f\|_2^2\le \|f\|_{1+\exp(-2t)}^2$ for all $t\ge 0$; call these $\mathrm{LHS}(t),\mathrm{RHS}(t)$. They are smooth on $[0,\infty)$ with $\mathrm{LHS}(0)=\mathrm{RHS}(0)$; deduce $\mathrm{LHS}'(0)\le \mathrm{RHS}'(0)$.
- **(b)** Compute $\mathrm{LHS}'(0)=-2\mathbf{I}[f]$ (via the Fourier representation; cf. Ex. 2.18).
- **(c)** Compute $\mathrm{RHS}'(0)=-\mathrm{Ent}[f^2]$, thereby deducing the inequality. Hint: set $F(t)=\mathbf{E}[|f|^{1+\exp(-2t)}]$ and show that $\mathrm{RHS}'(0)=F(0)\ln F(0)+F'(0)$.

<a id="pdf-9d1751394783-p038-b006"></a>
<!-- pdf-source: page=38; block=6; confidence=0.85 -->
**Exercise 10.24.** (a) For $f:\{-1,1\}^n\to\mathbb{R}$, show $\mathrm{Ent}[(1+\varepsilon f)^2]\sim 2\,\mathrm{Var}[f]\,\varepsilon^2$ as $\varepsilon\to 0$. (b) Deduce the Poincaré Inequality for $f$ from the Log-Sobolev Inequality.

<a id="pdf-9d1751394783-p038-b007"></a>
<!-- pdf-source: page=38; block=7; confidence=0.88 -->
**Exercise 10.25.** (a) From the Log-Sobolev Inequality, for $f:\{-1,1\}^n\to\{-1,1\}$ with $\alpha=\min\{\Pr[f=1],\Pr[f=-1]\}$: $2\alpha\ln(1/\alpha)\le \mathbf{I}[f]$ (10.37); this is off by a factor $\ln 2$ from the optimal edge-isoperimetric inequality (Thm 2.39). Hint: apply to $\tfrac12+\tfrac12 f$ or $\tfrac12-\tfrac12 f$. (b) Give a more streamlined direct derivation of (10.37) by differentiating the Small-Set Expansion Theorem.

<a id="pdf-9d1751394783-p038-b008"></a>
<!-- pdf-source: page=38; block=8; confidence=0.82 -->
**Exercise 10.26** (a direct proof of the Log-Sobolev Inequality). (a) First establish the $n=1$ case: show one may assume $f:\{-1,1\}\to\mathbb{R}$ is nonnegative with mean $1$ (hints: Ex. 2.14, Ex. 10.22(b)). (b) It then remains to establish $\tfrac12\mathrm{Ent}[(1+bx)^2]\le b^2$ for $b\in[-1,1]$; show $g(b)=b^2-\tfrac12\mathrm{Ent}[(1+bx)^2]$ is smooth on $[-1,1]$ and satisfies $g(0)=\dots$ [continued on next page].

<a id="pdf-9d1751394783-p039-b001"></a>
<!-- pdf-source: page=39; block=1; confidence=0.95 -->
## 10.6. Exercises and notes (book p. 321)

<a id="pdf-9d1751394783-p039-b002"></a>
<!-- pdf-source: page=39; block=2; confidence=0.88 -->
**Exercise 10.26 (continued).** (b, cont.) $g(0)=0$, $g'(0)=0$, and $g''(b)=\dfrac{2b^2}{1+b^2}+\ln\dfrac{1+b^2}{1-b^2}\ge 0$ for $b\in(-1,1)$; explain why this completes the $n=1$ case. (c) For any two functions $f_+,f_-:\{-1,1\}^n\to\mathbb{R}$, $\left(\dfrac{\sqrt{\mathbf{E}[f_+^2]}-\sqrt{\mathbf{E}[f_-^2]}}{2}\right)^2\le \mathbf{E}\!\left[\left(\dfrac{f_+-f_-}{2}\right)^2\right]$ (hint: triangle inequality for $\|\cdot\|_2$). (d) Prove the Log-Sobolev Inequality by "induction by restrictions" (§9.4): for the RHS establish $\mathbf{I}[f]=\mathbf{E}[((f_+-f_-)/2)^2]+\tfrac12\mathbf{I}[f_+]+\tfrac12\mathbf{I}[f_-]$; for the LHS apply induction, then the $n=1$ base case, then part (c).

<a id="pdf-9d1751394783-p039-b003"></a>
<!-- pdf-source: page=39; block=3; confidence=0.72 -->
**Log-Sobolev Inequality for general product space domains.** For $f\in L^2(\Omega^n,\pi^{\otimes n})$, write $\lambda=\min(\pi)$, $\lambda_0=1-\lambda$, and $u$ via $\exp(-u)=\lambda/\lambda_0$. Then $\tfrac12\,\varrho\,\mathrm{Ent}[f^2]\le \mathbf{I}[f]$, where $\varrho=\varrho(\lambda)=\dfrac{\lambda_0-\lambda}{\ln\lambda_0-\ln\lambda}$ (also expressible via a $\tfrac{\tanh(u/2)}{u/2}$ form).

<a id="pdf-9d1751394783-p039-b004"></a>
<!-- pdf-source: page=39; block=4; confidence=0.80 -->
**Exercise 10.27, parts (a)–(c).** (a) Establish the general product-space Log-Sobolev Inequality above by following the strategy of Ex. 10.23. (b) Show $\varrho(\lambda)\sim 2/\ln(1/\lambda)$ as $\lambda\to 0$. (c) For $f:\{-1,1\}^n\to\{-1,1\}$ under the $p$-biased distribution $\pi_p^{\otimes n}$, with $q=1-p$ and $\alpha=\min\{\Pr_{\pi_p}[f=1],\Pr_{\pi_p}[f=-1]\}$: $4\cdot\dfrac{q-p}{\ln q-\ln p}\cdot\alpha\ln(1/\alpha)\le \mathbf{I}[f^{(p)}]$, and hence as $p\to 0$, $\alpha\log_p\alpha\le (1+o_p(1))\,p\cdot\mathbf{E}_{x\sim\pi_p^{\otimes n}}[\mathrm{sens}_f(x)]$ (10.38). Remark: (10.38) is known to hold without the $o_p(1)$ for all $p\le 1/2$.

<a id="pdf-9d1751394783-p039-b005"></a>
<!-- pdf-source: page=39; block=5; confidence=0.90 -->
**Exercise 10.28.** Prove Theorem 10.21 (hint: recall Proposition 8.28).

<a id="pdf-9d1751394783-p039-b006"></a>
<!-- pdf-source: page=39; block=6; confidence=0.85 -->
**Exercise 10.29.** Let $X_1,\dots,X_n$ be independent $(2,q,\rho)$-hypercontractive random variables and $F(x)=\sum_{|S|\le k}\widehat{F}(S)\,x^S$ an $n$-variate multilinear polynomial of degree at most $k$. Show $\|F(X_1,\dots,X_n)\|_q\le (1/\rho)^k\,\|F(X_1,\dots,X_n)\|_2$ (hint: use Ex. 10.3).

<a id="pdf-9d1751394783-p039-b007"></a>
<!-- pdf-source: page=39; block=7; confidence=0.92 -->
**Exercise 10.30.** Let $0<\lambda\le1/2$ and let $(\Omega,\pi)$ be a finite probability space in which some outcome $\omega_0$ has $\pi(\omega_0)=\lambda$ (e.g. $\Omega=\{-1,1\}$, $\pi=\pi_\lambda$). Define $f\in L^2(\Omega,\pi)$ by $f(\omega_0)=1$, $f(\omega)=0$ for $\omega\ne\omega_0$. For $q\ge2$, compute $\|f\|_q/\|f\|_2=\lambda^{1/q-1/2}$ and deduce (in light of the proof of Theorem 10.21) that Corollary 10.20 cannot hold for $\rho>\lambda^{1/2-1/q}$.

<a id="pdf-9d1751394783-p040-b001"></a>
<!-- pdf-source: page=40; block=1; confidence=0.90 -->
# 10. Advanced hypercontractivity

(Running header, book page 322; exercises section continues.)

<a id="pdf-9d1751394783-p040-b002"></a>
<!-- pdf-source: page=40; block=2; confidence=0.93 -->
**Exercise 10.31.** Prove Theorem 10.22.

**Exercise 10.32.** Prove Theorem 10.23.

**Exercise 10.33.** Prove Theorem 10.24. (Hint: immediately worsen $q-1$ to $q$ so that finding the optimal choice of $q$ is easier.)

**Exercise 10.34.** Prove Theorem 10.25.

**Exercise 10.35.** Prove Friedgut's Junta Theorem for general product spaces as stated in Section 10.3.

**Exercise 10.36.** Show that (10.9) implies $F(p_c+\eta p_c)\ge 1-\epsilon$ in the proof of Theorem 10.29. (Hint: consider $\tfrac{d}{dp}\ln(1-F(p))$.)

**Exercise 10.37.** Justify the various calculations and observations in Example 10.45.

<a id="pdf-9d1751394783-p040-b003"></a>
<!-- pdf-source: page=40; block=3; confidence=0.90 -->
**Exercise 10.38.** (a) Let $p=\tfrac1n$ and let $f\in L^2(\{-1,1\}^n,\pi_p^{\otimes n})$ be any Boolean-valued function. Show that $I[f]\le 4$. (Hint: Proposition 8.45.)

(b) Specialize to $f=\chi_{[n]}$. Show $f$ is not $.1$-close to any width-$O(1)$ DNF (under the $\tfrac1n$-biased distribution, for $n$ sufficiently large), demonstrating that monotonicity cannot be removed from Friedgut's Conjecture. (Hint: fixing any constant number of coordinates cannot change the bias of $\chi_{[n]}$ much.)

<a id="pdf-9d1751394783-p040-b004"></a>
<!-- pdf-source: page=40; block=4; confidence=0.85 -->
**Definition (Exercise 10.39, pseudo-junta).** A function $h:\Omega^n\to\Sigma$ is a *pseudo-junta* if there are juntas $f_1,\dots,f_m:\Omega^n\to\{\text{True},\text{False}\}$ with domains $J_1,\dots,J_m\subseteq[n]$, and $g:(\Omega\cup\{*\})^n\to\Sigma$ (with $*\notin\Omega$ a new symbol), such that for each $x\in\Omega^n$, $h(x)=g(y)$ where
$$y_j=\begin{cases}x_j & \text{if } j\in J_i \text{ for some } i \text{ with } f_i(x)=\text{True},\\ * & \text{else.}\end{cases}$$
Interpretation: each junta $f_i$ decides whether coordinates in its domain are "notable"; $h(x)$ depends only on the set of notable coordinates. For a distribution $\pi$ on $\Omega$, the pseudo-junta has *width $k$* under $\pi^{\otimes n}$ if $\mathbb{E}_{x\sim\pi^{\otimes n}}[\#\{j: y_j\neq *\}]\le k$ (expected number of notable coordinates $\le k$); such $h$ is a $k$-pseudo-junta.

**To show:** if a $k$-pseudo-junta $h\in L^2(\Omega^n,\pi^{\otimes n})$ is $\{-1,1\}$-valued then $I[f]\le 4k$. (Hint: use the second statement of Proposition 8.24; consider notable coordinates for both $x$ and $x'=(x_1,\dots,x_{i-1},x_i',x_{i+1},\dots,x_n)$.)

<a id="pdf-9d1751394783-p040-b005"></a>
<!-- pdf-source: page=40; block=5; confidence=0.55 -->
**Exercise 10.40.** Establish a further consequence of Bourgain's Sharp Threshold Theorem. Let $f:\{\text{True},\text{False}\}^n\to\{\text{True},\text{False}\}$ be monotone with $I[f^{(p)}]\le K$. Assume $\mathrm{Var}[f]\ge .01$ and $0<p\le \exp(-cK^2)$, where $c$ is a large universal constant. Then there exists $T\subseteq[n]$ with $|T|\le O(K)$ such that
$$\Pr_{x\sim\pi_p^{\otimes n}}[\,f(x)=\text{True}\mid x_i=\text{True}\ \forall i\in T\,]\ \ge\ \Pr_{x\sim\pi_p^{\otimes n}}[f(x)=\text{True}]\cdot\exp(+O(K^2)).$$
(Hint: the theorem yields a booster toward True or False; the True case is easy, and to rule out False use $p\cdot|T|\ll\exp(-O(K^2))$.)

<a id="pdf-9d1751394783-p041-b001"></a>
<!-- pdf-source: page=41; block=1; confidence=0.85 -->
## 10.6. Exercises and notes

(Running header, book page 323.)

<a id="pdf-9d1751394783-p041-b002"></a>
<!-- pdf-source: page=41; block=2; confidence=0.85 -->
**Exercise 10.41.** Suppose in Bourgain's Sharp Threshold Theorem we drop the assumption $\mathrm{Var}[f]\ge .01$ (assume at least that $f$ is nonconstant). Show there is some $\tau$ with $|\tau|\ge \mathrm{stddev}[f]\cdot\exp\!\big(-O(I[f]^2/\mathrm{Var}[f]^2)\big)$ such that
$$\Pr_{x\sim\pi_p^{\otimes n}}\big[\,\exists\, T\subseteq[n],\ |T|\le O(I[f]/\mathrm{Var}[f])\ \text{such that } x_T \text{ is a } \tau\text{-booster}\,\big]\ \ge\ |\tau|.$$
(Cf. Exercise 9.32.)

<a id="pdf-9d1751394783-p041-b003"></a>
<!-- pdf-source: page=41; block=3; confidence=0.85 -->
**Exercise 10.42.** Beginnings of using Bourgain's Sharp Threshold Theorem for sharp thresholds of monotone properties, via $\neg\mathrm{3Col}$: a random $v$-vertex graph $G\sim\mathcal G(v,p)$ being non-3-colorable.

(a) Prove the critical probability satisfies $p_c\le O(1/v)$; i.e., there is a universal constant $C$ with $\Pr[G\sim\mathcal G(v,C/v)\text{ is 3-colorable}]=o_n(1)$. (Hint: union-bound over all potential 3-colorings.)

(b) Toward a sharp threshold: if the property had constant total influence at $p_c$, Bourgain's Theorem gives a constant-magnitude $\tau$ so that for $G\sim\mathcal G(v,p_c)$ there is a $|\tau|$ chance $G$ contains a $\tau$-boosting induced subgraph $G_T$. The boost toward 3-colorability is ruled out (a few missing edges barely help; cf. Ex. 10.40); local witnesses to non-3-colorability (e.g. a 4-clique boosts probability to 1) are very unlikely at $p_c$. As a partial step, prove the expected number of 4-cliques in $G\sim\mathcal G(v,p)$ is $o_v(1)$ unless $p=\Omega(v^{-2/3})$ (i.e. $p\gg p_c$).

<a id="pdf-9d1751394783-p042-b001"></a>
<!-- pdf-source: page=42; block=1; confidence=0.90 -->
### Notes

<a id="pdf-9d1751394783-p042-b002"></a>
<!-- pdf-source: page=42; block=2; confidence=0.88 -->
**Notes.** The standard template (Bonami [Bon70]) for the Hypercontractivity Theorem for $\pm1$ bits: prove the Two-Point Inequality, then induct (Exercise 10.3). Bonami's original proof reduced to the $1\le p\le q\le 2$ case (with more cumbersome calculus); the text follows Janson's [Jan97] proof of the Two-Point Inequality. An alternative derives it from the Log-Sobolev Inequality (Exercise 10.23), as done by Gross [Gro75].

The use of two-function hypercontractivity for an inductive proof (avoiding Exercise 10.1) follows the communication/coding viewpoint of Ahlswede–Gács [AG76] (inspired also by [MOR+06], [BBH+12], [KOTZ16]). Ahlswede–Gács connected hypercontractivity with small-set expansion in general product spaces and independently obtained the sharp Hypercontractivity Theorem for $\pm1$ bits, relying partly on Witsenhausen [Wit75].

<a id="pdf-9d1751394783-p042-b003"></a>
<!-- pdf-source: page=42; block=3; confidence=0.88 -->
**Notes (cont.).** The Generalized Small-Set Expansion Theorem is modeled on the Reverse Small-Set Expansion Theorem, first proved by Mossel et al. [MOR+06]. The Reverse Hypercontractivity Inequality is due to Borell [Bor82]; Exercises 10.6–10.9 follow [MOR+06]. It holds with no change in constants for every product probability space; see Mossel–Oleszkiewicz–Sen [MOS12].

The definition of a hypercontractive random variable is due to Krakowiak–Szulga [KS88]; basic facts of Section 10.2 (and Exercise 10.2) come from that work and Borell [Bor84] (also [KW92, Jan97, Szu98, MOO10]). The main (biased-bits) part of Theorem 10.18 is essentially from Latała–Oleszkiewicz [LO00] (see also Oleszkiewicz [Ole03]); Exercise 10.20 fleshes out their computations without new ideas. Earlier works [BKK+92, Tal94, FK96, Fri98] established forms of the General Hypercontractivity Theorem for $\lambda$-biased bits, yielding KKL-type theorems with correct asymptotic dependence on $\lambda$. The sharp Log-Sobolev Inequality for product spaces (Exercise 10.27) was derived independently of Latała–Oleszkiewicz by Higuchi–Yoshida [HY95] (without proof), Diaconis–Saloff-Coste [DSC96] (with proof), and possibly Rothaus (see [BL98]).

<a id="pdf-9d1751394783-p043-b001"></a>
<!-- pdf-source: page=43; block=1; confidence=0.95 -->
# 10.6. Exercises and notes

<a id="pdf-9d1751394783-p043-b002"></a>
<!-- pdf-source: page=43; block=2; confidence=0.92 -->
Historical/attribution notes. Open point: for the uniform $\pm 1$ setting, no known derivation of Latała–Oleszkiewicz's optimal biased hypercontractive inequality from the optimal biased Log-Sobolev inequality. Randomization/symmetrization trick for random variables credited to Kahane [Kah68]. All of Section 10.4 due to Bourgain [Bou79] (proof of Lemma 10.43 slightly different here). The constant $C_q$ in Theorem 10.39 is given without explicit dependence; Kwapień [Kwa10] showed one may take $C_{q'} = C_q = O(q/\log q)$ for $q \ge 2$. Proof of Bourgain's Theorem 10.47 follows [Bou99] (and [Bal13]).

<a id="pdf-9d1751394783-p043-b003"></a>
<!-- pdf-source: page=43; block=3; confidence=0.88 -->
The biased edge-isoperimetric inequality (10.38) from Exercise 10.27 was proved by induction on $n$, without the additional $o_p(1)$ error term, by Russo [Rus82] and independently by Kahn–Kalai [KK07]. This work and [Rus81] contain the germ of the idea that monotone functions with small influences have sharp thresholds.

<a id="pdf-9d1751394783-p043-b004"></a>
<!-- pdf-source: page=43; block=4; confidence=0.88 -->
On the sharp threshold for 3-colorability (Exercise 10.42): Alon–Spencer [AS08] give an elementary proof that at the critical probability for 3-colorability, every subgraph on $\varepsilon v$ vertices is 3-colorable, for some universal $\varepsilon > 0$. Existence of a sharp threshold for $k$-colorability proven by Achlioptas–Friedgut [AF99]; location essentially determined by Achlioptas–Naor [AN05].
