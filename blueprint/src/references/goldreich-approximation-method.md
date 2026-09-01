<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: 988dc9f0ae91c3a654cefe58b04f061cb2562d93b3d95f61835c530796c7992e -->

<a id="pdf-988dc9f0ae91-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.97 -->
**Title.** "On teaching the approximation method for circuit lower bounds" by Oded Goldreich (Weizmann Institute), March 15, 2023.

**Abstract.** Expository presentation of Razborov's approximation method (1987) and Smolensky's application (1987) giving lower bounds on the size of AC0[p]-circuits computing sums mod q, for primes q ≠ p. Provides a detailed exposition of both the special case q = 2 and the general case; recommends teaching only q = 2 and leaving q > 2 for advanced reading.

<a id="pdf-988dc9f0ae91-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.95 -->
Table of contents: (1) Introduction; (2) Basic material — 2.1 Overview, 2.2 the theorem and its proof; (3) Advanced reading — 3.1 case q < p, 3.2 case q > p; (4) Beyond recommended reading — 4.1 case q < p, 4.2 case q > p; Appendix on low-degree polynomials and approximating Majority; Acknowledgements; Bibliography. Footnote: partial support by ISF grant 1041/18 and ERC grant 819702.

<a id="pdf-988dc9f0ae91-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.93 -->
# 1 Introduction

Positions the Razborov–Smolensky lower bound for AC0[p]-circuits computing sums mod q (primes q ≠ p) as a celebrated circuit-complexity result whose standard textbook treatments cover only q = 2. Audience: graduate students assumed familiar with Boolean circuits (depth, fan-in) and the P-vs-NP problem. Key structural claim: proving the lower bound has two steps — (1) AC0[p]-circuit computation can be well-approximated by low-degree polynomials over GF(p); (2) summation mod q cannot be well-approximated by low-degree polynomials over GF(p). Step (1) is intuitive (Section 2.1, Lemma 2); Step (2) is Lemma 3 for q = 2 and Section 3 for general q; Section 2.2 also derives a Majority lower bound by reducing modular sums to it. Section 4 gives an alternative, more complicated proof of the general case.

<a id="pdf-988dc9f0ae91-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.93 -->
# 2 The basic material

States the central discrepancy underlying the approximation method: low-degree polynomials over a small prime field GF(p) can well-approximate functions computed by constant-depth unbounded-fan-in Boolean circuits, but cannot well-approximate the sum modulo q for any prime q ≠ p. Conclusion: constant-depth unbounded-fan-in circuits cannot compute such modular sums; this holds even when circuits are equipped with unbounded-fan-in MOD p gates.

<a id="pdf-988dc9f0ae91-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.90 -->
Notes that degree-n polynomials over GF(2) can compute any n-variate Boolean function, but the number of low-degree n-variate polynomials is far smaller than the number of n-variate Boolean functions. Approximation (rather than exact computation) is necessary because no low-degree polynomial can perfectly agree with even simple functions such as the n-wide AND/OR. Hence one studies the class of functions well-approximated by low-degree polynomials, which contains all constant-depth unbounded-fan-in circuit functions but excludes simple functions like Majority and MOD q (q ≠ field size). Footnotes: (1) DNF terms of size n become products of linear factors, e.g. x1 ∧ ¬x2 ∧ x3 = x1·(1−x2)·x3; (2) number of degree-d monomials over n variables is C(n,d); (3) a nonzero degree-d polynomial over GF(2) evaluates to 1 with probability ≥ 2^(−d).

<a id="pdf-988dc9f0ae91-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.90 -->
## 2.1 Overview

**Key claim (Eq. (1)).** An unbounded-fan-in OR-gate is well-approximated by a low-degree polynomial over GF(2): for every distribution D over {0,1}^w there exists a degree-ℓ polynomial P : GF(2)^w → GF(2) with

Pr_{(y_1,…,y_w)∼D}[ P(y_1,…,y_w) = OR(y_1,…,y_w) ] ≥ 1 − 2^(−ℓ).   (1)

The degree ℓ is logarithmic in the reciprocal of the error bound and independent of the number of variables w; the claim holds for any distribution D, which is crucial for replacing intermediate gates in a circuit.

**Proof idea.** For every (y_1,…,y_w) ∈ {0,1}^w \ {0^w}, a random linear function L : GF(2)^ℓ→GF(2) satisfies Pr_L[L(y)=1] = 1/2, while L(0,…,0)=0 for all linear L. Hence for every y ∈ {0,1}^w, with random linear functions L_1,…,L_ℓ,

Pr[ OR(L_1(y),…,L_ℓ(y)) = OR(y) ] ≥ 1 − 2^(−ℓ).

Thus there exist fixed linear functions L_1,…,L_ℓ achieving Pr_{y∼D}[OR(L_1(y),…,L_ℓ(y)) = OR(y)] ≥ 1 − 2^(−ℓ). Replacing OR(z_1,…,z_ℓ) by 1 − ∏_{j∈[ℓ]}(1−z_j) yields Eq. (1): define P(y) := 1 − ∏_{j∈[ℓ]}(1 − L_j(y)). A similar idea can be applied in GF(p), for any prime p, but in that case we raise the linear functions to the power p−1 in order to guarantee an answer in {0,1}, so the degree of the polynomial is (p−1)·ℓ. Footnote 4: under the uniform distribution one may directly use OR(y_1,…,y_ℓ) as approximator and replace it by 1 − ∏_{j∈[ℓ]}(1−y_j).

<a id="pdf-988dc9f0ae91-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.85 -->
Raising linear functions to the power $p-1$ forces outputs into $\{0,1\}$, giving polynomial degree $(p-1)\cdot\ell$. Replacing all OR/AND gates of a depth-$d$, size-$s$ circuit yields a degree $d\cdot(p-1)\cdot\ell$ polynomial over $\mathrm{GF}(p)$ approximating the circuit with error $\le s\cdot 2^{-\ell}$, even with unbounded fan-in $\mathrm{MOD}\,p$ gates (detailed in Lemma 2). Conversely, low-degree polynomials cannot approximate $\mathrm{MOD}\,q$ ($q\ne p$ prime) with such small error: the $q=2$ case is Lemma 3, the general case Section 3.

<a id="pdf-988dc9f0ae91-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.98 -->
## 2.2 The actual theorem and its proof

<a id="pdf-988dc9f0ae91-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.90 -->
Circuit lower bounds are meaningful only for explicit functions; "explicit" is undetermined but typically means polynomial-time (sometimes log-space) computable. Here the focus is size lower bounds for very explicit functions such as Majority and Parity.

<a id="pdf-988dc9f0ae91-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.95 -->
**Definition (AC0[m]).** $\mathrm{AC}^0[m]$ is the class of Boolean functions computable by polynomial-size, constant-depth circuit families with unbounded fan-in AND, OR, NOT, and $\mathrm{MOD}_m$ gates, where $m>1$ is a constant. The gate satisfies $\mathrm{MOD}_m(x_1,\dots,x_w)=0$ iff $\sum_{i\in[w]} x_i \equiv 0 \pmod m$, and $=1$ otherwise (i.e. when $\sum_{i\in[w]} x_i \bmod m \in \{1,\dots,m-1\}$). In particular $\mathrm{MOD}_2 = \mathrm{XOR} = \text{Parity}$. Attention is restricted to prime $m$; composite $m$ (even $m=6$) is open, except prime powers.

<a id="pdf-988dc9f0ae91-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.88 -->
The following result shows that for any prime $p$, $\mathrm{AC}^0[p]$ cannot compute simple "counting-flavored" functions such as Majority or $\mathrm{MOD}_q$ with $q\ne p$; notably, this statement is actually provable (unlike the analogous $\mathrm{AC}^0[6]$/Majority conjecture).

<a id="pdf-988dc9f0ae91-p004-b006"></a>
<!-- pdf-source: page=4; block=6; confidence=0.90 -->
**Footnote.** For every prime power $p^e$, $\mathrm{AC}^0[p^e]=\mathrm{AC}^0[p]$, since $\mathrm{MOD}_{p^e}$ is computable in $\mathrm{AC}^0[p]$ and $\mathrm{MOD}_p$ in $\mathrm{AC}^0[p^e]$ (by duplicating each input $p^{e-1}$ times). Construction of $\mathrm{MOD}_{p^e}$ from $\mathrm{MOD}_{p^{e-1}}$ and $\mathrm{MOD}_p$ gates:
- For $i\in[n]$, set $y_i=\mathrm{MOD}_{p^{e-1}}(x_1,\dots,x_i)$. Then $(y_{i-1},y_i)=(1,0)$ iff $\sum_{j\in[i-1]} x_j \equiv -1 \pmod{p^{e-1}}$ and $x_i=1$, so $|\{i\in\{2,\dots,n\}:(y_{i-1},y_i)=(1,0)\}| = \lfloor \sum_{i\in[n]} x_i / p^{e-1}\rfloor$.
- For $i\in\{2,\dots,n\}$, set $z_i=\mathrm{AND}(y_{i-1},\neg y_i)$. Then $\sum_{i\in[n]} x_i = p^{e-1}\cdot\big(\sum_{i\in\{2,\dots,n\}} z_i\big) + \big(\sum_{i\in[n]} x_i \bmod p\big)$.

Hence $\mathrm{MOD}_{p^e}(x)=0$ iff both $\mathrm{MOD}_p(z)=0$ and $\mathrm{MOD}_p(x)=0$.

<a id="pdf-988dc9f0ae91-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.90 -->
This statement can be proved, in contrast to the equally intuitive but open conjecture that $\mathrm{AC}^0[6]$ cannot compute Majority.

<a id="pdf-988dc9f0ae91-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.95 -->
**Theorem 1** (size lower bounds for constant-depth circuits with AND, OR, NOT, $\mathrm{MOD}_p$ gates, $p$ prime). For any prime $p\ge 2$:
1. Computing the majority of $n$ bits by a depth-$d$ circuit with unbounded fan-in AND, OR, NOT, $\mathrm{MOD}_p$ gates requires size $\exp(\Omega(n^{1/2d}))$.
2. For any prime $q\ne p$, computing $\mathrm{MOD}_q$ of $n$ bits by such a depth-$d$ circuit requires size $\exp(\Omega(n^{1/2d}))$.

In particular, Part 1 with $p=2$ gives $\mathrm{AC}^0[2]$ cannot compute Majority; Part 2 with $p=3,q=2$ gives $\mathrm{AC}^0[3]$ (hence $\mathrm{AC}^0$) cannot compute Parity; generally Part 2 gives $\mathrm{AC}^0[p]$ cannot compute $\mathrm{MOD}_q$ for $q\ne p$.

<a id="pdf-988dc9f0ae91-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.90 -->
The focus is Part 2, which implies a weaker but sufficient version of Part 1 (the $\mathrm{MOD}_q$ lower bound yields a Majority lower bound). The proof of Theorem 1 combines two steps.

<a id="pdf-988dc9f0ae91-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.92 -->
**Step 1.** Computation by $\mathrm{AC}^0[p]$ circuits is well-approximated by low-degree polynomials over $\mathrm{GF}(p)$. Proved in Lemma 2 (extending the $p=2$ overview).

<a id="pdf-988dc9f0ae91-p005-b005"></a>
<!-- pdf-source: page=5; block=5; confidence=0.92 -->
**Step 2.** The target functions ($n$-wise Majority and $n$-wise $\mathrm{MOD}_q$, $q\ne p$) cannot be well-approximated by low-degree polynomials over $\mathrm{GF}(p)$. Proved in Lemma 3 for $\mathrm{MOD}_2$ and any fixed prime $p\ne 2$; the general case $\mathrm{MOD}_q$ for fixed primes $q\ne p$ is in Section 3.

<a id="pdf-988dc9f0ae91-p005-b006"></a>
<!-- pdf-source: page=5; block=6; confidence=0.93 -->
**Lemma 2** (approximating $\mathrm{AC}^0[p]$ by low-degree polynomials over $\mathrm{GF}(p)$). For any prime $p\ge 2$, let $C:\{0,1\}^n\to\{0,1\}$ be a depth-$d$, size-$s$ circuit with unbounded fan-in AND, OR, NOT, $\mathrm{MOD}_p$ gates. Then there exists a degree-$D$ polynomial $A$ over $\mathrm{GF}(p)$ such that
$$\Pr_{x\in\{0,1\}^n}[A(x)=C(x)] > 1 - \frac{s}{\exp(\Omega(D^{1/d}))},$$
where the $\Omega$ hides a factor $\frac{\log p}{p-1}$. Setting $D=\sqrt{n}$ and $s=\exp(\Omega(n^{1/2d}))$ gives approximation error $o(1)$. (Later: degree-$\sqrt{n}$ polynomials over $\mathrm{GF}(p)$ have error rate $\Omega(1)$ against $\mathrm{MOD}_q$ for any fixed prime $q\ne p$.)

<a id="pdf-988dc9f0ae91-p005-b007"></a>
<!-- pdf-source: page=5; block=7; confidence=0.92 -->
**Proof.** By induction on the structure of $C$, with all arithmetic in $\mathrm{GF}(p)$. Let $g$ be the function computed by the top (output) gate; four cases are considered by gate type.

<a id="pdf-988dc9f0ae91-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.93 -->
**Case 1 (NOT gate).** If $g=\neg f$, approximate by $\tilde g := 1-\tilde f$, where $\tilde f$ approximates $f$. Then $\tilde g$ has the same degree as $\tilde f$, $\tilde g(x)\in\{0,1\}$ whenever $\tilde f(x)\in\{0,1\}$, and if $\tilde f(x)=f(x)$ then $\tilde g(x)=g(x)$. This replacement adds no approximation error.

<a id="pdf-988dc9f0ae91-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.92 -->
**Case 2 ($\mathrm{MOD}_p$ gate).** If $g=\mathrm{MOD}_p(f_1,\dots,f_w)$, approximate by $\tilde g := \big(\sum_{i\in[w]} \tilde f_i\big)^{p-1}$. Then $\deg(\tilde g)=(p-1)\cdot\max_{i\in[w]}\deg(\tilde f_i)$ and $\tilde g(x)\in\{0,1\}$ for all $x\in\{0,1\}^n$. If $\tilde f_i(x)=f_i(x)$ for all $i$, then $\tilde g(x)=\big(\sum_{i\in[w]} f_i(x)\big)^{p-1}=\mathrm{MOD}_p(f_1(x),\dots,f_w(x))$, using $v^{p-1}=1$ for $v\in\mathrm{GF}(p)\setminus\{0\}$ and $0^{p-1}=0$. No approximation error is added.

<a id="pdf-988dc9f0ae91-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.90 -->
**Case 3 (OR gate).** If $g=\mathrm{OR}(f_1,\dots,f_w)$, use linear functions $L_j:\mathrm{GF}(p)^w\to\mathrm{GF}(p)$, $j=1,\dots,\ell$ ($\ell$ a free parameter), and approximate by
$$\tilde g := 1 - \prod_{j\in[\ell]}\big(1 - L_j(\tilde f_1,\dots,\tilde f_w)^{p-1}\big).$$
Then $\deg(\tilde g)=\ell\cdot(p-1)\cdot\max_{i\in[w]}\deg(\tilde f_i)$, and $1-\prod_{j\in[\ell]}(1-L_j(v)^{p-1})\in\{0,1\}$ for all $v\in\mathrm{GF}(p)^w$, so $\tilde g(x)\in\{0,1\}$. The choice of the $L_j$ is the key issue, guided by Claim 2.1.

<a id="pdf-988dc9f0ae91-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.90 -->
**Claim 2.1** (random linear combination of elements of a non-zero sequence). If $v_1,\dots,v_w\in\{0,1\}$ with $\mathrm{OR}(v_1,\dots,v_w)=1$, then for a random linear $L:\mathrm{GF}(p)^w\to\mathrm{GF}(p)$, $\Pr_L[L(v_1,\dots,v_w)=0]=1/p$.

**Proof.** A random linear $L(z_1,\dots,z_w)=\sum_{i\in[w]} r_i z_i$ with $r_i$ uniform and independent, evaluated at any non-zero point, is uniformly distributed in $\mathrm{GF}(p)$.

<a id="pdf-988dc9f0ae91-p006-b005"></a>
<!-- pdf-source: page=6; block=5; confidence=0.85 -->
Selecting $L_1,\dots,L_\ell$ uniformly at random, for every $x\in\{0,1\}^n$ with $\tilde f_i(x)\in\{0,1\}$ for all $i$:
- If $\tilde f_1(x)=\cdots=\tilde f_w(x)=0$, all $L_j$ evaluate to $0$, so $\prod_{j\in[\ell]}(1-L_j^{p-1})$ is identically $1$.
- If $\tilde f_i(x)=1$ for some $i$, each $L_j$ evaluates to $0$ with probability $1/p$ (so each factor $1-L_j^{p-1}=1$ with probability $1/p$), hence the product $\prod_{j\in[\ell]}(1-L_j^{p-1})=1$ with probability $p^{-\ell}$.

<a id="pdf-988dc9f0ae91-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.88 -->
**Proof (cont.).** Since $1-\prod_{j\in[\ell]}(1-L_j^{\,p-1})\in\{0,1\}$ always, over random linear $L_1,\dots,L_w$:
$$\Pr_{L_1,\dots,L_w}\Big[\mathrm{OR}(\tilde f_1(x),\dots,\tilde f_w(x))\neq 1-\prod_{j\in[\ell]}\big(1-L_j(\tilde f_1(x),\dots,\tilde f_w(x))^{p-1}\big)\Big]\le p^{-\ell}.\qquad(2)$$
By an averaging argument there exist linear $L_1,\dots,L_\ell:\mathrm{GF}(p)^w\to\mathrm{GF}(p)$ such that for uniform $x\in\{0,1\}^n$ the same inequality holds:
$$\Pr_{x}\Big[\mathrm{OR}(\tilde f_1(x),\dots)\neq 1-\prod_{j\in[\ell]}\big(1-L_j(\dots)^{p-1}\big)\Big]\le p^{-\ell}.\qquad(3)$$
Hence replacing the OR-gate output $\mathrm{OR}(\tilde f_1(x),\dots,\tilde f_w(x))$ by $\tilde g$ adds approximation error $\le p^{-\ell}$.

<a id="pdf-988dc9f0ae91-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.85 -->
**Case 4 (top gate is AND).** If $g=\mathrm{AND}(f_1,\dots,f_w)$, approximate by $\tilde g \overset{\text{def}}{=}\prod_{j\in[\ell]}\big(1-L_j(1-\tilde f_1,\dots,1-\tilde f_w)^{p-1}\big)$, where $\tilde f_i$ approximates $f_i$ and the $L_j$ are suitable linear functions, obtained via $g=\neg\mathrm{OR}(\neg f_1,\dots,\neg f_w)$ (footnote 6). This replacement also adds approximation error $\le p^{-\ell}$.

<a id="pdf-988dc9f0ae91-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.90 -->
Replacing each gate by its polynomial adds error $\le p^{-\ell}$; replacing all $s$ gates yields total approximation error $\le s\cdot p^{-\ell}$. The degree of the resulting polynomial approximating circuit $C$ is at most $((p-1)\cdot\ell)^d$. Requiring $((p-1)\ell)^d\le D$, set $\ell=\tfrac{1}{p-1}\cdot D^{1/d}$, giving approximation error $s\cdot p^{-D^{1/d}/(p-1)}$.

<a id="pdf-988dc9f0ae91-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.90 -->
**Digest.** Key fact (Claim 2.1): a random linear function is positively correlated with an OR-gate (a weaker result follows using random 0–1 linear functions). Eq. (3) upper-bounds the error of replacing one OR-gate by a suitable degree-$(p-1)\ell$ polynomial; a union bound over all gates (with adequate $\ell$) gives Lemma 2. Raising $\mathrm{GF}(p)$-expressions to the power $p-1$ guarantees the resulting polynomial takes values in $\{0,1\}$.

<a id="pdf-988dc9f0ae91-p007-b005"></a>
<!-- pdf-source: page=7; block=5; confidence=0.90 -->
**Proving Part 1 of Theorem 1.** Part 2 (lower bound for $\mathrm{MOD}_q$) is proved by combining Lemma 2 with the fact that a degree-$\sqrt n$ polynomial over $\mathrm{GF}(p)$ cannot approximate the $n$-bit $\mathrm{MOD}_q$ function. Part 1 (lower bound for Majority) is provable analogously (see Appendix); a weaker version is shown here by noting any symmetric function (e.g. Parity $=\mathrm{MOD}_2$) $\mathrm{AC}^0$-reduces to Majority. Define $\mathrm{TH}^n_k:\{0,1\}^n\to\{0,1\}$ to return 1 iff the input has at least $k$ ones; then $\mathrm{TH}^n_k(x)=\mathrm{TH}^{2n+1}_{n+1}(x\,1^{n+1-k}0^k)$, and $\mathrm{TH}^{2n+1}_{n+1}$ is the $(2n+1)$-bit Majority. With $\mathrm{wt}(x_1,\dots,x_n)\overset{\text{def}}{=}|\{i\in[n]:x_i=1\}|$, suppose for some $S\subseteq[n]$ a function $f:\{0,1\}^n\to\{0,1\}$ satisfies $f(x)=1$ iff $\mathrm{wt}(x)\in S$ (continued p.8).

<a id="pdf-988dc9f0ae91-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.85 -->
For $S=\{s_1,\dots,s_m\}$, $f(x)=\bigvee_{i\in[m]}\mathrm{AND}\big(\mathrm{TH}^n_{s_i}(x),\,\neg\mathrm{TH}^n_{s_i+1}(x)\big)$, since $\mathrm{AND}(\mathrm{TH}^n_s,\neg\mathrm{TH}^n_{s+1})=1$ iff $\mathrm{wt}(x)=s$. Hence a size lower bound for depth-$(d+3)$ $\mathrm{AC}^0[p]$-circuits computing $f$ (e.g. $f=\mathrm{MOD}_2$) yields a size lower bound for depth-$d$ $\mathrm{AC}^0[p]$-circuits computing Majority; using specifics of the reduction, a depth-$d$ lower bound for $f$ yields a depth-$d$ lower bound for Majority. (Footnote 7: $f(x)=\sum_{i\in[m]}\mathrm{TH}^n_{s_i}(x)\cdot(1-\mathrm{TH}^n_{s_i+1}(x))$ over $\mathrm{GF}(p)$; such a depth-$(d+3)$ circuit is approximated by a polynomial of degree twice that of the depth-$d$ circuit computing $\mathrm{TH}^n_s$.)

<a id="pdf-988dc9f0ae91-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.93 -->
**Proving a special case of Part 2 of Theorem 1.** The case $q=2$ (lower bound for $\mathrm{MOD}_q$) is proved by combining Lemma 2 with Lemma 3 below.

<a id="pdf-988dc9f0ae91-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.90 -->
**Lemma 3.** There exists a constant $\epsilon>0$ such that for any prime $p\ge 3$, any $n$-variate polynomial $Q:\mathrm{GF}(p)^n\to\mathrm{GF}(p)$ of degree at most $\sqrt n$ fails to compute $n$-ary parity on at least $\epsilon\cdot 2^n$ of the $n$-bit inputs; that is, $\Pr_{x\in\{0,1\}^n}[Q(x)\neq\mathrm{MOD}_2(x)]\ge\epsilon$. For any constant $\delta>0$ the claim holds (with a different $\epsilon>0$) for degree $\delta\cdot\sqrt n$: for $\delta<1$, $\epsilon=0.5-O(\delta)$; for $\delta>1$, $\epsilon=\exp(-O(\delta^2))$; it also holds for non-constant $\delta$.

<a id="pdf-988dc9f0ae91-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.90 -->
The special case $q=2$ of Part 2 follows by suitable parameters in Lemma 2: in contrast to Lemma 3, this setting implies that for sufficiently small $c>0$, depth-$d$ size-$\exp(c\cdot n^{1/2d})$ $\mathrm{AC}^0[p]$-circuits can be approximated by degree-$\sqrt n$ polynomials with approximation error $o(1)$.

<a id="pdf-988dc9f0ae91-p008-b005"></a>
<!-- pdf-source: page=8; block=5; confidence=0.88 -->
**Proof.** Let $G\overset{\text{def}}{=}\{x\in\{0,1\}^n:Q(x)=\mathrm{MOD}_2(x)\}$. Goal: show $G$ misses a constant fraction of $\{0,1\}^n$ by using $Q$ to build a class of $p^{(1-\Omega(1))\cdot 2^n}$ multilinear polynomials that compute $p^{|G|}$ distinct functions; the low degree of $Q$ bounds the degree of these polynomials. Crucial step: substitute $x_i\in\{0,1\}\mapsto(-1)^{x_i}\in\{\pm1\}\equiv\{1,q-1\}$, where $(-1)^{x_i}=(1-x_i)(-1)^0+x_i(-1)^1=1-2x_i$. This relates $\mathrm{MOD}_2$ to a product: $(-1)^{\mathrm{MOD}_2(x_1,\dots,x_n)}=\prod_{i\in[n]}(-1)^{x_i}$. Define $R:\mathrm{GF}(p)^n\to\mathrm{GF}(p)$ by $R(y_1,\dots,y_n)\overset{\text{def}}{=}1-2\cdot Q(x_1,\dots,x_n)$ with $x_i=(1-y_i)/2$ (i.e. $y_i=1-2x_i$); $R$ has the same degree as $Q$, and $R(y_1,\dots,y_n)=\prod_{i\in[n]}y_i$ whenever the corresponding $(x_1,\dots,x_n)\in G$.

<a id="pdf-988dc9f0ae91-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.90 -->
For every $x\in\{0,1\}^n$: $\prod_{i\in[n]}(1-2x_i)=\prod_{i\in[n]}(-1)^{x_i}=(-1)^{\mathrm{MOD}_2(x)}=1-2\,\mathrm{MOD}_2(x)$; and $x\in G\Rightarrow\mathrm{MOD}_2(x)=Q(x)$. Hence $\prod(1-2x_i)=1-2Q(x)$ for $x\in G$, i.e. $\prod_{i\in[n]}y_i=R(y)$ when $((1-y_1)/2,\dots,(1-y_n)/2)\in G$. Let $H\overset{\text{def}}{=}\{y\in\{\pm1\}^n:R(y)=\prod_{i\in[n]}y_i\}$, so $|H|=|G|$; upper-bound $|H|$. Key: $R$ is degree $\sqrt n$ but on $H$ equals the degree-$n$ polynomial $\prod y_i$. Let $\mathcal F$ be all $f:H\to\mathrm{GF}(p)$, $|\mathcal F|=p^{|H|}$. Each $f$ is a linear combination of multilinear monomials (as $\sigma^2=1$ for $\sigma\in\{\pm1\}$): $f(y)=\sum_{I\subseteq[n]}f_I\prod_{i\in I}y_i$, $f_I\in\mathrm{GF}(p)$. Using $R(y)=\prod y_i$, any monomial reduces to degree $\le(n+\sqrt n)/2$: $\prod_{i\in I}y_i=R(y)\cdot\prod_{i\in[n]\setminus I}y_i$ of degree $\sqrt n+(n-|I|)$, and either $|I|\le(n+\sqrt n)/2$ or $\sqrt n+(n-|I|)<(n+\sqrt n)/2$ (using $y_i^2=1$). With $t\overset{\text{def}}{=}(n+\sqrt n)/2$: $f(y)=\sum_{|I|\le t}f_I\prod_{i\in I}y_i+\sum_{|I|>t}f_I\,R(y)\prod_{i\in[n]\setminus I}y_i$, a linear combination of multilinear monomials of degree $\le t$. The number of such monomials is $\sum_{i=0}^t\binom{n}{i}$, so $|\mathcal F|\le p^{\sum_{i=0}^t\binom{n}{i}}$, giving $|H|\le\sum_{i=0}^t\binom{n}{i}=\sum_{i\le 0.5n+O(\sqrt n)}\binom{n}{i}=(1-\Omega(1))\cdot 2^n$. $\square$

<a id="pdf-988dc9f0ae91-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.86 -->
Footnote 8 (general degree $D$). With $\deg Q=D$ and $t=(n+D)/2$, one must bound $\sum_{i\le t}\binom{n}{i}$. For $D\le\sqrt n$: $\sum_{i\le t}\binom{n}{i}\le\sum_{i\le(n-1)/2}\binom{n}{i}+(1+(D/2))\cdot O(2^n/\sqrt n)\le(0.5+O(D/\sqrt n))\cdot 2^n$. For $D>\sqrt n$: $2^{-n}\sum_{i\le t}\binom{n}{i}=1-\exp(-O(D^2/n))$.

<a id="pdf-988dc9f0ae91-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.90 -->
**Digest.** Lemma 3 uses an algebraic manipulation converting a low-degree polynomial approximating MOD2 over $\{0,1\}^n$ into a low-degree polynomial that effectively reduces (over $\{\pm1\}^n$) the degree of any monomial to $t \stackrel{\text{def}}{=} 0.5n + O(\sqrt{n})$, which bounds approximation quality. If the approximation is correct on $N$ inputs of $\{0,1\}^n$, the degree reduction holds for $N$ inputs in $\{\pm1\}^n \subseteq \mathrm{GF}(p)^n$ spanning a dimension-$N$ space; but functions on these $N$ inputs expressible as linear combinations of multilinear monomials of degree $\le t$ have dimension $\le \sum_{i\le t}\binom{n}{i} = (1-\Omega(1))\cdot 2^n$. Hence $N \le (1-\Omega(1))\cdot 2^n$. The enabling observation is $(-1)^{\mathrm{MOD2}(x)} = \prod_{i\in[n]}(-1)^{x_i}$, realized by the substitution $x_i \mapsto (-1)^{x_i}$, which agrees over $\{0,1\}$ with the linear map $L(\zeta)=1-2\zeta$.

<a id="pdf-988dc9f0ae91-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.90 -->
**Extension to arbitrary $q \ne p$.** One tries to extend to MODq via a $q$th root of unity and the $(q-1)$-dimensional extension field of $\mathrm{GF}(p)$ (using an element of multiplicative order $q$). Two obstacles arise, both absent for $q=2$: (1) generally $\mathrm{MODq}(x) \ne \mathrm{modq}(x) \stackrel{\text{def}}{=} \sum_{i\in[n]} x_i \bmod q$ even on $\{0,1\}$ — resolved by working with $\mathrm{modq}$; (2) products of multilinear monomials over $\{1,\omega\}$ need not be multilinear since $\omega^e \notin \{1,\omega\}$ for general $e\in\mathbb{Z}_q$ — resolved by reducing individual degrees via a linear transformation: for $\zeta\in\{1,\omega\}$ and $e\in\mathbb{Z}_q$, replace $\zeta^e$ with $\frac{\zeta-1}{\omega-1}\cdot\omega^e + \frac{\zeta-\omega}{1-\omega}$. This yields an extension of Lemma 3 to arbitrary $q\ne p$ for $\mathrm{modq}$; the gap to Lemma 2 (which concerns MODq) is bridged in Section 3.

<a id="pdf-988dc9f0ae91-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.97 -->
# 3 Advanced reading

<a id="pdf-988dc9f0ae91-p010-b004"></a>
<!-- pdf-source: page=10; block=4; confidence=0.92 -->
Recap: Lemma 3 translates a low-degree $\mathrm{GF}(p)$ polynomial approximating $\mathrm{MOD2}\equiv\mathrm{mod2}$ over $\{0,1\}^n$ into one approximating the product of $n$ variables valued in $\{\pm1\}=\{1,p-1\}$, and one hopes to extend to $\mathrm{modq}$ via a $q$th root of unity. Where is $p\ne q$ used: if $p=q$ then for every $e\in\mathbb{Z}$, $p^e-1$ is not divisible by $q$, so the extension field has no element of multiplicative order $q$. If $p\ne q$, then $p^{q-1}\equiv 1\pmod q$, so $q \mid p^{q-1}-1$, hence the $(q-1)$-dimensional extension field of $\mathrm{GF}(p)$ has elements of multiplicative order $q$.

<a id="pdf-988dc9f0ae91-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.93 -->
The $(q-1)$-dimensional extension field of $\mathrm{GF}(p)$ is spanned by the powers of the $q$th root of unity iff $(x^q-1)/(x-1)=\sum_{i=0}^{q-1}x^i$ is irreducible over $\mathrm{GF}(p)$; this holds for some $p\ne q$ and fails for others.

<a id="pdf-988dc9f0ae91-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.94 -->
**Notation.** Fix primes $p\ne q$. Let $K$ be the $(q-1)$-dimensional extension field of $\mathrm{GF}(p)$, and $\omega\in K$ an arbitrary element of multiplicative order $q$. Let $\mathbb{Z}_q\stackrel{\text{def}}{=}\{0,1,\dots,q-1\}$. Recall $\mathrm{modq}:\{0,1\}^n\to\mathbb{Z}_q$ with $\mathrm{modq}(x)\stackrel{\text{def}}{=}\sum_{i\in[n]}x_i \bmod q$. Functions ranging in $\mathrm{GF}(p)$ cannot approximate $\mathrm{modq}$ well when $q>p$; when $q<p$ one embeds $\mathbb{Z}_q$ into $\mathrm{GF}(p)$ directly. The case $q<p$ is treated first, $q>p$ later.

<a id="pdf-988dc9f0ae91-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.93 -->
## 3.1 The case of $q < p$

States and proves the natural extension of Lemma 3, now for $\mathrm{modq}$ (not MODq); it coincides with Lemma 3 at $q=2$ since $\mathrm{mod2}\equiv\mathrm{MOD2}$.

<a id="pdf-988dc9f0ae91-p011-b004"></a>
<!-- pdf-source: page=11; block=4; confidence=0.90 -->
**Lemma 4** (error rate of low-degree $\mathrm{GF}(p)$ polynomials approximating $\mathrm{mod}_q$). There exists a constant $\epsilon>0$ such that, for any prime $p>q$, any $n$-variate polynomial $Q:\mathrm{GF}(p)^n\to\mathrm{GF}(p)$ of degree at most $\sqrt{n}$ fails to compute $\mathrm{mod}_q$ on at least $\epsilon\cdot 2^n$ of the $n$-long inputs; i.e. $\Pr_{x\in\{0,1\}^n}[Q(x)\ne\mathrm{mod}_q(x)]\ge\epsilon$.

<a id="pdf-988dc9f0ae91-p011-b005"></a>
<!-- pdf-source: page=11; block=5; confidence=0.83 -->
For $p<q$ the statement is pointless: no $\mathrm{GF}(p)$ polynomial approximates $\mathrm{modq}$ with error below $(q-p-o(1))/q$, since $\Pr_{x\in\{0,1\}^n}[\mathrm{modq}(x)\in\{0,\dots,p-1\}]\le \tfrac{p}{2^n}$ (per-value probability). Lemma 4 concerns $\mathrm{modq}$, whereas contrast with Lemma 2 requires the analogous result for MODq; this gap is addressed later.

<a id="pdf-988dc9f0ae91-p011-b006"></a>
<!-- pdf-source: page=11; block=6; confidence=0.90 -->
**Proof.** Let $G\stackrel{\text{def}}{=}\{x\in\{0,1\}^n: Q(x)=\mathrm{modq}(x)\}$. Show $G$ misses a constant fraction of $\{0,1\}^n$ by using $Q$ to exhibit a class of $|K|^{(1-\Omega(1))\cdot 2^n}$ polynomials computing $|K|^{|G|}$ distinct functions, extending Lemma 3's proof. The crucial step is the substitution $x_i\in\{0,1\}\mapsto \omega^{x_i}\in\{1,\omega\}\subset K$ (for $q=2$, $\omega=-1$, $K=\mathrm{GF}(p)$). It gives $\omega^{\mathrm{modq}(x_1,\dots,x_n)}=\prod_{i\in[n]}\omega^{x_i}$. The map $\zeta\mapsto\omega^\zeta$ on $\mathbb{Z}_q$, extended to $K$, and its inverse are computed by degree-$(q-1)$ polynomials $M,M':K\to K$ with $M(\zeta)=\omega^\zeta$ and $M'(M(\zeta))=\zeta$ for $\zeta\in\mathbb{Z}_q$.

<a id="pdf-988dc9f0ae91-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.90 -->
**Proof (cont.).** Define $R:K^n\to K$ by $R(y_1,\dots,y_n)\stackrel{\text{def}}{=}M(Q(x_1,\dots,x_n))$ with $x_i=M'(y_i)$ (equivalently $y_i=M(x_i)$ for $x_i\in\{0,1\}$); $R$ has degree $(q-1)^2\cdot\sqrt{n}$, viewing $Q$ over $K$. Salient feature: $R(y)=\prod_{i\in[n]}y_i$ whenever $(M'(y_1),\dots,M'(y_n))\in G$. Indeed for $x\in\{0,1\}^n$: $\prod_{i\in[n]}M(x_i)=\prod_{i\in[n]}\omega^{x_i}=\omega^{\mathrm{modq}(x)}=M(\mathrm{modq}(x))$, and $x\in G$ gives $\mathrm{modq}(x)=Q(x)$, so $\prod_i M(x_i)=M(Q(x))$, i.e. $\prod_i y_i=R(y)$ for $y\in\{1,\omega\}^n$ with $(M'(y_1),\dots,M'(y_n))\in G$.

<a id="pdf-988dc9f0ae91-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.90 -->
Let $H\stackrel{\text{def}}{=}\{y\in\{1,\omega\}^n: R(y)=\prod_{i\in[n]}y_i\}$; then $|H|\ge|G|$, and it suffices to upper-bound $|H|$. Key property: $R$ has degree $(q-1)^2\sqrt{n}$ yet, restricted to $H$, equals the degree-$n$ polynomial $\prod_{i\in[n]}y_i$.

<a id="pdf-988dc9f0ae91-p012-b003"></a>
<!-- pdf-source: page=12; block=3; confidence=0.90 -->
Consider $F=\{f:H\to K\}$, so $|F|=|K|^{|H|}$. Each $f\in F$ is a linear combination of multilinear monomials: for distinct $\alpha,\beta\in K$, any $g:\{\alpha,\beta\}\to K$ equals the linear function
$$L_{\alpha,\beta,g}(\zeta)\stackrel{\text{def}}{=}\frac{\zeta-\beta}{\alpha-\beta}\,g(\alpha)+\frac{\zeta-\alpha}{\beta-\alpha}\,g(\beta)\quad(4)$$
with $L(\alpha)=g(\alpha)$, $L(\beta)=g(\beta)$. For $e_1,\dots,e_n\in\mathbb{Z}_q$, replace $\prod_i y_i^{e_i}$ by $\prod_i L_{1,\omega,g_{e_i}}(y_i)$ where $g_e(\zeta)=\zeta^e$ (values preserved on $\{1,\omega\}^n$). Hence for $y\in H$, $f(y)=\sum_{I\subseteq[n]}f_I\prod_{i\in I}y_i$ with $f_I\in K$.

<a id="pdf-988dc9f0ae91-p012-b004"></a>
<!-- pdf-source: page=12; block=4; confidence=0.86 -->
Using $R(y)=\prod_{i\in[n]}y_i$ on $H$, reduce the number of variables per monomial to at most $(n+(q-1)^2\sqrt{n})/2$: since $\prod_{i\in I}y_i=\big(\prod_{i\in[n]}y_i\big)\cdot\prod_{i\in[n]\setminus I}y_i^{q-1}=R(y)\cdot\prod_{i\in[n]\setminus I}y_i^{q-1}$, using $y_i^q=1$ for $i\in I$ (as $y_i\in\{1,\omega\}$), and $R(y)\cdot\prod_{i\in[n]\setminus I}y_i^{q-1}$ is a linear combination of monomials each with at most $\sqrt{n}+(n-|I|)$ variables. So either $|I|\le(n+(q-1)^2\sqrt{n})/2$ or $\sqrt{n}+(n-|I|)<(n+(q-1)^2\sqrt{n})/2$. Setting $t\stackrel{\text{def}}{=}(n+(q-1)^2\sqrt{n})/2$,
$$f(y)=\sum_{I\subseteq[n]:|I|\le t}f_I\prod_{i\in I}y_i+\sum_{I\subseteq[n]:|I|>t}f_I\prod_{i\in I}y_i.$$

<a id="pdf-988dc9f0ae91-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.90 -->
**Proof (continued).** The displayed identity expands the sum as $\sum_{I\subseteq[n]:|I|\le t} f_I\cdot\prod_{i\in I} y_i \;+\; \sum_{I\subseteq[n]:|I|>t} f_I\cdot R(y)\cdot\prod_{i\in[n]\setminus I} y_i^{q-1}$, showing every $f\in F$ is a linear combination of monomials each using at most $t=(n+(q-1)^2\sqrt{n})/2$ variables. Replacing each power $y_i^e$ by the corresponding linear function $L_{1,\omega,g_e}$ (with $g_e(\zeta)=\zeta^e$) makes each $f\in F$ a linear combination of multi-linear monomials of degree at most $t$. Their number is $N \stackrel{\text{def}}{=}\sum_{i=0}^{t}\binom{n}{i}$, hence $|F|\le |K|^N$; the claim follows since $N=(1-\exp(-\Omega(q^4)))\cdot 2^n=(1-\Omega(1))\cdot 2^n$.

<a id="pdf-988dc9f0ae91-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.65 -->
Remark (Digest). The proof of Lemma 4 mirrors that of Lemma 3, replacing $\mathrm{GF}(p)$ by its $(q-1)$-dimensional extension $K$ and replacing $-1\in\mathrm{GF}(p)$ by $\omega\in K$ of multiplicative order $q$. Two additional modifications: (1) though $\bmod_q$'s inputs are bits, the map $\zeta\mapsto\omega^\zeta$ is defined over $\mathbb{Z}_q$; it and its inverse are degree-$(q-1)$ polynomials over $K$, so $\deg R$ exceeds $\deg Q$ by a factor $(q-1)^2$. (2) In two places arbitrary powers of $y_i\in\{1,\omega\}$ are replaced by linear functions of $y_i$ (Eq. (4)), keeping the argument on multi-linear low-degree polynomials computing functions in $F$. Note: Lemma 4 concerns approximating $\bmod_q:\{0,1\}^n\to\mathbb{Z}_n$, whereas the contrast with Lemma 2 (used for Part 2 of Theorem 1) concerns $\mathrm{MOD}_q:\{0,1\}^n\to\{0,1\}$.

<a id="pdf-988dc9f0ae91-p013-b003"></a>
<!-- pdf-source: page=13; block=3; confidence=0.85 -->
**Bridging the gap (MOD_q vs mod_q).** Lemma 4 gives that every degree-$\sqrt{n}$ polynomial over $\mathrm{GF}(p)$ approximates $\bmod_q$ with error rate $\Omega(1)$; the contrast with Lemma 2 requires the same for $\mathrm{MOD}_q$. Proved by contrapositive: from a $\mathrm{GF}(p)$-polynomial approximating $\mathrm{MOD}_q$ with error $o(1)$, produce a same-degree polynomial approximating $\bmod_q$ with error $o(1)$. Reduction: $\bmod_q(x)=\sum_{i\in[q-1]}(1-\mathrm{MOD}_q(x1^{q-i}0^i))\cdot i$, valid because $\mathrm{MOD}_q(x1^{q-i}0^i)=0 \iff \bmod_q(x1^{q-i}0^i)=0 \iff \bmod_q(x)=i$. Thus an approximator $Q$ of $\mathrm{MOD}_q$ gives $Q'(x)=\sum_{i\in[q-1]}(1-Q(x1^{q-i}0^i))\cdot i$ for $\bmod_q$, which preserves degree but not error rate.

<a id="pdf-988dc9f0ae91-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.86 -->
**Proof (continued).** The error rate of $Q'$ is at most a $(q-1)\cdot 2^q$ factor larger than that of $Q$: $\Pr_{x\in\{0,1\}^n}[Q'(x)\ne\bmod_q(x)] \le \sum_{i\in[q-1]}\Pr_x[Q(x1^{q-i}0^i)\ne\mathrm{MOD}_q(x1^{q-i}0^i)] \le (q-1)\cdot\dfrac{\Pr_{z\in\{0,1\}^{n+q}}[Q(z)\ne\mathrm{MOD}_q(z)]}{2^{-q}}$. Tolerable since $q$ is constant and $Q$'s error rate is $o(1)$.

<a id="pdf-988dc9f0ae91-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.90 -->
**Section 3.2 — The case of $q>p$.** The hypothesis $q<p$ was used only in Section 3.1 to embed $\mathbb{Z}_q$ in $\mathrm{GF}(p)$. For $q>p$, pick an integer $e>1$ with $q<p^e$ (e.g. $e=\lceil\log_p q\rceil$) and embed $\mathbb{Z}_q$ in $\mathrm{GF}(p)^e$ via $\psi:\mathbb{Z}_q\to\mathrm{GF}(p)^e$.

<a id="pdf-988dc9f0ae91-p014-b003"></a>
<!-- pdf-source: page=14; block=3; confidence=0.83 -->
**Modifications for $q>p$.** In Lemma 4 take $Q:\mathrm{GF}(p)^n\to\mathrm{GF}(p)^e$ with hypothesis $\Pr_{x\in\{0,1\}^n}[Q(x)\ne\psi(\bmod_q(x))]\ge\epsilon$ ($\psi$ applied only to the output), and set $G\stackrel{\text{def}}{=}\{x\in\{0,1\}^n: Q(x)=\psi(\bmod_q(x))\}$. Replace $M:K\to K$, $M':K\to K$ by $M:K^e\to K$, $M':K\to K$ with $M(\psi(\zeta))=\omega^\zeta$ for $\zeta\in\mathbb{Z}_q$ and $M'(\omega^\zeta)=\zeta$ for $\zeta\in\{0,1\}$; now $M$ is an $e$-variate polynomial of individual degree $p-1$ and $M'$ is linear. Define $R:K^n\to K$, $R(y_1,\dots,y_n)\stackrel{\text{def}}{=}M(Q(M'(y_1),\dots,M'(y_n)))$, of degree $e\cdot(p-1)\cdot\sqrt{n}$. For $(x_1,\dots,x_n)\in G$: $R(\omega^{x_1},\dots,\omega^{x_n}) = M(Q(x_1,\dots,x_n)) = M(\psi(\bmod_q(x))) = \omega^{\bmod_q(x)} = \prod_{i\in[n]}\omega^{x_i}$. (Footnote 10: an alternative $M':K\to K^e$ via an $e$-long sequence of degree-$(q-1)$ univariate polynomials with $M'(\omega^\zeta)=\psi(\zeta)$ would give $R$ degree $e\cdot(p-1)\cdot(q-1)\cdot\sqrt{n}$.)

<a id="pdf-988dc9f0ae91-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.84 -->
**Proof (continued).** Let $H\stackrel{\text{def}}{=}\{y\in\{1,\omega\}^n: R(y)=\prod_{i\in[n]}y_i\}$; then $|H|\ge|G|$ as before, and one proceeds exactly as in the part upper-bounding $|H|$. When bridging the gap between $\mathrm{MOD}_q$ and $\bmod_q$, define $Q'(x)=\sum_{i\in[q-1]}(1-Q(x1^{q-i}0^i))\cdot\psi(i)\in\mathrm{GF}(p)^e$. This restates Lemma 4 with $\bmod_q$ approximated by an $e$-long sequence of $n$-variate polynomials over $\mathrm{GF}(p)$, $e=\lceil\log_p q\rceil$. An alternative avoiding the $q<p$/$q>p$ split treats $\omega^{\bmod_q(x)}$ as a representation of $\bmod_q(x)$: start from a low-degree $Q:K^n\to K$ and lower-bound $\Pr_{x\in\{0,1\}^n}[Q(x)\ne\omega^{\bmod_q(x)}]$.

<a id="pdf-988dc9f0ae91-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.85 -->
**Section 4 — Beyond the recommended reading.** Extend $\bmod_q$ from $\{0,1\}^n$ to $\mathbb{Z}_q^n$: define $\bmod'_q:\mathbb{Z}_q^n\to\mathbb{Z}_q$ by $\bmod'_q(x)=\sum_{i\in[n]}x_i \bmod q$, with error rate $\Pr_{x\in\mathbb{Z}_q^n}[Q(x)\ne\bmod'_q(x)]$ for low-degree $Q:\mathrm{GF}(p)^n\to\mathrm{GF}(p)$. Approximating $\bmod_q$ reduces to approximating $\bmod'_q$ (shown at end of Section 4.1), and the converse holds; combining the converse reduction with a lower bound wrt $\bmod'_q$ gives an alternative (more complicated) proof of Lemma 4. This section proves the error rate of any degree-$\sqrt{n}$ polynomial over $\mathrm{GF}(p)$ wrt $\bmod'_q$ is bounded below by a positive constant. Difficulty: products of multi-linear monomials need not be multi-linear; unlike Lemma 4 (where individual degrees were reduced to 1 since only values at $1,\omega$ mattered), here all powers of $\omega$ matter, so one instead considers all monomials of total degree $\le t$ and individual degree $\le q-1$, contrasting their number with the number of functions on the subset of $\mathbb{Z}_q^n$ where $Q$ agrees with $\bmod'_q$. Notation: primes $p\ne q$, $K$ the $(q-1)$-dimensional extension of $\mathrm{GF}(p)$, $\omega\in K$ of order $q$; cases $q<p$ (embed $\mathbb{Z}_q$ in $\mathrm{GF}(p)$) and $q>p$ (embed in $\mathrm{GF}(p)^e$, $e=\lceil\log_p q\rceil$).

<a id="pdf-988dc9f0ae91-p015-b003"></a>
<!-- pdf-source: page=15; block=3; confidence=0.92 -->
**Section 4.1 — The case of $q<p$.** $\bmod'_q:\mathbb{Z}_q^n\to\mathbb{Z}_q$ is defined by $\bmod'_q(x_1,\dots,x_n)\stackrel{\text{def}}{=}\sum_{i\in[n]}x_i \bmod q$.

<a id="pdf-988dc9f0ae91-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.90 -->
**Lemma 5 (error rate of low-degree GF(p) polynomials approximating mod'_q).** There is a constant ε > 0 such that, for every prime p > q, any n-variate polynomial Q : GF(p)^n → GF(p) of degree at most √n fails to compute mod'_q on at least ε·q^n of the n-long inputs; that is, Pr_{x∈{0,1,…,q−1}^n}[Q(x) ≠ mod'_q(x)] ≥ ε.

<a id="pdf-988dc9f0ae91-p016-b002"></a>
<!-- pdf-source: page=16; block=2; confidence=0.90 -->
**Proof.** Let G := {x ∈ Z_q^n : Q(x) = mod'_q(x)} be the agreement set. Goal: show G misses a constant fraction of Z_q^n, by using Q to build a class of |K|^{(1−Ω(1))·q^n} polynomials computing |K|^{|G|} distinct functions. The argument extends the proof of Lemma 4; the crucial step remains a variable substitution.

<a id="pdf-988dc9f0ae91-p016-b003"></a>
<!-- pdf-source: page=16; block=3; confidence=0.85 -->
**Proof step (substitution).** Map x_i ∈ Z_q to ω^{x_i}, using ω^{mod'_q(x_1,…,x_n)} = ∏_{i∈[n]} ω^{x_i}. There exist degree-(q−1) polynomials M, M' : K → K with M(ζ) = ω^ζ and M'(M(ζ)) = ζ for all ζ ∈ Z_q. Define R : K^n → K by R(y_1,…,y_n) := M(Q(x_1,…,x_n)) where x_i = M'(y_i) (equivalently y_i = M(x_i) for x_i ∈ Z_q ⊂ GF(p)); R is obtained by viewing Q over K. The definitions of M, M', R carry over from Lemma 4 despite G being defined differently.

<a id="pdf-988dc9f0ae91-p016-b004"></a>
<!-- pdf-source: page=16; block=4; confidence=0.85 -->
**Proof step (feature of R).** R has degree at most (q−1)^2·√n, yet R(y_1,…,y_n) = ∏_{i∈[n]} y_i whenever the corresponding (x_1,…,x_n) = (M'(y_1),…,M'(y_n)) ∈ G. Define H := { y ∈ {ω^e : e ∈ Z_q}^n : R(y) = ∏_{i∈[n]} y_i }, so |H| ≥ |G|; we upper-bound |H|. Key fact: R is degree ≤ (q−1)^2·√n but, restricted to H, coincides with the degree-n polynomial ∏_{i∈[n]} y_i.

<a id="pdf-988dc9f0ae91-p016-b005"></a>
<!-- pdf-source: page=16; block=5; confidence=0.85 -->
**Proof step (function class F).** Let F be all functions f : H → K, so |F| = |K|^{|H|}. Each f is a linear combination of monomials of individual degree ≤ q−1 (since σ^q = 1 for σ ∈ {ω^e : e ∈ Z_q}). Using R(y) = ∏ y_i on H, multiply by small powers of R to reduce each monomial's total degree to at most t := ((q−1)·n + 2(q−1)^3·√n)/2. For a monomial ∏_{i} y_i^{e_i} with e_i ∈ Z_q, there exists j ∈ Z_q with ∑_{i∈[n]}(e_i + j mod q) ≤ (q−1)·n/2 (integer sum), because E_{j∈Z_q}[e_i + j mod q] = (q−1)/2.

<a id="pdf-988dc9f0ae91-p016-b006"></a>
<!-- pdf-source: page=16; block=6; confidence=0.90 -->
**Footnote.** As in Lemma 4: for every (x_1,…,x_n) ∈ Z_q^n, ∏_{i∈[n]} M(x_i) = ∏_{i∈[n]} ω^{x_i} = ω^{mod'_q(x_1,…,x_n)} = M(mod'_q(x_1,…,x_n)); and (x_1,…,x_n) ∈ G implies mod'_q(x_1,…,x_n) = Q(x_1,…,x_n).

<a id="pdf-988dc9f0ae91-p017-b001"></a>
<!-- pdf-source: page=17; block=1; confidence=0.85 -->
**Proof step (bounding |F|).** Equation (5): (∏_{i∈[n]} y_i)^j · ∏_{i∈[n]} y_i^{e_i} = ∏_{i∈[n]} y_i^{e_i+j mod q}, whose r.h.s. has total degree ≤ (q−1)·n/2. Choosing j_e ∈ Z_q per exponent vector e, write any f as f(y) = ∑_{e∈Z_q^n} f_e ∏_i y_i^{e_i} = ∑_e f_e · R(y)^{q−j_e mod q} · ∏_i y_i^{e_i+j_e mod q}, with f_e ∈ K. Each term is a linear combination of monomials of total degree ≤ (q−1)·deg(R) + (q−1)n/2 ≤ t and individual degree ≤ q−1 (using y_i^q = 1). Hence f is a linear combination of such monomials. The count of monomials of total degree ≤ t and individual degree ≤ q−1 is (1 − exp(−O(q^4)))·q^n, since Pr[sum of n i.i.d. uniform Z_q variables > t = 0.5(q−1)n + (q−1)^3√n] = exp(−O(q^4)). Therefore |F| ≤ |K|^{(1−Ω(1))·q^n}. ∎

<a id="pdf-988dc9f0ae91-p017-b002"></a>
<!-- pdf-source: page=17; block=2; confidence=0.90 -->
**Reduction: mod'_q : Z_q^n → Z_q to mod_q : {0,1}^n → Z_q.**

<a id="pdf-988dc9f0ae91-p017-b003"></a>
<!-- pdf-source: page=17; block=3; confidence=0.85 -->
**Proof step (unary encoding).** Use U : Z_q → {0,1}^{q−1}, U(σ) = 1^σ 0^{q−1−σ} (Hamming weight σ), computable by q−1 univariate degree-(q−1) polynomials over GF(p) (uses Z_q ⊆ GF(p), i.e. q < p). Then mod'_q(x_1,…,x_n) = mod_q(U(x_1),…,U(x_n)). An approximator Q for mod_q gives Q'(x) = Q(U(x_1),…,U(x_n)) for mod'_q, of degree (q−1)× larger; but error rate is not preserved — it may blow up by a factor (2^{q−1}/q)^n, which is unaffordable.

<a id="pdf-988dc9f0ae91-p017-b004"></a>
<!-- pdf-source: page=17; block=4; confidence=0.85 -->
**Proof step (random routing).** Set n' = (q−1)·n and use a Hamming-weight-preserving bijection Π : {0,1}^{n'} → {0,1}^{n'}, Π(z_1,…,z_{n'}) = (z_{π(1)},…,z_{π(n')}) for random permutation π of [n']. If X = (X_1,…,X_n) is uniform in Z_q^n, then Π(U(X_1),…,U(X_n)) is o(1)-close to uniform on {0,1}^{n'}, since the total variation distance between the 1-count of (U(X_1),…,U(X_n)) (= ∑_{i∈[n]} X_i) and that of a uniform n'-bit string vanishes with n.

<a id="pdf-988dc9f0ae91-p018-b001"></a>
<!-- pdf-source: page=18; block=1; confidence=0.85 -->
**Proof step (fixing π).** Using the o(1)-closeness: Pr_{x∈Z_q^n, π∈Sym_{n'}}[Q(Π(U(x_1),…,U(x_n))) ≠ mod'_q(x)] = Pr[Q(Π(U(x))) ≠ mod_q(U(x))] ≤ Pr_{z∈{0,1}^{n'}}[Q(z) ≠ mod_q(z)] + o(1). Hence there exists a permutation π whose routing map Π_π (Π_π(z) = (z_{π(1)},…,z_{π(n')})) satisfies Pr_{x∈Z_q^n}[Q(Π_π(U(x))) ≠ mod'_q(x)] ≤ Pr_{z}[Q(z) ≠ mod_q(z)] + o(1). Define Q'(x) := Q(Π_π(U(x_1),…,U(x_n))); Π_π only permutes variables, giving the desired approximator.

<a id="pdf-988dc9f0ae91-p018-b002"></a>
<!-- pdf-source: page=18; block=2; confidence=0.90 -->
**Reduction: mod_q : {0,1}^n → Z_q to mod'_q : Z_q^n → Z_q.**

<a id="pdf-988dc9f0ae91-p018-b003"></a>
<!-- pdf-source: page=18; block=3; confidence=0.88 -->
**Proof step (randomized reduction).** On input x ∈ {0,1}^n, pick random r ∈ Z_q^n and output (mod q) the sum of q − mod'_q(r) and mod'_q(r + x mod q). Since 2-argument addition mod q is a bivariate polynomial A of individual degree q−1, define Q_r(x) := A(q − mod'_q(r), Q(A(r_1,x_1),…,A(r_n,x_n))). Then Pr_{r∈Z_q^n}[Q_r(x) = mod_q(x)] = Pr_r[Q(r + x mod q) = mod_q(r + x mod q)] = Pr_r[Q(r) = mod'_q(r)]. Averaging over x: E_r[Pr_x[Q_r(x) = mod_q(x)]] = Pr_r[Q(r) = mod'_q(r)]. Hence some fixed r gives error rate of Q_r w.r.t. mod_q at most the error rate of Q w.r.t. mod'_q. Degree of Q_r is (q−1)^2 times that of Q; the claim follows. ∎

<a id="pdf-988dc9f0ae91-p018-b004"></a>
<!-- pdf-source: page=18; block=4; confidence=0.95 -->
**4.2 The case of q > p.**

<a id="pdf-988dc9f0ae91-p018-b005"></a>
<!-- pdf-source: page=18; block=5; confidence=0.90 -->
As in Section 3, the hypothesis q < p was used only in Section 4.1, to embed Z_q into GF(p); associating Z_q with {0,…,q−1} and GF(p) with {0,…,p−1} gave an implicit straightforward embedding.

<a id="pdf-988dc9f0ae91-p019-b001"></a>
<!-- pdf-source: page=19; block=1; confidence=0.90 -->
**Setup (case q > p).** Pick an integer $e>1$ with $q<p^e$ and fix an embedding $\psi:\mathbb{Z}_q\to\mathrm{GF}(p)^e$ of $\mathbb{Z}_q$ into $\mathrm{GF}(p)^e$. The following bullets modify Section 4.1 accordingly.

<a id="pdf-988dc9f0ae91-p019-b002"></a>
<!-- pdf-source: page=19; block=2; confidence=0.92 -->
**Modification (Lemma 5 hypothesis).** Consider $Q:\mathrm{GF}(p)^{en}\to\mathrm{GF}(p)^e$ with hypothesis $\Pr_{x\in\mathbb{Z}_q^n}[Q(\psi(x))\neq\psi(\mathrm{mod}_q(x))]\ge\epsilon$, where $\psi(x_1,\dots,x_n)=(\psi(x_1),\dots,\psi(x_n))$ and $\mathrm{mod}_q:\mathbb{Z}_q^n\to\mathbb{Z}_q$ is unchanged. The proof begins by defining $G:=\{x\in\mathbb{Z}_q^n : Q(\psi(x))=\psi(\mathrm{mod}_q(x))\}$.

<a id="pdf-988dc9f0ae91-p019-b003"></a>
<!-- pdf-source: page=19; block=3; confidence=0.90 -->
**Modification (proof of Lemma 5).** Use maps $M:K^e\to K$ and $M':K\to K^e$ with $M(\psi(\zeta))=\omega^\zeta$ and $M'(\omega^\zeta)=\psi(\zeta)$ for all $\zeta\in\mathbb{Z}_q$; now $M$ is an $e$-variate polynomial of individual degree $p-1$ and $M'$ is an $e$-long sequence of univariate polynomials of degree $q-1$. Define $R:K^n\to K$ by $R(y_1,\dots,y_n):=M(Q(M'(y_1),\dots,M'(y_n)))$, of degree $e\cdot(p-1)\cdot(q-1)\cdot\sqrt{n}$. For $(x_1,\dots,x_n)\in G$: $R(\omega^{x_1},\dots,\omega^{x_n})=M(Q(\psi(x_1),\dots,\psi(x_n)))=M(\psi(\mathrm{mod}'_q(x_1,\dots,x_n)))=\omega^{\mathrm{mod}'_q(x_1,\dots,x_n)}=\prod_{i\in[n]}\omega^{x_i}$. Let $H:=\{y\in\{\omega^e:e\in\mathbb{Z}_q\}^n : R(y)=\prod_{i\in[n]}y_i\}$; since $|H|\ge|G|$ (as before), proceed as in the second part of the proof.

<a id="pdf-988dc9f0ae91-p019-b004"></a>
<!-- pdf-source: page=19; block=4; confidence=0.86 -->
**Modification (reducing $\mathrm{mod}'_q$ to $\mathrm{mod}_q$).** Keep the unary encoding $U:\mathbb{Z}_q\to\{0,1\}^{q-1}$ but compute it over $\mathrm{GF}(p)^e$: in defining $Q'$ set $U'(\psi(\zeta))=U(\zeta)$ for $\zeta\in\mathbb{Z}_q$, computing each bit of $U(\zeta)$ by $e$-variate polynomials acting on $\psi(\zeta)\in\mathrm{GF}(p)^e$. For $x\in\mathbb{Z}_q^n$, define $Q'(\psi(x)):=Q(\Pi_\pi(U'(\psi(x_1)),\dots,U'(\psi(x_n))))$, whose value equals $Q(\Pi_\pi(U(x_1),\dots,U(x_n)))$.

<a id="pdf-988dc9f0ae91-p019-b005"></a>
<!-- pdf-source: page=19; block=5; confidence=0.85 -->
**Modification (reducing $\mathrm{mod}_q$ to $\mathrm{mod}'_q$).** Given $Q:\mathrm{GF}(p)^{en}\to\mathrm{GF}(p)^e$ approximating $\mathrm{mod}'_q:\mathbb{Z}_q^n\to\mathbb{Z}_q$ (embedded via $\psi$), derive $Q_r:\mathrm{GF}(p)^n\to\mathrm{GF}(p)^e$ approximating $\mathrm{mod}_q:\{0,1\}^n\to\mathbb{Z}_q$. For $r\in\mathbb{Z}_q^n$, define $Q_r(x):=A(\psi(q-\mathrm{mod}'_q(r)),\,Q(A(\psi(r_1),\psi(x_1)),\dots,A(\psi(r_n),\psi(x_n))))$, where $A:\mathrm{GF}(p)^e\times\mathrm{GF}(p)^e\to\mathrm{GF}(p)^e$ is an $e$-long sequence of $e$-variate polynomials computing a representation of addition mod $q$.

<a id="pdf-988dc9f0ae91-p020-b001"></a>
<!-- pdf-source: page=20; block=1; confidence=0.98 -->
# Appendix: Low degree polynomials and approximating Majority

<a id="pdf-988dc9f0ae91-p020-b002"></a>
<!-- pdf-source: page=20; block=2; confidence=0.90 -->
**Definitions.** $\mathrm{TH}^n_k:\{0,1\}^n\to\{0,1\}$ returns 1 iff its input has at least $k$ ones, i.e. $\mathrm{TH}^n_k(x)=1$ iff $\mathrm{wt}(x)\ge k$; and $\mathrm{TH}^n_k(x)=\mathrm{TH}^{2n+1}_{n+1}(x\,1^{n+1-k}0^k)$, where $\mathrm{TH}^{2n+1}_{n+1}$ is the $(2n+1)$-bit Majority. Hence for any $t\in[n]$ a lower bound for $(2n+1)$-bit Majority follows from a lower bound for $\mathrm{TH}^n_t$. Set $t(n):=\lceil(n+\sqrt{n})/2\rceil$; the goal is to show low degree polynomials over $\mathrm{GF}(2)$ cannot approximate $\mathrm{TH}^n_{t(n)}$ well.

<a id="pdf-988dc9f0ae91-p020-b003"></a>
<!-- pdf-source: page=20; block=3; confidence=0.93 -->
**Lemma 6.** Any $n$-variate polynomial $Q:\mathrm{GF}(2)^n\to\mathrm{GF}(2)$ of degree smaller than $\sqrt{n}$ fails to compute $\mathrm{TH}^n_{t(n)}$ on $\Omega(2^n/\sqrt{n})$ of the $n$-bit inputs; that is, $\Pr_{x\in\{0,1\}^n}[Q(x)\neq\mathrm{TH}^n_t(x)]=\Omega(1/\sqrt{n})$. Combining (contrasting) Lemma 6 with Lemma 2 establishes Part 1 of Theorem 1 for the case $p=2$.

<a id="pdf-988dc9f0ae91-p020-b004"></a>
<!-- pdf-source: page=20; block=4; confidence=0.88 -->
**Proof.** Write $x\le s$ if $x_i\le s_i$ for all $i\in[n]$. Claim: for every $s$ with $\mathrm{wt}(s)\ge\sqrt{n}$, $\sum_{x\le s}Q(x)\equiv0\ (\mathrm{mod}\ 2)$. Proof of claim: for each monomial and $I\subseteq[n]$ with $|I|<\sqrt{n}$, $\sum_{x\le s}\prod_{i\in I}x_i=|\{x:(x\le s)\wedge(\forall i\in I)\,x_i=1\}|=2^{\mathrm{wt}(s)-|I|}$ if $I\subseteq\{i:s_i=1\}$, else $0$; here $\mathrm{wt}(s)-|I|\ge1$ since $\mathrm{wt}(s)\ge\sqrt{n}>|I|$. Let $W_t:=\{x:\mathrm{wt}(x)=t(n)\}$ and $D:=\{x:Q(x)\neq\mathrm{TH}^n_{t(n)}(x)\}$. Form the Boolean matrix with rows $W_t$, columns $D$, entry $(r,c)=\chi(r\ge c)$, and consider its rank over $\mathrm{GF}(2)$. For $r\in W_t$ let $D_r:=\{c\in D:c\le r\}$; then for every $r'\in W_t$, $\sum_{c\in D_r}\chi(r'\ge c)=\sum_{c\in D}\chi((c\le r)\wedge(c\le r'))=\sum_{x\le r\wedge r'}\chi(x\in D)$, with $\wedge$ componentwise. Since $x\in D$ iff $Q(x)+\mathrm{TH}^n_{t(n)}(x)\equiv1\ (\mathrm{mod}\ 2)$, $\sum_{x\le r\wedge r'}\chi(x\in D)\equiv\sum_{x\le r\wedge r'}Q(x)+\sum_{x\le r\wedge r'}\mathrm{TH}^n_{t(n)}(x)\ (\mathrm{mod}\ 2)$.

<a id="pdf-988dc9f0ae91-p021-b001"></a>
<!-- pdf-source: page=21; block=1; confidence=0.90 -->
**Proof (continued).** Since $\mathrm{wt}(r\wedge r')\ge\mathrm{wt}(r)+\mathrm{wt}(r')-n=2t(n)-n\ge\sqrt{n}$, the claim (with $s=r\wedge r'$) gives the first sum $\equiv0\ (\mathrm{mod}\ 2)$. The second sum is $0$ if $r'\neq r$ (then $\mathrm{wt}(r\wedge r')<t(n)$) and $1$ if $r'=r$ (from the term $x=r$). Thus for every $r\in W_t$ a linear combination of columns yields a unit vector with 1 in row $r$, so the matrix has rank $\ge|W_t|$, whence $|D|\ge|W_t|=\binom{n}{t(n)}=\Theta(2^n/\sqrt{n})$. $\square$

<a id="pdf-988dc9f0ae91-p021-b002"></a>
<!-- pdf-source: page=21; block=2; confidence=0.95 -->
**Acknowledgements.** Thanks to Avishay Tal.

**References.** [1] Arora, Barak, *Computational Complexity: A Modern Approach*, Cambridge, 2009. [2] Goldreich, *Computational Complexity: A Conceptual Perspective*, Cambridge, 2008. [3] Jukna, *Boolean Function Complexity: Advances and Frontiers*, Springer, 2012. [4] Smolensky, *Algebraic Methods in the Theory of Lower Bounds for Boolean Circuit Complexity*, 19th STOC, 77–82, 1987. [5] Razborov, *Lower bounds on the size of bounded-depth networks over a complete basis with logical addition*, Mat. Zametki 41(4):598–607, 1987 (Russian; Eng. transl. Math. Notes 41(4):333–338).
