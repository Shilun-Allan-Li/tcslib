<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: d3f46480810510b7214c577966db129b442258da3e59cd7c9a4052b901cc9eba -->

<a id="pdf-d3f464808105-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.86 -->
**Lecture 7: Razborov–Smolensky.** 18.405J/6.841J Advanced Complexity Theory, Spring 2016. Lecturer Mohammad Bavarian; scribe Brian Chen.

<a id="pdf-d3f464808105-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.90 -->
Previous lecture: PARITY ∉ AC0. Goal today is to strengthen this qualitatively by proving lower bounds against a stronger circuit model, following the Sipser program toward understanding P/poly and P.

<a id="pdf-d3f464808105-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.92 -->
Target classes beyond AC0 form the chain AC0 ⊆ AC0[m] ⊆ ACC0 ⊆ TC0. AC0[m] and ACC0 use bounded-depth circuits augmented with mod-m gates.

<a id="pdf-d3f464808105-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.95 -->
**Definition 1.** For an integer m ≥ 2, a mod-m gate has unbounded fan-in and, on inputs y₁,…,y_k, outputs Mod_m(y₁,…,y_k) = 0 if Σyᵢ ≡ 0 (mod m) and 1 if Σyᵢ ≢ 0 (mod m); i.e. it outputs 1 iff the number of 1-inputs is not ≡ 0 mod m.

<a id="pdf-d3f464808105-p001-b005"></a>
<!-- pdf-source: page=1; block=5; confidence=0.95 -->
**Definition 2.** For m ≥ 2, AC0[m] is the class of languages decidable by bounded-depth, polynomial-size circuits with AND, OR, NOT, and mod-m gates.

<a id="pdf-d3f464808105-p001-b006"></a>
<!-- pdf-source: page=1; block=6; confidence=0.90 -->
ACC0 allows mod-m gates for arbitrary m rather than a fixed m; TC0 uses threshold gates, stronger than AND/OR/mod-m. Formal definitions deferred; neither is used in today's main proof.

<a id="pdf-d3f464808105-p001-b007"></a>
<!-- pdf-source: page=1; block=7; confidence=0.82 -->
**Section 3 (Main Theorem).** Statement of today's main result follows.

<a id="pdf-d3f464808105-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.93 -->
**Theorem 3.** PARITY ∉ AC0[3]. More precisely, any depth-d circuit over {AND, OR, NOT, mod-3} computing PARITY has SIZE ≥ 2^{Ω(n^{1/(2d)})}. Strategy: approximate AC0[3] circuits by low-degree polynomials over F₃, then show low-degree polynomials cannot approximate PARITY well, a contradiction.

<a id="pdf-d3f464808105-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.90 -->
**Section 3.1.** Regard {0,1}ⁿ ⊆ F₃ⁿ (F₃ = field of 3 elements). For a circuit C:{0,1}ⁿ→{0,1}, construct a polynomial C̃:F₃ⁿ→F₃ that behaves like C on {0,1}ⁿ.

<a id="pdf-d3f464808105-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.90 -->
Naïve polynomial simulations over F₃: NOT(b)=1−b; AND(b₁,…,b_k)=b₁b₂···b_k; OR(b₁,…,b_k)=1−(1−b₁)···(1−b_k) (de Morgan); mod-3 = (b₁+···+b_k)² (since 0²≡0, 1²≡2²≡1 mod 3; generalizes to modulus m via the (m−1)th power in F_m). Problem: unbounded fan-in AND/OR yield very high degree, so an approximation Ã of C is used instead, matching C on most inputs.

<a id="pdf-d3f464808105-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.93 -->
**Definition 4.** A polynomial p:F₃ⁿ→F₃ is proper if it maps {0,1}ⁿ into {0,1}. (The proof is split into two lemmas, stated next.)

<a id="pdf-d3f464808105-p002-b005"></a>
<!-- pdf-source: page=2; block=5; confidence=0.94 -->
**Lemma 5.** Let t ≥ 1 be an integer and C an AC0[3] circuit of depth d. Then there exists a proper polynomial of degree at most (2t)^d that agrees with C on at least a fraction 1 − SIZE(C)/2^t of all inputs in {0,1}ⁿ. (t is a parameter to be chosen later.)

<a id="pdf-d3f464808105-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.92 -->
**Lemma 6.** Let g:F₃ⁿ→F₃ be a proper polynomial of degree ≤ √n. Then g agrees with PARITY on at most 49/50 of the inputs in {0,1}ⁿ. (The constant 49/50 is not tight; improving √n, e.g. to n^{2/3}, would be more valuable.)

<a id="pdf-d3f464808105-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.90 -->
**Proof.** Suppose for the sake of contradiction that PARITY ∈ AC⁰[3], so that there is some fixed positive integer $d$ such that, for all input sizes, there is a depth-$d$ AC⁰[3] circuit $C$ that computes PARITY. Let $t = \dfrac{n^{1/2d}}{2}$ and apply Lemma 5; then there is a proper polynomial $p$ with degree at most $\sqrt{n}$ that agrees with PARITY on $1 - \dfrac{\mathrm{SIZE}(C)}{2^{n^{1/2d}/2}}$ of inputs. Then, by Lemma 6,
$$\frac{\mathrm{SIZE}(C)}{2^{n^{1/2d}/2}} \ge \frac{1}{50}\,2^{n^{1/2d}},$$
which implies
$$\mathrm{SIZE}(C) \ge \frac{1}{50}\,2^{n^{1/2d}/2},$$
contradicting the polynomial size of $C$ and concluding the proof. More generally, the same proof shows that any bounded-depth circuit using AND, OR, NOT, and mod-3 gates that computes PARITY must have at least this size. ∎

<a id="pdf-d3f464808105-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.85 -->
**Proof (Lemma 5, Section 4).** WLOG the circuit uses only mod-3, NOT, and OR gates (AND is rewritten via de Morgan as one OR with NOT gates; the added NOT gates do not increase the construction's degree). Process layer by layer, approximating each gate in layer k (from the bottom) by a polynomial of degree ≤ (2t)^k.

**Base case:** each bottom-layer input is a degree-1 monomial xᵢ.

**Inductive step (layer k→k+1):** assume layer-k gates approximated by degree ≤ (2t)^k polynomials.
- NOT gate with input approximated by f: output approximated by 1 − f, an exact simulation that does not increase degree (so NOT gates are harmless). 
(OR-gate case continues beyond this page.)

<a id="pdf-d3f464808105-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.90 -->
**Proof (mod-3 gate case).** If a mod-3 gate has its inputs approximated with the polynomials $\tilde f_i$, approximate its output as the polynomial $\left(\sum_{k=1}^{s}\tilde f_i\right)^2$. The degree of this polynomial is at most $2(2t)^k \ge (2t)^{k+1}$. This is also an exact simulation of the mod-3 gate: if the inputs are all in $\{0,1\}$, then the sum counts exactly how many of them are 1 and the final squaring maps $0$ to $0$ and non-zero to $1$.

<a id="pdf-d3f464808105-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.91 -->
**Proof (OR gate case).** To exactly simulate an OR gate with $s$ inputs, we'd have to use something like the polynomial $1-\prod_{i=1}^{s}(1-\tilde f_i)$, which has degree $s(2t)^k \gg (2t)^{k+1}$, so this does not work (unless the gate is narrow enough, $s\ge 2t$; but we cannot rely on that). Instead, we pick $t$ random subsets $L_1,L_2,\dots,L_t\subseteq\{1,2,\dots,s\}$ (where each element has an independent $1/2$ chance of being in each subset), and approximate the OR gate with the polynomial
$$\tilde f = 1-\prod_{i=1}^{t}\left(1-\Big(\sum_{m\in T_i}\tilde f_m\Big)^2\right).$$
We observe that, if all inputs are $0$, then every sum is $0$, every multiplicand in the product is $1$, and $\tilde f=0$, which is correct. If any input, say $\tilde f_j$, is $1$, then each sum $\sum_{m\in T_i}\tilde f_m$ has probability $\ge 1/2$ of being nonzero ($T_i$ has probability $1/2$ of including or excluding $j$, and those give different sums, of which at least one is nonzero); if any sum is nonzero, then its square is $1$, the corresponding multiplicand is $0$, and $\tilde f=1$. Thus, for all inputs, the OR simulation is correct with probability $\ge 1-1/2^t$.

<a id="pdf-d3f464808105-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.90 -->
**Proof (conclusion).** By a union bound over the gates, the resulting polynomial disagrees with at most $\mathrm{SIZE}(C)/2^t$ of all possible inputs, completing the argument. The error bound depends only on the number of AND and OR gates, not the full circuit size.

<a id="pdf-d3f464808105-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.90 -->
Narrow OR gates can be simulated exactly within the allotted degree; the random subset selection matters only for wide OR gates.

<a id="pdf-d3f464808105-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.97 -->
**4.1 Proof of Second Lemma**

<a id="pdf-d3f464808105-p004-b006"></a>
<!-- pdf-source: page=4; block=6; confidence=0.96 -->
**Lemma (Second Lemma).** Let $g$ be a proper polynomial with degree $\le \sqrt{n}$. Then $g$ agrees with PARITY on at most $49/50$ of inputs.

<a id="pdf-d3f464808105-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.85 -->
**Fact (stated without proof).** $\displaystyle\sum_{i=0}^{n/2+\sqrt{n}}\binom{n}{i} \le \frac{49}{50}\cdot 2^n.$

<a id="pdf-d3f464808105-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.83 -->
**Proof (change of basis).** Change basis $\{0,1\}\to\{-1,1\}^n$ via $q(x_1,\dots,x_n)=1+g(x_1+1,\dots,x_n+1)$. Then $q$ maps $\{-1,1\}^n\to\{-1,1\}$, and under this basis PARITY becomes the product $\prod_i x_i$. For each input, $g$ agrees with PARITY iff $q(x_1+1,\dots,x_n+1)$ agrees with $\prod_i(x_i+1)$. The goal is to count inputs where $q(x_1,\dots,x_n)=\prod_i x_i$.

<a id="pdf-d3f464808105-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.95 -->
**Proof (setup of $G$ and $p$).** Let $G=\{u\in\{-1,1\}^n \mid q(u)=\prod_{x\in u} x\}$. Now, pick an arbitrary function $p:G\to \mathbb{F}_3$ and extend it to $p:\mathbb{F}_3^n\to\mathbb{F}_3$. Note that, over finite fields, every function can be expressed as a polynomial, so assume $p$ is a polynomial. The idea below is that the properties of $q$ and $\mathbb{F}_3$ will allow us to simplify $p$ to a low-degree polynomial without affecting its behavior on $G$, which bounds the number of possible ways one could have picked a function $G\to\mathbb{F}_3$ at the start, which in turn bounds $|G|$.

<a id="pdf-d3f464808105-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.86 -->
**Proof (multilinearization).** Write $p=\sum a_{i_1,\dots,i_n}x_1^{i_1}x_2^{i_2}\cdots x_n^{i_n}$. Since $G\subseteq\{-1,1\}^n$ has $x_i^2=1$, reduce every exponent $i_j$ mod 2, so all $i_j\in\{0,1\}$ and $p$ becomes multilinear without changing its behavior on $G$.

<a id="pdf-d3f464808105-p005-b005"></a>
<!-- pdf-source: page=5; block=5; confidence=0.83 -->
**Proof (degree reduction).** Write $p=\sum_{S\subseteq[n]}a_S\prod_{i\in S}x_i$, $[n]=\{1,\dots,n\}$. For $S$ with $|S|\ge n/2$,
$$\prod_{i\in S}x_i=\prod_{i\notin S}x_i\cdot\prod_{i\in[n]}x_i,$$
since doubly-multiplied variables simplify to 1. Replacing the full product by $q$ gives $\prod_{i\notin S}x_i\cdot q(x_1,\dots,x_n)$, of degree $\le n/2+\sqrt{n}$. As this holds on $G$, every term of degree $>n/2+\sqrt{n}$ in $p$ can be replaced by one of degree $\le n/2+\sqrt{n}$ without affecting $p$ on $G$.

<a id="pdf-d3f464808105-p005-b006"></a>
<!-- pdf-source: page=5; block=6; confidence=0.85 -->
**Proof (conclusion).** The remaining polynomials are multilinear of total degree $\le n/2+\sqrt{n}$, so their space has $\mathbb{F}_3$-dimension $<\sum_{i=1}^{n/2+\sqrt{n}}\binom{n}{i}\le \frac{49}{50}2^n$. The dimension of choices for the original $p:G\to\mathbb{F}_3$ equals $|G|$. Therefore $|G|\le \frac{49}{50}2^n$, as desired. $\square$

<a id="pdf-d3f464808105-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.90 -->
**5 Other Comments — 5.1 Generalization.** The proof generalizes to show mod-$p$ gates are not in $\mathrm{AC}^0[q]$ for any distinct primes $p,q$, but not to composite $m$; $\mathrm{AC}^0[m]$ for composite $m$ is much harder (no good bounds for $\mathrm{AC}^0[6]$ for 30 years, only recently changed). Note $\mathrm{AC}^0[6]$ is more powerful than $\mathrm{AC}^0[2]$ and $\mathrm{AC}^0[3]$: a mod-6 gate simulates a mod-2 gate using three copies of every input and a mod-3 gate using two copies.

<a id="pdf-d3f464808105-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.93 -->
**Definition 7 (ACC0).** The class of languages decidable by bounded-depth polynomial-size circuits with AND, OR, NOT, and mod-$m$ gates for any $m$. Since any circuit uses finitely many mod types, $\mathrm{ACC}^0=\bigcup_{m_1,\dots,m_k\in\mathbb{N}}\mathrm{AC}^0[m_1,\dots,m_k]$, where $\mathrm{AC}^0[m_1,m_2,\dots]$ allows AND, OR, NOT, and mod-$m_i$ gates for any $i$.

<a id="pdf-d3f464808105-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.95 -->
**Definition 8 (threshold gate).** For an integer $m$, a threshold gate has unbounded fan-in and outputs 1 iff the number of inputs equal to 1 is $\ge m$.

<a id="pdf-d3f464808105-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.96 -->
**Definition 9 (TC0).** The class of languages decidable by bounded-depth polynomial-size circuits with threshold gates.

<a id="pdf-d3f464808105-p006-b005"></a>
<!-- pdf-source: page=6; block=5; confidence=0.90 -->
**Remark.** Threshold gates are more powerful than AND, OR, and mod-$m$ gates. AND and OR are special cases (threshold $m=$ number of inputs, or $m=1$). Mod-$m$ gates are built from polynomially many threshold and NOT gates in bounded depth: one can test whether the number of 1-inputs is exactly $k$ (copy inputs twice, test $\ge k$ and $\not\ge k+1$); testing each possible value $0,m,\dots$ needs only polynomially many gates since $k$ is polynomial in $n$. Consequently $\mathrm{TC}^0$ is more powerful than $\mathrm{ACC}^0$.

<a id="pdf-d3f464808105-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.98 -->
## 5.3 Looking Forward

<a id="pdf-d3f464808105-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.95 -->
Next lecture proves $\mathrm{NEXP} \not\subseteq \mathrm{ACC}^0$ (Ryan Williams, 2010), the first result beyond the era's prior bounds. Conjectured but unproven: $\mathrm{MAJ} \notin \mathrm{ACC}^0$, where MAJ decides whether a majority of boolean inputs are true. Almost nothing is known about $\mathrm{TC}^0$ lower bounds.

<a id="pdf-d3f464808105-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.97 -->
MIT OpenCourseWare citation/terms-of-use notice for 18.405J / 6.841J *Advanced Complexity Theory*, Spring 2016. No mathematical content.
