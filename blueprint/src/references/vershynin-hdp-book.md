<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: 681b6f3d947f71c023f3d1090e7aa33fd7e302647a6dfb6e69bd272363b6f462 -->

<a id="pdf-681b6f3d947f-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.95 -->
**Title page.** *High-Dimensional Probability: An Introduction with Applications in Data Science*, by Roman Vershynin (UC Irvine). First Edition, dated May 20, 2024; note directs readers to the newer Second Edition online. No mathematical content.

<a id="pdf-681b6f3d947f-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.90 -->
**Contents.** Table of contents (front matter includes Preface and an "Appetizer: using probability to cover a geometric set"). Ch. 1 Preliminaries on random variables: basic quantities, classical inequalities, limit theorems, notes. Ch. 2 Concentration of sums of independent random variables: motivation, Hoeffding's inequality, Chernoff's inequality, degrees of random graphs, sub-gaussian distributions, general Hoeffding's and Khintchine's inequalities, sub-exponential distributions, Bernstein's inequality, notes. Ch. 3 Random vectors in high dimensions: concentration of the norm, covariance matrices and PCA, examples of high-dimensional distributions, sub-gaussian distributions in higher dimensions, Grothendieck's inequality and semidefinite programming, maximum cut for graphs, kernel trick and tightening of Grothendieck's inequality, notes. Ch. 4 Random matrices: preliminaries on matrices, nets/covering and packing numbers, error correcting codes, upper bounds on random sub-gaussian matrices, community detection in networks, two-sided bounds on sub-gaussian matrices. No theorem statements on this page.

<a id="pdf-681b6f3d947f-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.95 -->
**Table of Contents (continued).** Front matter listing chapters and sections with page numbers:

- 4.7 Application: covariance estimation and clustering; 4.8 Notes
- **5 Concentration without independence:** 5.1 Concentration of Lipschitz functions on the sphere; 5.2 Concentration on other metric measure spaces; 5.3 Application: Johnson–Lindenstrauss Lemma; 5.4 Matrix Bernstein's inequality; 5.5 Application: community detection in sparse networks; 5.6 Application: covariance estimation for general distributions; 5.7 Notes
- **6 Quadratic forms, symmetrization and contraction:** 6.1 Decoupling; 6.2 Hanson–Wright Inequality; 6.3 Concentration of anisotropic random vectors; 6.4 Symmetrization; 6.5 Random matrices with non-i.i.d. entries; 6.6 Application: matrix completion; 6.7 Contraction Principle; 6.8 Notes
- **7 Random processes:** 7.1 Basic concepts and examples; 7.2 Slepian's inequality; 7.3 Sharp bounds on Gaussian matrices; 7.4 Sudakov's minoration inequality; 7.5 Gaussian width; 7.6 Stable dimension, stable rank, and Gaussian complexity; 7.7 Random projections of sets; 7.8 Notes
- **8 Chaining:** 8.1 Dudley's inequality; 8.2 Application: empirical processes; 8.3 VC dimension; 8.4 Application: statistical learning theory; 8.5 Generic chaining; 8.6 Talagrand's majorizing measure and comparison theorems; 8.7 Chevet's inequality; 8.8 Notes
- **9 Deviations of random matrices and geometric consequences:** 9.1 Matrix deviation inequality; 9.2 Random matrices, random projections and covariance estimation; 9.3 Johnson–Lindenstrauss Lemma for infinite sets; 9.4 Random sections: M* bound and Escape Theorem; 9.5 Notes

<a id="pdf-681b6f3d947f-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.90 -->
**Table of Contents (continued).**

- **10 Sparse Recovery:** 10.1 High-dimensional signal recovery problems; 10.2 Signal recovery based on M* bound; 10.3 Recovery of sparse signals; 10.4 Low-rank matrix recovery; 10.5 Exact recovery and the restricted isometry property; 10.6 Lasso algorithm for sparse regression; 10.7 Notes
- **11 Dvoretzky–Milman's Theorem:** 11.1 Deviations of random matrices with respect to general norms; 11.2 Johnson–Lindenstrauss embeddings and sharper Chevet inequality; 11.3 Dvoretzky–Milman's Theorem; 11.4 Notes
- Bibliography

<a id="pdf-681b6f3d947f-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.95 -->
**Preface.** Textbook on high-dimensional probability aimed at doctoral/advanced masters students and beginning researchers in data sciences. Subject: probability theory of random objects in R^n for large dimension n, emphasizing random vectors, random matrices, and random projections. Core techniques taught: concentration inequalities, covering/packing arguments, decoupling and symmetrization, chaining and comparison for stochastic processes, and VC-dimension combinatorics. Applications integrated: covariance estimation, semidefinite programming, networks, statistical learning, error-correcting codes, clustering, matrix completion, dimension reduction, sparse signal recovery, and sparse regression. Prerequisites: a rigorous (Masters/PhD-level) probability course, strong undergraduate linear algebra, and familiarity with basic metric/normed space notions.

<a id="pdf-681b6f3d947f-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.95 -->
**Preface (continued).** Assumed background includes Hilbert spaces and linear operators; measure theory is helpful but not essential.

<a id="pdf-681b6f3d947f-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.95 -->
Exercises are embedded in the text for immediate self-checking; difficulty is rated by coffee-cup count, from easiest (one) to hardest (four).

<a id="pdf-681b6f3d947f-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.90 -->
Pointers to further sources: [8] on the probabilistic method in discrete math/CS, forthcoming [20] on mathematical data science with CS applications (both accessible to graduate/advanced-undergraduate readers), and graduate lecture notes [212] with more theoretical high-dimensional probability. Each chapter ends with a Notes section.

<a id="pdf-681b6f3d947f-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.92 -->
Thanks to many colleagues for suggestions, corrections, proofreading, and figures, both before and after publication; post-publication corrections are incorporated in the electronic version. Signed Irvine, California, May 12, 2025.

<a id="pdf-681b6f3d947f-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.95 -->
**Appetizer: using probability to cover a geometric set.** Opening chapter motivating probabilistic reasoning in geometry.

<a id="pdf-681b6f3d947f-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.97 -->
**Definition (convex combination).** A convex combination of points $z_1,\dots,z_m \in \mathbb{R}^n$ is a linear combination $\sum_{i=1}^m \lambda_i z_i$ with $\lambda_i \ge 0$ and $\sum_{i=1}^m \lambda_i = 1$. (0.1)

<a id="pdf-681b6f3d947f-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.97 -->
**Definition (convex hull).** For $T \subset \mathbb{R}^n$, $\mathrm{conv}(T) := \{\text{convex combinations of } z_1,\dots,z_m \in T \text{ for } m \in \mathbb{N}\}$, i.e. the set of all convex combinations of finite collections of points in $T$.

<a id="pdf-681b6f3d947f-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.90 -->
Figure 0.1: illustration of the convex hull of a point set (major U.S. cities). The number $m$ of points in a convex combination is a priori unrestricted, but Caratheodory's theorem shows $m \le n+1$ suffices.

<a id="pdf-681b6f3d947f-p009-b005"></a>
<!-- pdf-source: page=9; block=5; confidence=0.97 -->
**Theorem 0.0.1 (Caratheodory's theorem).** Every point in $\mathrm{conv}(T)$, for $T \subset \mathbb{R}^n$, can be expressed as a convex combination of at most $n+1$ points from $T$.

<a id="pdf-681b6f3d947f-p009-b006"></a>
<!-- pdf-source: page=9; block=6; confidence=0.90 -->
The bound $n+1$ is optimal: it is attained for a simplex $T$ (a set of $n+1$ points in general position). The text then begins to consider a relaxed requirement (sentence continues on the next page).

<a id="pdf-681b6f3d947f-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.97 -->
# Appetizer: using probability to cover a geometric set

<a id="pdf-681b6f3d947f-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.94 -->
Motivates *approximating* a point $x \in \operatorname{conv}(T)$ rather than exactly representing it as a convex combination, and asks whether fewer than $n+1$ points suffice — claiming the required count need not depend on the dimension $n$.

<a id="pdf-681b6f3d947f-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.96 -->
**Theorem 0.0.2 (Approximate Carathéodory's theorem).** Let $T \subset \mathbb{R}^n$ with $\operatorname{diam}(T) \le 1$. Then for every $x \in \operatorname{conv}(T)$ and every integer $k$ there exist points $x_1,\dots,x_k \in T$ such that
$$\Big\| x - \tfrac{1}{k}\sum_{j=1}^{k} x_j \Big\|_2 \le \frac{1}{\sqrt{k}}.$$
Footnote: $\operatorname{diam}(T) = \sup\{\|s-t\|_2 : s,t \in T\}$; for a general $T$ the bound becomes $\operatorname{diam}(T)/\sqrt{k}$.

<a id="pdf-681b6f3d947f-p010-b004"></a>
<!-- pdf-source: page=10; block=4; confidence=0.93 -->
Two notable features: the number $k$ of points is independent of the dimension $n$, and the convex-combination coefficients can all be taken equal to $1/k$ (repetitions among the $x_i$ allowed).

<a id="pdf-681b6f3d947f-p010-b005"></a>
<!-- pdf-source: page=10; block=5; confidence=0.95 -->
**Proof.** (Empirical method of B. Maurey.) By translating, assume the radius of $T$ is bounded by $1$: $\|t\|_2 \le 1$ for all $t \in T$ (0.2). Write $x = \sum_{i=1}^m \lambda_i z_i$ as a convex combination of $z_i \in T$ (0.1). Interpreting the $\lambda_i$ as probabilities, define a random vector $Z$ with $\mathbb{P}\{Z = z_i\} = \lambda_i$; then $\mathbb{E}\,Z = \sum_{i=1}^m \lambda_i z_i = x$. For independent copies $Z_1, Z_2, \dots$ of $Z$, the strong law of large numbers gives $\tfrac{1}{k}\sum_{j=1}^k Z_j \to x$ almost surely. Computing the variance:
$$\mathbb{E}\Big\| x - \tfrac{1}{k}\sum_{j=1}^k Z_j \Big\|_2^2 = \frac{1}{k^2}\,\mathbb{E}\Big\|\sum_{j=1}^k (Z_j - x)\Big\|_2^2 = \frac{1}{k^2}\sum_{j=1}^k \mathbb{E}\|Z_j - x\|_2^2.$$

<a id="pdf-681b6f3d947f-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.95 -->
**Proof (continued).** The last identity uses $\mathbb{E}(Z_i - x) = 0$ (sum-of-variances, Exercise 0.0.3). Bounding each term: $\mathbb{E}\|Z_j - x\|_2^2 = \mathbb{E}\|Z - \mathbb{E}Z\|_2^2 = \mathbb{E}\|Z\|_2^2 - \|\mathbb{E}Z\|_2^2 \le \mathbb{E}\|Z\|_2^2 \le 1$ (since $Z \in T$ and (0.2)). Hence $\mathbb{E}\big\| x - \tfrac{1}{k}\sum_{j=1}^k Z_j \big\|_2^2 \le \tfrac{1}{k}$, so some realization satisfies $\big\| x - \tfrac{1}{k}\sum_{j=1}^k Z_j \big\|_2^2 \le \tfrac{1}{k}$; each $Z_j \in T$, completing the proof. $\blacksquare$

<a id="pdf-681b6f3d947f-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.95 -->
**Exercise 0.0.3.** Verify the two variance identities used above: (a) for independent mean-zero random vectors $Z_1,\dots,Z_k$ in $\mathbb{R}^n$, $\ \mathbb{E}\big\|\sum_{j=1}^k Z_j\big\|_2^2 = \sum_{j=1}^k \mathbb{E}\|Z_j\|_2^2$; (b) for any random vector $Z$ in $\mathbb{R}^n$, $\ \mathbb{E}\|Z - \mathbb{E}Z\|_2^2 = \mathbb{E}\|Z\|_2^2 - \|\mathbb{E}Z\|_2^2$.

<a id="pdf-681b6f3d947f-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.93 -->
Introduces a computational-geometry application: given $P \subset \mathbb{R}^n$, cover it by balls of radius $\varepsilon$; asks for the smallest number of balls and their placement (Figure 0.2).

<a id="pdf-681b6f3d947f-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.96 -->
**Corollary 0.0.4 (Covering polytopes by balls).** Let $P$ be a polytope in $\mathbb{R}^n$ with $N$ vertices and $\operatorname{diam}(P) \le 1$. Then $P$ can be covered by at most $N^{\lceil 1/\varepsilon^2 \rceil}$ Euclidean balls of radius $\varepsilon > 0$.

<a id="pdf-681b6f3d947f-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.95 -->
**Proof.** Set $k := \lceil 1/\varepsilon^2 \rceil$ and $\mathcal{N} := \big\{ \tfrac{1}{k}\sum_{j=1}^k x_j : x_j \text{ vertices of } P \big\}$. Since $P = \operatorname{conv}(T)$ with $T$ its vertex set, Theorem 0.0.2 places every $x \in P$ within distance $1/\sqrt{k} \le \varepsilon$ of some point of $\mathcal{N}$, so the $\varepsilon$-balls centered at $\mathcal{N}$ cover $P$. There are $N^k$ ways to choose $k$ vertices with repetition, hence $|\mathcal{N}| \le N^k = N^{\lceil 1/\varepsilon^2 \rceil}$. $\blacksquare$

<a id="pdf-681b6f3d947f-p012-b003"></a>
<!-- pdf-source: page=12; block=3; confidence=0.93 -->
Notes that the covering problem is revisited via packing (Section 4.2), entropy and coding (Section 4.3), and random processes (Chapters 7–8).

<a id="pdf-681b6f3d947f-p012-b004"></a>
<!-- pdf-source: page=12; block=4; confidence=0.95 -->
**Exercise 0.0.5 (Sum of binomial coefficients).** Prove, for all integers $m \in [1,n]$,
$$\Big(\frac{n}{m}\Big)^m \le \binom{n}{m} \le \sum_{k=0}^m \binom{n}{k} \le \Big(\frac{en}{m}\Big)^m.$$
Hint: multiply by $(m/n)^m$, replace it by $(m/n)^k$ on the left, and apply the Binomial Theorem.

<a id="pdf-681b6f3d947f-p012-b005"></a>
<!-- pdf-source: page=12; block=5; confidence=0.95 -->
**Exercise 0.0.6 (Improved covering).** Show that in Corollary 0.0.4, $(C + C\varepsilon^2 N)^{\lceil 1/\varepsilon^2 \rceil}$ balls suffice, for an absolute constant $C$ — slightly stronger than $N^{\lceil 1/\varepsilon^2 \rceil}$ for small $\varepsilon$. Hint: the number of unordered $k$-element subsets chosen with repetition from an $N$-element set is $\binom{N+k-1}{k}$; simplify using Exercise 0.0.5.

<a id="pdf-681b6f3d947f-p012-b006"></a>
<!-- pdf-source: page=12; block=6; confidence=0.96 -->
## 0.0.1 Notes

<a id="pdf-681b6f3d947f-p012-b007"></a>
<!-- pdf-source: page=12; block=7; confidence=0.94 -->
This section illustrates the probabilistic method (further combinatorial illustrations in [8]). Maurey's empirical method originates in [166]; B. Carl used it for covering-number bounds [49], including those in Corollary 0.0.4 and Exercise 0.0.6, and the bound of Exercise 0.0.6 is sharp [49, 50].

<a id="pdf-681b6f3d947f-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.95 -->
**Chapter 1 — Preliminaries on random variables.** Recalls basic probability theory: expectation, variance, and moments (§1.1); classical inequalities (§1.2); and the two fundamental limit theorems, the law of large numbers and the central limit theorem (§1.3).

<a id="pdf-681b6f3d947f-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.95 -->
**Section 1.1 (Basic quantities).** For a random variable $X$: expectation (mean) $\mathbb{E}\,X$ and variance $\mathrm{Var}(X) = \mathbb{E}(X - \mathbb{E}\,X)^2$. Moment generating function $M_X(t) = \mathbb{E}\,e^{tX}$, $t \in \mathbb{R}$. For $p>0$: $p$-th moment $\mathbb{E}\,X^p$ and $p$-th absolute moment $\mathbb{E}\,|X|^p$. The $L^p$ norm is $\|X\|_{L^p} = (\mathbb{E}\,|X|^p)^{1/p}$ for $p \in (0,\infty)$, extended to $p=\infty$ by $\|X\|_{L^\infty} = \operatorname{ess\,sup}|X|$. (Notational convention: nonlinear functions bind before expectation, so $\mathbb{E}\,f(X)$ means $\mathbb{E}[f(X)]$.)

<a id="pdf-681b6f3d947f-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.95 -->
**Definition ($L^p$ spaces).** $L^p = L^p(\Omega,\Sigma,P) = \{X : \|X\|_{L^p} < \infty\}$. For $p \in [1,\infty]$, $\|\cdot\|_{L^p}$ is a norm and $L^p$ is a Banach space (by Minkowski's inequality (1.4)); for $p<1$ the triangle inequality fails and it is not a norm. The case $p=2$ gives a Hilbert space with inner product $\langle X,Y\rangle_{L^2} = \mathbb{E}\,XY$ and $\|X\|_{L^2} = (\mathbb{E}\,|X|^2)^{1/2}$ (1.1). Standard deviation: $\|X - \mathbb{E}\,X\|_{L^2} = \sqrt{\mathrm{Var}(X)} = \sigma(X)$. Covariance: $\mathrm{cov}(X,Y) = \mathbb{E}(X-\mathbb{E}\,X)(Y-\mathbb{E}\,Y) = \langle X - \mathbb{E}\,X,\, Y - \mathbb{E}\,Y\rangle_{L^2}$ (1.2).

<a id="pdf-681b6f3d947f-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.90 -->
**Remark 1.1.1 (Geometry of random variables).** Viewing random variables as vectors in $L^2$, identity (1.2) interprets covariance geometrically: the more $X - \mathbb{E}\,X$ and $Y - \mathbb{E}\,Y$ are aligned, the larger their inner product and covariance.

<a id="pdf-681b6f3d947f-p014-b003"></a>
<!-- pdf-source: page=14; block=3; confidence=0.93 -->
**Section 1.2 (Classical inequalities).** **Jensen's inequality:** for any random variable $X$ and convex $\varphi:\mathbb{R}\to\mathbb{R}$, $\varphi(\mathbb{E}\,X) \le \mathbb{E}\,\varphi(X)$. Consequence: $\|X\|_{L^p}$ is nondecreasing in $p$, i.e. $\|X\|_{L^p} \le \|X\|_{L^q}$ for $0 \le p \le q \le \infty$ (1.3), since $\varphi(x)=x^{q/p}$ is convex when $q/p \ge 1$. (A function $\varphi$ is convex if $\varphi(\lambda x + (1-\lambda)y) \le \lambda\varphi(x) + (1-\lambda)\varphi(y)$ for $\lambda \in [0,1]$.)

<a id="pdf-681b6f3d947f-p014-b004"></a>
<!-- pdf-source: page=14; block=4; confidence=0.95 -->
**Minkowski's inequality.** For $p \in [1,\infty]$ and $X,Y \in L^p$: $\|X+Y\|_{L^p} \le \|X\|_{L^p} + \|Y\|_{L^p}$ (1.4). This is the triangle inequality, showing $\|\cdot\|_{L^p}$ is a norm for $p \in [1,\infty]$.

<a id="pdf-681b6f3d947f-p014-b005"></a>
<!-- pdf-source: page=14; block=5; confidence=0.95 -->
**Cauchy–Schwarz inequality.** For $X,Y \in L^2$: $|\mathbb{E}\,XY| \le \|X\|_{L^2}\,\|Y\|_{L^2}$.

<a id="pdf-681b6f3d947f-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.95 -->
**Hölder's inequality.** For conjugate exponents $p,q \in (1,\infty)$ with $1/p + 1/q = 1$, and $X \in L^p$, $Y \in L^q$: $|\mathbb{E}\,XY| \le \|X\|_{L^p}\,\|Y\|_{L^q}$. Also holds for the pair $p=1$, $q=\infty$.

<a id="pdf-681b6f3d947f-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.95 -->
**Definition (CDF and tail).** The cumulative distribution function of $X$ is $F_X(t) = P\{X \le t\}$, $t \in \mathbb{R}$. The tail is $P\{X > t\} = 1 - F_X(t)$, often more convenient to work with.

<a id="pdf-681b6f3d947f-p015-b003"></a>
<!-- pdf-source: page=15; block=3; confidence=0.97 -->
**Lemma 1.2.1 (Integral identity).** For a non-negative random variable $X$, $\mathbb{E}\,X = \int_0^\infty P\{X > t\}\,dt$. Both sides are finite or infinite simultaneously.

<a id="pdf-681b6f3d947f-p015-b004"></a>
<!-- pdf-source: page=15; block=4; confidence=0.96 -->
**Proof.** Represent any $x \ge 0$ as $x = \int_0^x 1\,dt = \int_0^\infty \mathbf{1}_{\{t<x\}}\,dt$. Substitute $X$ for $x$ and take expectations: $\mathbb{E}\,X = \mathbb{E}\int_0^\infty \mathbf{1}_{\{t<X\}}\,dt = \int_0^\infty \mathbb{E}\,\mathbf{1}_{\{t<X\}}\,dt = \int_0^\infty P\{t < X\}\,dt$, exchanging expectation and integration by Fubini–Tonelli. $\square$

<a id="pdf-681b6f3d947f-p015-b005"></a>
<!-- pdf-source: page=15; block=5; confidence=0.95 -->
**Exercise 1.2.2 (Generalized integral identity).** Prove, for any (not necessarily non-negative) random variable $X$: $\mathbb{E}\,X = \int_0^\infty P\{X > t\}\,dt - \int_{-\infty}^0 P\{X < t\}\,dt$.

<a id="pdf-681b6f3d947f-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.97 -->
**Exercise 1.2.3 (p-moments via tails).** For a random variable $X$ and $p \in (0,\infty)$, show that $\mathbb{E}|X|^p = \int_0^\infty p t^{p-1} \, \mathbb{P}\{|X| > t\}\, dt$ whenever the right-hand side is finite. Hint: apply the integral identity for $|X|^p$ and change variables.

<a id="pdf-681b6f3d947f-p016-b002"></a>
<!-- pdf-source: page=16; block=2; confidence=0.98 -->
**Proposition 1.2.4 (Markov's Inequality).** For any non-negative random variable $X$ and $t > 0$, $\mathbb{P}\{X \ge t\} \le \dfrac{\mathbb{E}X}{t}$.

<a id="pdf-681b6f3d947f-p016-b003"></a>
<!-- pdf-source: page=16; block=3; confidence=0.97 -->
**Proof.** Fix $t > 0$. Using the identity $x = x\mathbf{1}_{\{x \ge t\}} + x\mathbf{1}_{\{x < t\}}$, substitute $X$ and take expectations: $\mathbb{E}X = \mathbb{E}[X\mathbf{1}_{\{X \ge t\}}] + \mathbb{E}[X\mathbf{1}_{\{X < t\}}] \ge \mathbb{E}[t\mathbf{1}_{\{X \ge t\}}] + 0 = t\,\mathbb{P}\{X \ge t\}$. Divide by $t$. $\square$

<a id="pdf-681b6f3d947f-p016-b004"></a>
<!-- pdf-source: page=16; block=4; confidence=0.98 -->
**Corollary 1.2.5 (Chebyshev's inequality).** For a random variable $X$ with mean $\mu$ and variance $\sigma^2$, and any $t > 0$, $\mathbb{P}\{|X - \mu| \ge t\} \le \dfrac{\sigma^2}{t^2}$.

<a id="pdf-681b6f3d947f-p016-b005"></a>
<!-- pdf-source: page=16; block=5; confidence=0.97 -->
**Exercise 1.2.6.** Deduce Chebyshev's inequality by squaring both sides of $|X - \mu| \ge t$ and applying Markov's inequality.

<a id="pdf-681b6f3d947f-p016-b006"></a>
<!-- pdf-source: page=16; block=6; confidence=0.96 -->
**Remark 1.2.7.** Proposition 2.5.2 will establish relations among moment generating functions, $L^p$ norms, and tails.

<a id="pdf-681b6f3d947f-p016-b007"></a>
<!-- pdf-source: page=16; block=7; confidence=0.95 -->
**1.3 Limit theorems.** For independent random variables $X_1,\dots,X_N$, variance is additive: $\operatorname{Var}(X_1 + \cdots + X_N) = \operatorname{Var}(X_1) + \cdots + \operatorname{Var}(X_N)$.

<a id="pdf-681b6f3d947f-p017-b001"></a>
<!-- pdf-source: page=17; block=1; confidence=0.96 -->
If additionally the $X_i$ are i.i.d. with mean $\mu$ and variance $\sigma^2$, dividing the variance identity by $N^2$ gives $\operatorname{Var}\!\left(\frac{1}{N}\sum_{i=1}^N X_i\right) = \frac{\sigma^2}{N}$ (1.5). The sample-mean variance shrinks to $0$ as $N \to \infty$, motivating the law of large numbers.

<a id="pdf-681b6f3d947f-p017-b002"></a>
<!-- pdf-source: page=17; block=2; confidence=0.98 -->
**Theorem 1.3.1 (Strong law of large numbers).** Let $X_1, X_2, \dots$ be i.i.d. with mean $\mu$, and $S_N = X_1 + \cdots + X_N$. Then $\dfrac{S_N}{N} \to \mu$ almost surely as $N \to \infty$.

<a id="pdf-681b6f3d947f-p017-b003"></a>
<!-- pdf-source: page=17; block=3; confidence=0.97 -->
The central limit theorem identifies the limiting distribution as the standard normal $N(0,1)$, with density $f(x) = \dfrac{1}{\sqrt{2\pi}} e^{-x^2/2}$, $x \in \mathbb{R}$ (1.6).

<a id="pdf-681b6f3d947f-p017-b004"></a>
<!-- pdf-source: page=17; block=4; confidence=0.97 -->
**Theorem 1.3.2 (Lindeberg-Lévy central limit theorem).** Let $X_1, X_2, \dots$ be i.i.d. with mean $\mu$ and variance $\sigma^2$, and $S_N = X_1 + \cdots + X_N$. Normalize to zero mean and unit variance: $Z_N := \dfrac{S_N - \mathbb{E}S_N}{\sqrt{\operatorname{Var}(S_N)}} = \dfrac{1}{\sigma\sqrt{N}} \sum_{i=1}^N (X_i - \mu)$. Then $Z_N \to N(0,1)$ in distribution as $N \to \infty$.

<a id="pdf-681b6f3d947f-p017-b005"></a>
<!-- pdf-source: page=17; block=5; confidence=0.96 -->
Convergence in distribution means the CDF of $Z_N$ converges pointwise to that of $N(0,1)$; equivalently, for every $t \in \mathbb{R}$, $\mathbb{P}\{Z_N \ge t\} \to \mathbb{P}\{g \ge t\} = \dfrac{1}{\sqrt{2\pi}} \int_t^\infty e^{-x^2/2}\, dx$ as $N \to \infty$, where $g \sim N(0,1)$.

<a id="pdf-681b6f3d947f-p018-b001"></a>
<!-- pdf-source: page=18; block=1; confidence=0.97 -->
**Exercise 1.3.3.** Let $X_1, X_2, \dots$ be i.i.d. with mean $\mu$ and finite variance. Show that $\mathbb{E}\left|\frac{1}{N}\sum_{i=1}^N X_i - \mu\right| = O\!\left(\frac{1}{\sqrt{N}}\right)$ as $N \to \infty$.

<a id="pdf-681b6f3d947f-p018-b002"></a>
<!-- pdf-source: page=18; block=2; confidence=0.97 -->
**de Moivre-Laplace theorem.** Special case with $X_i \sim \mathrm{Ber}(p)$, $p \in (0,1)$: $X_i$ takes values $1,0$ with probabilities $p, 1-p$; $\mathbb{E}X_i = p$, $\operatorname{Var}(X_i) = p(1-p)$. The sum $S_N = X_1 + \cdots + X_N$ has the binomial distribution $\mathrm{Binom}(N,p)$. The CLT gives, as $N \to \infty$, $\dfrac{S_N - Np}{\sqrt{Np(1-p)}} \to N(0,1)$ in distribution (1.7).

<a id="pdf-681b6f3d947f-p018-b003"></a>
<!-- pdf-source: page=18; block=3; confidence=0.96 -->
When the $X_i \sim \mathrm{Ber}(p_i)$ have parameters decaying so fast that $\mathbb{E}S_N = O(1)$, the CLT fails and $S_N$ converges to a Poisson limit instead. A random variable $Z \sim \mathrm{Pois}(\lambda)$ takes values in $\{0,1,2,\dots\}$ with $\mathbb{P}\{Z = k\} = e^{-\lambda}\dfrac{\lambda^k}{k!}$, $k = 0,1,2,\dots$ (1.8).

<a id="pdf-681b6f3d947f-p018-b004"></a>
<!-- pdf-source: page=18; block=4; confidence=0.98 -->
**Theorem 1.3.4 (Poisson Limit Theorem).** Let $X_{N,i}$, $1 \le i \le N$, be independent with $X_{N,i} \sim \mathrm{Ber}(p_{N,i})$, and $S_N = \sum_{i=1}^N X_{N,i}$. Assume, as $N \to \infty$, $\max_{i \le N} p_{N,i} \to 0$ and $\mathbb{E}S_N = \sum_{i=1}^N p_{N,i} \to \lambda < \infty$. Then $S_N \to \mathrm{Pois}(\lambda)$ in distribution.

<a id="pdf-681b6f3d947f-p019-b001"></a>
<!-- pdf-source: page=19; block=1; confidence=0.98 -->
## 1.4 Notes

<a id="pdf-681b6f3d947f-p019-b002"></a>
<!-- pdf-source: page=19; block=2; confidence=0.95 -->
Standard graduate-level material. Proofs of the strong law of large numbers (Theorem 1.3.1) and the Lindeberg–Lévy CLT (Theorem 1.3.2) are found in [72, Secs. 1.7, 2.4] and [23, Secs. 6, 27]. Proposition 1.2.4 and Corollary 1.2.5 are both due to Chebyshev, but Proposition 1.2.4 is called Markov's inequality by tradition.

<a id="pdf-681b6f3d947f-p020-b001"></a>
<!-- pdf-source: page=20; block=1; confidence=0.97 -->
# 2. Concentration of sums of independent random variables

<a id="pdf-681b6f3d947f-p020-b002"></a>
<!-- pdf-source: page=20; block=2; confidence=0.94 -->
Introduces concentration inequalities: Hoeffding's (§2.2, §2.6), Chernoff's (§2.3), Bernstein's (§2.8); and two distribution classes, sub-gaussian (§2.5) and sub-exponential (§2.7). Applications: randomized algorithms (§2.2) and random graphs (§2.4).

<a id="pdf-681b6f3d947f-p020-b003"></a>
<!-- pdf-source: page=20; block=3; confidence=0.97 -->
## 2.1 Why concentration inequalities?

<a id="pdf-681b6f3d947f-p020-b004"></a>
<!-- pdf-source: page=20; block=4; confidence=0.94 -->
Concentration inequalities bound how a random variable $X$ deviates from its mean $\mu$, typically as two-sided tail bounds $P\{|X-\mu|>t\}\le \text{(small)}$. The simplest is Chebyshev's inequality (Corollary 1.2.5), which is general but often too weak, illustrated below with the binomial distribution.

<a id="pdf-681b6f3d947f-p020-b005"></a>
<!-- pdf-source: page=20; block=5; confidence=0.93 -->
**Question 2.1.1.** For $N$ tosses of a fair coin, bound the probability of getting at least $\tfrac34 N$ heads. Let $S_N$ be the number of heads, so $\mathbb{E}\,S_N = N/2$ and $\mathrm{Var}(S_N) = N/4$. Chebyshev gives
$$P\!\left\{S_N \ge \tfrac34 N\right\} \le P\!\left\{\left|S_N - \tfrac{N}{2}\right| \ge \tfrac{N}{4}\right\} \le \frac{4}{N}. \tag{2.1}$$
Thus the probability decays at least linearly in $N$.

<a id="pdf-681b6f3d947f-p021-b001"></a>
<!-- pdf-source: page=21; block=1; confidence=0.93 -->
Writing $S_N = \sum_{i=1}^{N} X_i$ with $X_i$ i.i.d. Bernoulli$(1/2)$ (heads indicators), the De Moivre–Laplace CLT (1.7) says the normalized count $Z_N = (S_N - N/2)/\sqrt{N/4}$ converges to $N(0,1)$. Hence for large $N$,
$$P\!\left\{S_N \ge \tfrac34 N\right\} = P\!\left\{Z_N \ge \sqrt{N/4}\right\} \approx P\!\left\{g \ge \sqrt{N/4}\right\}, \tag{2.2}$$
with $g \sim N(0,1)$. A good normal tail bound is needed to see how this decays.

<a id="pdf-681b6f3d947f-p021-b002"></a>
<!-- pdf-source: page=21; block=2; confidence=0.95 -->
**Proposition 2.1.2 (Tails of the normal distribution).** For $g \sim N(0,1)$ and all $t>0$,
$$\left(\frac1t - \frac1{t^3}\right)\frac{1}{\sqrt{2\pi}}\,e^{-t^2/2} \le P\{g \ge t\} \le \frac1t\cdot\frac{1}{\sqrt{2\pi}}\,e^{-t^2/2}.$$
In particular, for $t \ge 1$ the tail is bounded by the density:
$$P\{g \ge t\} \le \frac{1}{\sqrt{2\pi}}\,e^{-t^2/2}. \tag{2.3}$$

<a id="pdf-681b6f3d947f-p021-b003"></a>
<!-- pdf-source: page=21; block=3; confidence=0.94 -->
**Proof.** Upper bound: in $P\{g\ge t\} = \frac{1}{\sqrt{2\pi}}\int_t^\infty e^{-x^2/2}\,dx$ substitute $x = t+y$, giving
$$P\{g\ge t\} = \frac{1}{\sqrt{2\pi}}\int_0^\infty e^{-t^2/2}e^{-ty}e^{-y^2/2}\,dy \le \frac{1}{\sqrt{2\pi}}e^{-t^2/2}\int_0^\infty e^{-ty}\,dy,$$
using $e^{-y^2/2}\le 1$; the last integral equals $1/t$. Lower bound: from the identity $\int_t^\infty (1-3x^{-4})e^{-x^2/2}\,dx = \left(\tfrac1t - \tfrac1{t^3}\right)e^{-t^2/2}$. $\blacksquare$

<a id="pdf-681b6f3d947f-p022-b001"></a>
<!-- pdf-source: page=22; block=1; confidence=0.95 -->
Continuing from (2.2), one expects the probability of at least $\tfrac34 N$ heads to be smaller than $\frac{1}{\sqrt{2\pi}}e^{-N/8}$ (2.4), an exponential decay in $N$ far better than the linear Chebyshev decay (2.1). However (2.4) does not follow rigorously from the CLT: although the normal approximation in (2.2) is valid, its error decays slower than linearly in $N$, as quantified next.

<a id="pdf-681b6f3d947f-p022-b002"></a>
<!-- pdf-source: page=22; block=2; confidence=0.97 -->
**Theorem 2.1.3 (Berry-Esseen central limit theorem).** In the setting of Theorem 1.3.2, for every $N$ and every $t\in\mathbb{R}$,
$$\big|\,P\{Z_N \ge t\} - P\{g \ge t\}\,\big| \le \frac{\rho}{\sqrt{N}},$$
where $\rho = \mathbb{E}\,|X_1-\mu|^3/\sigma^3$ and $g \sim N(0,1)$.

<a id="pdf-681b6f3d947f-p022-b003"></a>
<!-- pdf-source: page=22; block=3; confidence=0.95 -->
The approximation error in (2.2) is of order $1/\sqrt{N}$, which destroys the desired exponential decay (2.4). This cannot be improved in general: for even $N$, Stirling's approximation gives $P\{S_N = N/2\} = 2^{-N}\binom{N}{N/2} \asymp 1/\sqrt{N}$, hence $P\{Z_N = 0\} \asymp 1/\sqrt{N}$, whereas the continuous normal law has $P\{g = 0\} = 0$; so the error must be of order $1/\sqrt{N}$.

<a id="pdf-681b6f3d947f-p022-b004"></a>
<!-- pdf-source: page=22; block=4; confidence=0.94 -->
Summary: the CLT approximates $S_N = X_1 + \dots + X_N$ by the normal law, whose tails are light and exponentially decaying, but its approximation error decays slower than linearly. This large error obstructs proving exponential-tail concentration for $S_N$, motivating direct approaches that bypass the CLT.

<a id="pdf-681b6f3d947f-p022-b005"></a>
<!-- pdf-source: page=22; block=5; confidence=0.95 -->
Notation: $f \asymp g$ means equivalence up to constant factors, i.e. there exist constants $c, C > 0$ with $cf(x) \le g(x) \le Cf(x)$ for all $x$ (or all sufficiently large $x$). The one-sided versions are written $f \lesssim g$ and $f \gtrsim g$.

<a id="pdf-681b6f3d947f-p023-b001"></a>
<!-- pdf-source: page=23; block=1; confidence=0.96 -->
**Exercise 2.1.4 (Truncated normal distribution).** For $g \sim N(0,1)$ and all $t \ge 1$, show that
$$\mathbb{E}\, g^2 \mathbf{1}_{\{g>t\}} = t\cdot\frac{1}{\sqrt{2\pi}}e^{-t^2/2} + P\{g>t\} \le \Big(t + \tfrac1t\Big)\frac{1}{\sqrt{2\pi}}e^{-t^2/2}.$$
Hint: integrate by parts.

<a id="pdf-681b6f3d947f-p023-b002"></a>
<!-- pdf-source: page=23; block=2; confidence=0.96 -->
**2.2 Hoeffding's inequality.** A simple concentration inequality for sums of i.i.d. symmetric Bernoulli random variables.

<a id="pdf-681b6f3d947f-p023-b003"></a>
<!-- pdf-source: page=23; block=3; confidence=0.97 -->
**Definition 2.2.1 (Symmetric Bernoulli distribution).** $X$ has the symmetric Bernoulli (Rademacher) distribution if $P\{X=-1\} = P\{X=1\} = \tfrac12$. Equivalently, $X$ is Bernoulli$(1/2)$ iff $Z = 2X-1$ is symmetric Bernoulli.

<a id="pdf-681b6f3d947f-p023-b004"></a>
<!-- pdf-source: page=23; block=4; confidence=0.97 -->
**Theorem 2.2.2 (Hoeffding's inequality).** Let $X_1,\dots,X_N$ be independent symmetric Bernoulli random variables and $a = (a_1,\dots,a_N)\in\mathbb{R}^N$. Then for any $t \ge 0$,
$$P\Big\{\sum_{i=1}^N a_i X_i \ge t\Big\} \le \exp\!\Big(-\frac{t^2}{2\|a\|_2^2}\Big).$$

<a id="pdf-681b6f3d947f-p023-b005"></a>
<!-- pdf-source: page=23; block=5; confidence=0.96 -->
**Proof.** Assume WLOG $\|a\|_2 = 1$. Multiply by $\lambda > 0$, exponentiate, and apply Markov's inequality:
$$P\Big\{\sum_i a_i X_i \ge t\Big\} = P\Big\{\exp\big(\lambda\sum_i a_i X_i\big) \ge e^{\lambda t}\Big\} \le e^{-\lambda t}\,\mathbb{E}\exp\big(\lambda\sum_i a_i X_i\big). \tag{2.5}$$
This reduces the problem to bounding the MGF of the sum, which by independence factorizes:
$$\mathbb{E}\exp\big(\lambda\sum_{i=1}^N a_i X_i\big) = \prod_{i=1}^N \mathbb{E}\exp(\lambda a_i X_i). \tag{2.6}$$

<a id="pdf-681b6f3d947f-p024-b001"></a>
<!-- pdf-source: page=24; block=1; confidence=0.97 -->
**Proof (continued).** Since each $X_i$ takes $\pm 1$ with probability $1/2$,
$$\mathbb{E}\exp(\lambda a_i X_i) = \frac{e^{\lambda a_i} + e^{-\lambda a_i}}{2} = \cosh(\lambda a_i).$$

<a id="pdf-681b6f3d947f-p024-b002"></a>
<!-- pdf-source: page=24; block=2; confidence=0.97 -->
**Exercise 2.2.3 (Bounding the hyperbolic cosine).** Show that $\cosh(x) \le \exp(x^2/2)$ for all $x\in\mathbb{R}$. Hint: compare Taylor expansions of both sides.

<a id="pdf-681b6f3d947f-p024-b003"></a>
<!-- pdf-source: page=24; block=3; confidence=0.96 -->
**Proof (continued).** The bound gives $\mathbb{E}\exp(\lambda a_i X_i) \le \exp(\lambda^2 a_i^2/2)$. Substituting into (2.6) and (2.5),
$$P\Big\{\sum_i a_i X_i \ge t\Big\} \le e^{-\lambda t}\prod_{i=1}^N \exp(\lambda^2 a_i^2/2) = \exp\!\Big(-\lambda t + \frac{\lambda^2}{2}\sum_i a_i^2\Big) = \exp\!\Big(-\lambda t + \frac{\lambda^2}{2}\Big),$$
using $\|a\|_2 = 1$. Optimizing over $\lambda > 0$, the minimum is at $\lambda = t$, yielding $P\{\sum_i a_i X_i \ge t\} \le \exp(-t^2/2)$. $\square$

<a id="pdf-681b6f3d947f-p024-b004"></a>
<!-- pdf-source: page=24; block=4; confidence=0.95 -->
Hoeffding's inequality is a concentration version of the CLT: with $\|a\|_2 = 1$ it gives the tail $e^{-t^2/2}$, matching the standard normal tail bound (2.3), even though the two distributions are not exponentially close. Applied to Question 2.1.1, after rescaling from Bernoulli to symmetric Bernoulli, $P\{\text{at least } \tfrac34 N \text{ heads}\} \le \exp(-N/8).$

<a id="pdf-681b6f3d947f-p025-b001"></a>
<!-- pdf-source: page=25; block=1; confidence=0.97 -->
## 2.2 Hoeffding's inequality

<a id="pdf-681b6f3d947f-p025-b002"></a>
<!-- pdf-source: page=25; block=2; confidence=0.95 -->
**Remark 2.2.4 (Non-asymptotic results).** Hoeffding's inequality holds for every fixed $N$ (not only as $N\to\infty$), and it strengthens as $N$ grows; this non-asymptotic character makes such concentration inequalities useful in data science, where $N$ is the sample size.

<a id="pdf-681b6f3d947f-p025-b003"></a>
<!-- pdf-source: page=25; block=3; confidence=0.93 -->
Applying the one-sided Hoeffding bound to $-X_i$ gives a bound on $P\{-S \ge t\}$; combined with $P\{S \ge t\}$ via $P\{|S| \ge t\} = P\{S \ge t\} + P\{-S \ge t\}$ (where $S = \sum_{i=1}^N a_i X_i$), the bound doubles.

<a id="pdf-681b6f3d947f-p025-b004"></a>
<!-- pdf-source: page=25; block=4; confidence=0.97 -->
**Theorem 2.2.5 (Hoeffding's inequality, two-sided).** Let $X_1,\dots,X_N$ be independent symmetric Bernoulli random variables and $a = (a_1,\dots,a_N) \in \mathbb{R}^N$. Then for any $t>0$,
$$P\left\{\left|\sum_{i=1}^N a_i X_i\right| \ge t\right\} \le 2\exp\left(-\frac{t^2}{2\|a\|_2^2}\right).$$

<a id="pdf-681b6f3d947f-p025-b005"></a>
<!-- pdf-source: page=25; block=5; confidence=0.94 -->
The MGF-based proof extends beyond symmetric Bernoulli variables; e.g. it yields the following bound for general bounded random variables.

<a id="pdf-681b6f3d947f-p025-b006"></a>
<!-- pdf-source: page=25; block=6; confidence=0.97 -->
**Theorem 2.2.6 (Hoeffding's inequality for general bounded random variables).** Let $X_1,\dots,X_N$ be independent with $X_i \in [m_i, M_i]$ for every $i$. Then for any $t>0$,
$$P\left\{\sum_{i=1}^N (X_i - \mathbb{E}X_i) \ge t\right\} \le \exp\left(-\frac{2t^2}{\sum_{i=1}^N (M_i - m_i)^2}\right).$$

<a id="pdf-681b6f3d947f-p025-b007"></a>
<!-- pdf-source: page=25; block=7; confidence=0.96 -->
**Exercise 2.2.7.** Prove Theorem 2.2.6, possibly with an absolute constant in place of the $2$ in the exponent.

<a id="pdf-681b6f3d947f-p025-b008"></a>
<!-- pdf-source: page=25; block=8; confidence=0.96 -->
**Exercise 2.2.8 (Boosting randomized algorithms).** A randomized decision algorithm returns the correct answer with probability $\tfrac12 + \delta$, $\delta>0$. Running it $N$ times and taking the majority vote gives the correct answer with probability $\ge 1-\varepsilon$ (for $\varepsilon \in (0,1)$) provided
$$N \ge \frac{1}{2\delta^2}\ln\left(\frac{1}{\varepsilon}\right).$$
Hint: apply Hoeffding to the indicators of wrong answers.

<a id="pdf-681b6f3d947f-p026-b001"></a>
<!-- pdf-source: page=26; block=1; confidence=0.95 -->
**Exercise 2.2.9 (Robust estimation of the mean).** Estimate $\mu = \mathbb{E}X$ from an i.i.d. sample $X_1,\dots,X_N$; an estimate is $\varepsilon$-accurate if it lies in $(\mu-\varepsilon, \mu+\varepsilon)$, with $\sigma^2 = \operatorname{Var}X$.
(a) A sample of size $N = O(\sigma^2/\varepsilon^2)$ suffices for an $\varepsilon$-accurate estimate with probability $\ge 3/4$ (hint: use the sample mean $\hat\mu := \tfrac1N \sum_{i=1}^N X_i$).
(b) A sample of size $N = O(\log(\delta^{-1})\,\sigma^2/\varepsilon^2)$ suffices with probability $\ge 1-\delta$ (hint: take the median of $O(\log(\delta^{-1}))$ weak estimates from part (a)).

<a id="pdf-681b6f3d947f-p026-b002"></a>
<!-- pdf-source: page=26; block=2; confidence=0.95 -->
**Exercise 2.2.10 (Small ball probabilities).** Let $X_1,\dots,X_N$ be non-negative independent random variables with continuous distributions whose densities are uniformly bounded by $1$.
(a) Show the MGF satisfies $\mathbb{E}\exp(-tX_i) \le \tfrac{1}{t}$ for all $t>0$.
(b) Deduce that for any $\varepsilon>0$, $P\left\{\sum_{i=1}^N X_i \le \varepsilon N\right\} \le (e\varepsilon)^N$.
Hint: rewrite $\sum X_i \le \varepsilon N$ as $\sum(-X_i/\varepsilon) \ge -N$ and mimic the Hoeffding proof, using part (a) for the MGF.

<a id="pdf-681b6f3d947f-p026-b003"></a>
<!-- pdf-source: page=26; block=3; confidence=0.94 -->
## 2.3 Chernoff's inequality

The general Hoeffding bound (Theorem 2.2.6) can be too conservative, e.g. for Bernoulli $X_i$ with small parameters $p_i$ where $S_N$ is approximately Poisson (Theorem 1.3.4): Hoeffding ignores the magnitudes of $p_i$ and gives a Gaussian tail far from the true Poisson tail. Chernoff's inequality is sensitive to the $p_i$.

<a id="pdf-681b6f3d947f-p026-b004"></a>
<!-- pdf-source: page=26; block=4; confidence=0.97 -->
**Theorem 2.3.1 (Chernoff's inequality).** Let $X_i$ be independent Bernoulli random variables with parameters $p_i$, let $S_N = \sum_{i=1}^N X_i$, and $\mu = \mathbb{E}S_N$. Then for any $t > \mu$,
$$P\{S_N \ge t\} \le e^{-\mu}\left(\frac{e\mu}{t}\right)^t.$$

<a id="pdf-681b6f3d947f-p026-b005"></a>
<!-- pdf-source: page=26; block=5; confidence=0.93 -->
Footnote to Exercise 2.2.9(a): precisely, there is an absolute constant $C$ such that $N \ge C\sigma^2/\varepsilon^2$ implies $P\{|\hat\mu - \mu| \le \varepsilon\} \ge 3/4$, with $\hat\mu$ the sample mean.

<a id="pdf-681b6f3d947f-p027-b001"></a>
<!-- pdf-source: page=27; block=1; confidence=0.96 -->
**Proof.** Using the MGF method as in Theorem 2.2.2: multiply $S_N \ge t$ by $\lambda$, exponentiate, and apply Markov's inequality with independence to get
$$P\{S_N \ge t\} \le e^{-\lambda t}\prod_{i=1}^N \mathbb{E}\exp(\lambda X_i). \quad (2.7)$$
For each Bernoulli variable, $\mathbb{E}\exp(\lambda X_i) = e^\lambda p_i + (1-p_i) = 1 + (e^\lambda - 1)p_i \le \exp[(e^\lambda-1)p_i]$, using $1+x \le e^x$. Hence $\prod_{i} \mathbb{E}\exp(\lambda X_i) \le \exp[(e^\lambda-1)\mu]$, giving
$$P\{S_N \ge t\} \le e^{-\lambda t}\exp[(e^\lambda-1)\mu],$$
valid for all $\lambda>0$. Substituting $\lambda = \ln(t/\mu) > 0$ (since $t>\mu$) and simplifying completes the proof. $\square$

<a id="pdf-681b6f3d947f-p027-b002"></a>
<!-- pdf-source: page=27; block=2; confidence=0.96 -->
**Exercise 2.3.2 (Chernoff's inequality: lower tails).** Modify the proof of Theorem 2.3.1 to show that for any $t < \mu$,
$$P\{S_N \le t\} \le e^{-\mu}\left(\frac{e\mu}{t}\right)^t.$$

<a id="pdf-681b6f3d947f-p027-b003"></a>
<!-- pdf-source: page=27; block=3; confidence=0.96 -->
**Exercise 2.3.3 (Poisson tails).** Let $X \sim \mathrm{Pois}(\lambda)$. Show that for any $t > \lambda$,
$$P\{X \ge t\} \le e^{-\lambda}\left(\frac{e\lambda}{t}\right)^t. \quad (2.8)$$
Hint: combine Chernoff's inequality with the Poisson limit theorem (Theorem 1.3.4).

<a id="pdf-681b6f3d947f-p027-b004"></a>
<!-- pdf-source: page=27; block=4; confidence=0.94 -->
**Remark 2.3.4 (Poisson tails).** The bound (2.8) is sharp: using Stirling's formula $k! \approx \sqrt{2\pi k}\,(k/e)^k$, the pmf (1.8) of $X \sim \mathrm{Pois}(\lambda)$ satisfies
$$P\{X = k\} \approx \frac{1}{\sqrt{2\pi k}}\, e^{-\lambda}\left(\frac{e\lambda}{k}\right)^k. \quad (2.9)$$
Thus the whole-tail bound (2.8) has essentially the same form as the probability of the single smallest value $k$ in that tail.

<a id="pdf-681b6f3d947f-p028-b001"></a>
<!-- pdf-source: page=28; block=1; confidence=0.85 -->
Trailing sentence: the ratio between the two quantities is the factor $\sqrt{2\pi k}$, negligible since both quantities are exponentially small in $k$.

<a id="pdf-681b6f3d947f-p028-b002"></a>
<!-- pdf-source: page=28; block=2; confidence=0.95 -->
**Exercise 2.3.5 (Chernoff's inequality: small deviations).** In the setting of Theorem 2.3.1, show that for $\delta \in (0,1]$,
$$\mathbb{P}\{|S_N - \mu| \ge \delta\mu\} \le 2e^{-c\mu\delta^2},$$
with $c>0$ an absolute constant. Hint: apply Theorem 2.3.1 and Exercise 2.3.2 with $t=(1\pm\delta)\mu$ and analyze for small $\delta$.

<a id="pdf-681b6f3d947f-p028-b003"></a>
<!-- pdf-source: page=28; block=3; confidence=0.95 -->
**Exercise 2.3.6 (Poisson distribution near the mean).** For $X \sim \mathrm{Pois}(\lambda)$ and $t \in (0,\lambda]$, show
$$\mathbb{P}\{|X-\lambda| \ge t\} \le 2\exp\!\left(-\frac{ct^2}{\lambda}\right).$$
Hint: combine Exercise 2.3.5 with the Poisson limit theorem (Theorem 1.3.4).

<a id="pdf-681b6f3d947f-p028-b004"></a>
<!-- pdf-source: page=28; block=4; confidence=0.90 -->
**Remark 2.3.7 (Large and small deviations).** Two tail regimes for $\mathrm{Pois}(\lambda)$: near the mean $\lambda$ (small deviations) the tail resembles $N(\lambda,\lambda)$; far right of the mean (large deviations) the tail is heavier, decaying like $(\lambda/t)^t$. See Figure 2.1.

<a id="pdf-681b6f3d947f-p028-b005"></a>
<!-- pdf-source: page=28; block=5; confidence=0.90 -->
Figure 2.1: probability mass function of $\mathrm{Pois}(\lambda)$ with $\lambda=10$; approximately normal near the mean $\lambda$, with heavier tails to the right.

<a id="pdf-681b6f3d947f-p028-b006"></a>
<!-- pdf-source: page=28; block=6; confidence=0.95 -->
**Exercise 2.3.8 (Normal approximation to Poisson).** For $X \sim \mathrm{Pois}(\lambda)$, show that as $\lambda \to \infty$,
$$\frac{X-\lambda}{\sqrt{\lambda}} \to N(0,1)$$
in distribution. Hint: derive from the CLT using that a sum of independent Poissons is Poisson.

<a id="pdf-681b6f3d947f-p029-b001"></a>
<!-- pdf-source: page=29; block=1; confidence=0.98 -->
# 2.4 Application: degrees of random graphs

<a id="pdf-681b6f3d947f-p029-b002"></a>
<!-- pdf-source: page=29; block=2; confidence=0.90 -->
Application of Chernoff's inequality to random graphs. The Erdős–Rényi model $G(n,p)$: on $n$ vertices, each distinct pair is joined independently with probability $p$; used as a simple stochastic model for large real-world networks.

<a id="pdf-681b6f3d947f-p029-b003"></a>
<!-- pdf-source: page=29; block=3; confidence=0.92 -->
Figure 2.2: a random graph from $G(n,p)$ with $n=200$, $p=1/40$.

<a id="pdf-681b6f3d947f-p029-b004"></a>
<!-- pdf-source: page=29; block=4; confidence=0.90 -->
**Definition.** The degree of a vertex is the number of incident edges. In $G(n,p)$ the expected degree of every vertex is $(n-1)p =: d$. Claim to follow: relatively dense graphs ($d \gtrsim \log n$) are almost regular with high probability (all degrees $\approx d$).

<a id="pdf-681b6f3d947f-p029-b005"></a>
<!-- pdf-source: page=29; block=5; confidence=0.96 -->
**Proposition 2.4.1 (Dense graphs are almost regular).** There is an absolute constant $C$ such that: for $G \sim G(n,p)$ with expected degree $d \ge C\log n$, with high probability (e.g. $0.9$) all vertices of $G$ have degrees between $0.9d$ and $1.1d$.

<a id="pdf-681b6f3d947f-p029-b006"></a>
<!-- pdf-source: page=29; block=6; confidence=0.95 -->
**Proof.** Combine Chernoff's inequality with a union bound. Fix vertex $i$; its degree $d_i$ is a sum of $n-1$ independent $\mathrm{Ber}(p)$ indicators, so by Chernoff (Exercise 2.3.5),
$$\mathbb{P}\{|d_i - d| \ge 0.1d\} \le 2e^{-cd}.$$

<a id="pdf-681b6f3d947f-p030-b001"></a>
<!-- pdf-source: page=30; block=1; confidence=0.95 -->
**Proof (continued).** Union bound over all $n$ vertices:
$$\mathbb{P}\{\exists i \le n : |d_i - d| \ge 0.1d\} \le \sum_{i=1}^{n} \mathbb{P}\{|d_i-d|\ge 0.1d\} \le n\cdot 2e^{-cd}.$$
If $d \ge C\log n$ for large enough absolute $C$, this is $\le 0.1$; hence the complementary event satisfies
$$\mathbb{P}\{\forall i \le n : |d_i - d| < 0.1d\} \ge 0.9. \qquad\blacksquare$$

<a id="pdf-681b6f3d947f-p030-b002"></a>
<!-- pdf-source: page=30; block=2; confidence=0.90 -->
Sparser graphs ($d = o(\log n)$) are not almost regular, but useful degree bounds still hold. In the following exercises $n \to \infty$; $p$ need not be constant in $n$.

<a id="pdf-681b6f3d947f-p030-b003"></a>
<!-- pdf-source: page=30; block=3; confidence=0.93 -->
**Exercise 2.4.2 (Bounding degrees of sparse graphs).** For $G \sim G(n,p)$ with $d = O(\log n)$, show that with high probability (0.9) all vertices have degrees $O(\log n)$. Hint: modify the proof of Proposition 2.4.1.

<a id="pdf-681b6f3d947f-p030-b004"></a>
<!-- pdf-source: page=30; block=4; confidence=0.93 -->
**Exercise 2.4.3 (Bounding degrees of very sparse graphs).** For $G \sim G(n,p)$ with $d = O(1)$, show that with high probability (0.9) all vertices have degrees $O\!\left(\dfrac{\log n}{\log\log n}\right).$

<a id="pdf-681b6f3d947f-p030-b005"></a>
<!-- pdf-source: page=30; block=5; confidence=0.92 -->
**Exercise 2.4.4 (Sparse graphs are not almost regular).** For $G \sim G(n,p)$ with $d = o(\log n)$, show that with high probability (0.9) $G$ has a vertex of degree $10d$. Hint: the $d_i$ are not independent; replace them by independent $d_i'$ (count over not all vertices), then use Poisson approximation (2.9).

<a id="pdf-681b6f3d947f-p030-b006"></a>
<!-- pdf-source: page=30; block=6; confidence=0.90 -->
**Exercise 2.4.5 (Very sparse graphs are far from being regular).** Statement begins ("Consider ...") but is cut off on this page; gives a lower bound on degrees matching the upper bound of Exercise 2.4.3 for $d = O(1)$. Footnote 3: $10d$ is assumed integer, and the factor 10 can be any constant.

<a id="pdf-681b6f3d947f-p031-b001"></a>
<!-- pdf-source: page=31; block=1; confidence=0.90 -->
**Exercise.** For a random graph $G \sim G(n,p)$ with expected degrees $d = O(1)$, show that with high probability (say $0.9$) $G$ has a vertex of degree $\Omega\!\left(\frac{\log n}{\log\log n}\right)$.

<a id="pdf-681b6f3d947f-p031-b002"></a>
<!-- pdf-source: page=31; block=2; confidence=0.99 -->
# 2.5 Sub-gaussian distributions

<a id="pdf-681b6f3d947f-p031-b003"></a>
<!-- pdf-source: page=31; block=3; confidence=0.92 -->
Motivation: extend concentration beyond Bernoulli variables to a class containing the normal distribution. Guiding question — which $X_i$ satisfy a Hoeffding-type bound
$$P\!\left\{\Big|\sum_{i=1}^{N} a_i X_i\Big| \ge t\right\} \le 2\exp\!\left(-\frac{c t^2}{\lVert a\rVert_2^2}\right)?$$
A single-term case ($\sum a_i X_i = X_i$) reduces to $P\{|X_i|>t\} \le 2e^{-ct^2}$, forcing $X_i$ to have **sub-gaussian tails**. The sub-gaussian class contains Gaussian, Bernoulli, and all bounded distributions.

<a id="pdf-681b6f3d947f-p031-b004"></a>
<!-- pdf-source: page=31; block=4; confidence=0.97 -->
For $X \sim N(0,1)$, using (2.3) and symmetry, the tail bound is
$$P\{|X|\ge t\} \le 2e^{-t^2/2}\quad\text{for all } t\ge 0. \tag{2.10}$$

<a id="pdf-681b6f3d947f-p031-b005"></a>
<!-- pdf-source: page=31; block=5; confidence=0.90 -->
**Exercise 2.5.1 (Moments of the normal distribution).** Show that for each $p\ge 1$, $X \sim N(0,1)$ satisfies the $L^p$-norm formula (statement continues on next page).

<a id="pdf-681b6f3d947f-p032-b001"></a>
<!-- pdf-source: page=32; block=1; confidence=0.92 -->
For $p\ge 1$ and $X \sim N(0,1)$:
$$\lVert X\rVert_{L^p} = (\mathbb{E}|X|^p)^{1/p} = \sqrt{2}\,\left[\frac{\Gamma((1+p)/2)}{\Gamma(1/2)}\right]^{1/p}.$$
Deduce $\lVert X\rVert_{L^p} = O(\sqrt{p})$ as $p \to \infty$. \tag{2.11}

<a id="pdf-681b6f3d947f-p032-b002"></a>
<!-- pdf-source: page=32; block=2; confidence=0.98 -->
Classical MGF of $X \sim N(0,1)$:
$$\mathbb{E}\exp(\lambda X) = e^{\lambda^2/2}\quad\text{for all }\lambda\in\mathbb{R}. \tag{2.12}$$

<a id="pdf-681b6f3d947f-p032-b003"></a>
<!-- pdf-source: page=32; block=3; confidence=0.96 -->
## 2.5.1 Sub-gaussian properties

For a general $X$, the tail decay (2.10), moment growth (2.11), and MGF growth (2.12) are shown to be equivalent characterizations.

<a id="pdf-681b6f3d947f-p032-b004"></a>
<!-- pdf-source: page=32; block=4; confidence=0.96 -->
**Proposition 2.5.2 (Sub-gaussian properties).** For a random variable $X$, the following are equivalent, with parameters $K_i>0$ differing by at most an absolute constant factor:

(i) $\exists K_1>0$: $P\{|X|\ge t\} \le 2\exp(-t^2/K_1^2)$ for all $t\ge 0$.

(ii) $\exists K_2>0$: $\lVert X\rVert_{L^p} = (\mathbb{E}|X|^p)^{1/p} \le K_2\sqrt{p}$ for all $p\ge 1$.

(iii) $\exists K_3>0$: $\mathbb{E}\exp(\lambda^2 X^2) \le \exp(K_3^2\lambda^2)$ for all $|\lambda|\le 1/K_3$.

(iv) $\exists K_4>0$: $\mathbb{E}\exp(X^2/K_4^2) \le 2$.

Moreover, if $\mathbb{E}X = 0$, then (i)–(iv) are also equivalent to:

(v) $\exists K_5>0$: $\mathbb{E}\exp(\lambda X) \le \exp(K_5^2\lambda^2)$ for all $\lambda\in\mathbb{R}$.

<a id="pdf-681b6f3d947f-p032-b005"></a>
<!-- pdf-source: page=32; block=5; confidence=0.95 -->
Footnote 4: the equivalence means there is an absolute constant $C$ such that property $i$ implies property $j$ with parameter $K_j \le C K_i$ for any two properties $i,j = 1,\dots,5$.

<a id="pdf-681b6f3d947f-p033-b001"></a>
<!-- pdf-source: page=33; block=1; confidence=0.94 -->
**Proof. (i ⇒ ii)** By homogeneity assume $K_1=1$. By the integral identity (Lemma 1.2.1) and change of variables $u=t^p$:
$$\mathbb{E}|X|^p = \int_0^\infty P\{|X|^p\ge u\}\,du = \int_0^\infty P\{|X|\ge t\}\,p t^{p-1}\,dt \le \int_0^\infty 2e^{-t^2} p t^{p-1}\,dt = p\,\Gamma(p/2) \le 3p(p/2)^{p/2},$$
using property (i), $t^2=s$, and $\Gamma(x)\le 3x^x$ for $x\ge 1/2$. Taking the $p$-th root gives (ii) with $K_2\le 3$.

<a id="pdf-681b6f3d947f-p033-b002"></a>
<!-- pdf-source: page=33; block=2; confidence=0.94 -->
**(ii ⇒ iii)** Assume $K_2=1$. Taylor expansion:
$$\mathbb{E}\exp(\lambda^2 X^2) = 1 + \sum_{p=1}^\infty \frac{\lambda^{2p}\mathbb{E}[X^{2p}]}{p!}.$$
Using $\mathbb{E}[X^{2p}]\le (2p)^p$ (from ii) and Stirling $p!\ge (p/e)^p$:
$$\mathbb{E}\exp(\lambda^2 X^2) \le \sum_{p=0}^\infty (2e\lambda^2)^p = \frac{1}{1-2e\lambda^2}$$
provided $2e\lambda^2<1$. Then $1/(1-x)\le e^{2x}$ on $[0,1/2]$ gives $\mathbb{E}\exp(\lambda^2 X^2)\le \exp(4e\lambda^2)$ for $|\lambda|\le 1/\sqrt{e}$, i.e. (iii) with $K_3=2\sqrt{e}$.

<a id="pdf-681b6f3d947f-p033-b003"></a>
<!-- pdf-source: page=33; block=3; confidence=0.95 -->
**(iii ⇒ iv)** Trivial.

**(iv ⇒ i)** Assume $K_4=1$. By Markov's inequality (Prop. 1.2.4):
$$P\{|X|\ge t\} = P\{e^{X^2}\ge e^{t^2}\} \le e^{-t^2}\mathbb{E}e^{X^2} \le 2e^{-t^2}$$
using property (iv). This gives (i) with $K_1=1$.

<a id="pdf-681b6f3d947f-p033-b004"></a>
<!-- pdf-source: page=33; block=4; confidence=0.93 -->
To prove the second part (equivalence with (v) when $\mathbb{E}X=0$), it remains to show $iii \Rightarrow v$ and $v \Rightarrow i$.

<a id="pdf-681b6f3d947f-p034-b001"></a>
<!-- pdf-source: page=34; block=1; confidence=0.97 -->
**Proof (iii ⇒ v).** Assume property iii with $K_3=1$. Using $e^x \le x + e^{x^2}$ (valid for all $x\in\mathbb{R}$) and $\mathbb{E}X=0$: $\mathbb{E}\,e^{\lambda X} \le \mathbb{E}[\lambda X + e^{\lambda^2 X^2}] = \mathbb{E}\,e^{\lambda^2 X^2} \le e^{\lambda^2}$ for $|\lambda|\le 1$ (last step by iii). For $|\lambda|\ge 1$, use $2\lambda x \le \lambda^2 + x^2$: $\mathbb{E}\,e^{\lambda X} \le e^{\lambda^2/2}\,\mathbb{E}\,e^{X^2/2} \le e^{\lambda^2/2}\exp(1/2) \le e^{\lambda^2}$. Hence property v holds with $K_5=1$.

<a id="pdf-681b6f3d947f-p034-b002"></a>
<!-- pdf-source: page=34; block=2; confidence=0.97 -->
**Proof (v ⇒ i).** Assume property v with $K_5=1$. For a parameter $\lambda>0$, by Markov's inequality and property v: $\mathbb{P}\{X\ge t\} = \mathbb{P}\{e^{\lambda X}\ge e^{\lambda t}\} \le e^{-\lambda t}\,\mathbb{E}\,e^{\lambda X} \le e^{-\lambda t}e^{\lambda^2} = e^{-\lambda t + \lambda^2}$. Optimizing at $\lambda=t/2$ gives $\mathbb{P}\{X\ge t\}\le e^{-t^2/4}$. Applying to $-X$ gives $\mathbb{P}\{X\le -t\}\le e^{-t^2/4}$; combining, $\mathbb{P}\{|X|\ge t\}\le 2e^{-t^2/4}$. Thus property i holds with $K_1=2$, completing the proof of the proposition.

<a id="pdf-681b6f3d947f-p034-b003"></a>
<!-- pdf-source: page=34; block=3; confidence=0.98 -->
**Remark 2.5.3.** The constant $2$ in some properties of Proposition 2.5.2 is not special and may be replaced by any absolute constant larger than $1$.

<a id="pdf-681b6f3d947f-p034-b004"></a>
<!-- pdf-source: page=34; block=4; confidence=0.98 -->
**Exercise 2.5.4.** Show that the condition $\mathbb{E}X=0$ is necessary for property v to hold.

<a id="pdf-681b6f3d947f-p034-b005"></a>
<!-- pdf-source: page=34; block=5; confidence=0.97 -->
**Exercise 2.5.5.** (a) For $X\sim N(0,1)$, show $\lambda \mapsto \mathbb{E}\exp(\lambda^2 X^2)$ is finite only in a bounded neighborhood of $0$. (b) If a random variable $X$ satisfies $\mathbb{E}\exp(\lambda^2 X^2) \le \exp(K\lambda^2)$ for all $\lambda\in\mathbb{R}$ and some constant $K$, show $X$ is bounded, i.e. $\|X\|_\infty < \infty$.

<a id="pdf-681b6f3d947f-p035-b001"></a>
<!-- pdf-source: page=35; block=1; confidence=0.98 -->
## 2.5.2 Definition and examples of sub-gaussian distributions

<a id="pdf-681b6f3d947f-p035-b002"></a>
<!-- pdf-source: page=35; block=2; confidence=0.98 -->
**Definition 2.5.6 (Sub-gaussian random variables).** A random variable $X$ satisfying one of the equivalent properties i–iv of Proposition 2.5.2 is called sub-gaussian. Its sub-gaussian norm $\|X\|_{\psi_2}$ is the smallest $K_4$ in property iv:
$$\|X\|_{\psi_2} = \inf\{t>0 : \mathbb{E}\exp(X^2/t^2) \le 2\}. \quad (2.13)$$

<a id="pdf-681b6f3d947f-p035-b003"></a>
<!-- pdf-source: page=35; block=3; confidence=0.98 -->
**Exercise 2.5.7.** Verify that $\|\cdot\|_{\psi_2}$ is a norm on the space of sub-gaussian random variables.

<a id="pdf-681b6f3d947f-p035-b004"></a>
<!-- pdf-source: page=35; block=4; confidence=0.96 -->
Restatement of Proposition 2.5.2: every sub-gaussian $X$ satisfies, for absolute constants $C,c>0$:
$$\mathbb{P}\{|X|\ge t\} \le 2\exp(-ct^2/\|X\|_{\psi_2}^2)\ \text{ for all } t\ge 0; \quad (2.14)$$
$$\|X\|_{L^p} \le C\|X\|_{\psi_2}\sqrt{p}\ \text{ for all } p\ge 1; \quad (2.15)$$
$$\mathbb{E}\exp(X^2/\|X\|_{\psi_2}^2) \le 2;$$
$$\text{if } \mathbb{E}X=0 \text{ then } \mathbb{E}\exp(\lambda X) \le \exp(C\lambda^2\|X\|_{\psi_2}^2)\ \text{ for all } \lambda\in\mathbb{R}. \quad (2.16)$$
Moreover, up to absolute constant factors, $\|X\|_{\psi_2}$ is the smallest number making each inequality valid.

<a id="pdf-681b6f3d947f-p035-b005"></a>
<!-- pdf-source: page=35; block=5; confidence=0.97 -->
**Example 2.5.8.** (a) Gaussian: $X\sim N(0,1)$ is sub-gaussian with $\|X\|_{\psi_2}\le C$ (absolute constant); more generally $X\sim N(0,\sigma^2)$ has $\|X\|_{\psi_2}\le C\sigma$. (b) Bernoulli: for symmetric Bernoulli $X$, since $|X|=1$, $\|X\|_{\psi_2} = 1/\sqrt{\ln 2}$. (c) Bounded: any bounded $X$ is sub-gaussian with $\|X\|_{\psi_2}\le C\|X\|_\infty$ (2.17), where $C=1/\sqrt{\ln 2}$.

<a id="pdf-681b6f3d947f-p035-b006"></a>
<!-- pdf-source: page=35; block=6; confidence=0.98 -->
**Exercise 2.5.9.** Check that the Poisson, exponential, Pareto, and Cauchy distributions are not sub-gaussian.

<a id="pdf-681b6f3d947f-p036-b001"></a>
<!-- pdf-source: page=36; block=1; confidence=0.95 -->
**Exercise 2.5.10 (Maximum of sub-gaussians).** For a sequence $X_1,X_2,\dots$ of (not necessarily independent) sub-gaussian random variables with $K=\max_i\|X_i\|_{\psi_2}$, show $\mathbb{E}\max_i \frac{|X_i|}{\sqrt{1+\log i}} \le CK$, and deduce that for every $N\ge 2$, $\mathbb{E}\max_{i\le N}|X_i| \le CK\sqrt{\log N}$. Hint: set $Y_i := X_i/(CK\sqrt{1+\log i})$, use the sub-gaussian tail (2.14) and a union bound to get $\mathbb{P}\{\exists i: |Y_i|\ge t\}\lesssim e^{-t^2}$ for $t\ge 1$, then apply the integrated tail formula (Lemma 1.2.1), splitting the integral over $[0,1]$ and $[1,\infty)$.

<a id="pdf-681b6f3d947f-p036-b002"></a>
<!-- pdf-source: page=36; block=2; confidence=0.97 -->
**Exercise 2.5.11 (Lower bound).** Show the bound of Exercise 2.5.10 is sharp: for independent $X_1,\dots,X_N\sim N(0,1)$, prove $\mathbb{E}\max_{i\le N} X_i \ge c\sqrt{\log N}$.

<a id="pdf-681b6f3d947f-p036-b003"></a>
<!-- pdf-source: page=36; block=3; confidence=0.98 -->
## 2.6 General Hoeffding's and Khintchine's inequalities

<a id="pdf-681b6f3d947f-p036-b004"></a>
<!-- pdf-source: page=36; block=4; confidence=0.95 -->
Motivation: the characterization of sub-gaussians lets Hoeffding's inequality (Theorem 2.2.2) extend to general sub-gaussian distributions, via a rotation invariance property. For independent $X_i\sim N(0,\sigma_i^2)$, the sum is normal:
$$\sum_{i=1}^N X_i \sim N\Big(0, \sum_{i=1}^N \sigma_i^2\Big). \quad (2.18)$$
This rotation invariance of the normal distribution extends to general sub-gaussians up to an absolute constant.

<a id="pdf-681b6f3d947f-p036-b005"></a>
<!-- pdf-source: page=36; block=5; confidence=0.97 -->
**Proposition 2.6.1 (Sums of independent sub-gaussians).** Let $X_1,\dots,X_N$ be independent, mean-zero, sub-gaussian random variables. Then $\sum_{i=1}^N X_i$ is sub-gaussian, and
$$\Big\|\sum_{i=1}^N X_i\Big\|_{\psi_2}^2 \le C \sum_{i=1}^N \|X_i\|_{\psi_2}^2,$$
where $C$ is an absolute constant.

<a id="pdf-681b6f3d947f-p037-b001"></a>
<!-- pdf-source: page=37; block=1; confidence=0.95 -->
**Proof.** Bound the MGF of the sum: for any λ∈ℝ,

E exp(λ Σ_{i=1}^N X_i) = Π_{i=1}^N E exp(λX_i) (independence) ≤ Π_{i=1}^N exp(Cλ²‖X_i‖²_{ψ₂}) (sub-gaussian property (2.16)) = exp(λ²K²), where K² := C Σ_{i=1}^N ‖X_i‖²_{ψ₂}.

By the equivalence of properties (v) and (iv) in Proposition 2.5.2 and Definition 2.5.6, this MGF bound implies Σ_{i=1}^N X_i is sub-gaussian with ‖Σ_{i=1}^N X_i‖_{ψ₂} ≤ C₁K, C₁ an absolute constant. ∎

<a id="pdf-681b6f3d947f-p037-b002"></a>
<!-- pdf-source: page=37; block=2; confidence=0.97 -->
**Theorem 2.6.2 (General Hoeffding's inequality).** Let X₁,…,X_N be independent, mean-zero, sub-gaussian random variables. Then for every t≥0,

P{ |Σ_{i=1}^N X_i| ≥ t } ≤ 2 exp( −ct² / Σ_{i=1}^N ‖X_i‖²_{ψ₂} ),

with c an absolute constant.

<a id="pdf-681b6f3d947f-p037-b003"></a>
<!-- pdf-source: page=37; block=3; confidence=0.97 -->
**Theorem 2.6.3 (General Hoeffding's inequality).** Let X₁,…,X_N be independent, mean-zero, sub-gaussian random variables and a=(a₁,…,a_N)∈ℝ^N. Then for every t≥0,

P{ |Σ_{i=1}^N a_i X_i| ≥ t } ≤ 2 exp( −ct² / (K²‖a‖²₂) ),

where K = max_i ‖X_i‖_{ψ₂}.

<a id="pdf-681b6f3d947f-p037-b004"></a>
<!-- pdf-source: page=37; block=4; confidence=0.95 -->
**Exercise 2.6.4.** Deduce Hoeffding's inequality for bounded random variables (Theorem 2.2.6) from Theorem 2.6.3, possibly with some absolute constant in place of 2 in the exponent.

<a id="pdf-681b6f3d947f-p037-b005"></a>
<!-- pdf-source: page=37; block=5; confidence=0.90 -->
Application: the general Hoeffding inequality yields the classical Khintchine inequality for the Lᵖ-norms of sums of independent random variables.

<a id="pdf-681b6f3d947f-p038-b001"></a>
<!-- pdf-source: page=38; block=1; confidence=0.94 -->
**Exercise 2.6.5 (Khintchine's inequality).** Let X₁,…,X_N be independent sub-gaussian random variables with zero means and unit variances, and a=(a₁,…,a_N)∈ℝ^N. Prove that for every p∈[2,∞),

(Σ_{i=1}^N a_i²)^{1/2} ≤ ‖Σ_{i=1}^N a_i X_i‖_{Lᵖ} ≤ CK√p (Σ_{i=1}^N a_i²)^{1/2},

where K = max_i ‖X_i‖_{ψ₂} and C is an absolute constant.

<a id="pdf-681b6f3d947f-p038-b002"></a>
<!-- pdf-source: page=38; block=2; confidence=0.90 -->
**Exercise 2.6.6 (Khintchine's inequality for p=1).** In the setting of Exercise 2.6.5, show

c(K)(Σ_{i=1}^N a_i²)^{1/2} ≤ ‖Σ_{i=1}^N a_i X_i‖_{L¹} ≤ (Σ_{i=1}^N a_i²)^{1/2},

where K = max_i ‖X_i‖_{ψ₂} and c(K)>0 may depend only on K. Hint (extrapolation trick): prove ‖Z‖₂ ≤ ‖Z‖₁^{1/4}‖Z‖₃^{3/4} for Z=Σ a_i X_i, and bound ‖Z‖₃ via Khintchine for p=3.

<a id="pdf-681b6f3d947f-p038-b003"></a>
<!-- pdf-source: page=38; block=3; confidence=0.95 -->
**Exercise 2.6.7 (Khintchine's inequality for p∈(0,2)).** State and prove a version of Khintchine's inequality for p∈(0,2). Hint: modify the extrapolation trick of Exercise 2.6.6.

<a id="pdf-681b6f3d947f-p038-b004"></a>
<!-- pdf-source: page=38; block=4; confidence=0.93 -->
**2.6.1 Centering.** Many results (e.g. Hoeffding) assume mean-zero variables; otherwise one centers X_i by subtracting its mean. The L² centering inequality holds: ‖X − EX‖_{L²} ≤ ‖X‖_{L²} (2.19). The goal is an analogous bound for the sub-gaussian norm.

<a id="pdf-681b6f3d947f-p038-b005"></a>
<!-- pdf-source: page=38; block=5; confidence=0.96 -->
**Lemma 2.6.8 (Centering).** If X is a sub-gaussian random variable, then X − EX is sub-gaussian too, and

‖X − EX‖_{ψ₂} ≤ C‖X‖_{ψ₂},

with C an absolute constant.

<a id="pdf-681b6f3d947f-p038-b006"></a>
<!-- pdf-source: page=38; block=6; confidence=0.94 -->
**Proof.** Since ‖·‖_{ψ₂} is a norm (Exercise 2.5.7), the triangle inequality gives

‖X − EX‖_{ψ₂} ≤ ‖X‖_{ψ₂} + ‖EX‖_{ψ₂} (2.20).

It remains to bound the second term. For any constant random variable a, ‖a‖_{ψ₂} ≲ |a| (recall (2.17)); this is applied with a = EX. [Notation a ≲ b means a ≤ Cb for an absolute constant C.]

<a id="pdf-681b6f3d947f-p039-b001"></a>
<!-- pdf-source: page=39; block=1; confidence=0.95 -->
**Proof (cont.).** Bounding the constant term: ‖EX‖_{ψ₂} ≲ |EX| ≤ E|X| (Jensen) = ‖X‖₁ ≲ ‖X‖_{ψ₂} (using (2.15) with p=1). Substituting into (2.20) completes the proof. ∎

<a id="pdf-681b6f3d947f-p039-b002"></a>
<!-- pdf-source: page=39; block=2; confidence=0.95 -->
**Exercise 2.6.9.** Show that, unlike (2.19), the centering inequality of Lemma 2.6.8 does not hold with C=1.

<a id="pdf-681b6f3d947f-p039-b003"></a>
<!-- pdf-source: page=39; block=3; confidence=0.92 -->
**2.7 Sub-exponential distributions.** The sub-gaussian class, though large, omits distributions with heavier-than-gaussian tails. Motivating example: a standard normal vector g=(g₁,…,g_N)∈ℝ^N with independent N(0,1) coordinates, and its Euclidean norm ‖g‖₂ = (Σ_{i=1}^N g_i²)^{1/2}. Although the g_i are sub-gaussian, the g_i² are not: by Gaussian tails (Proposition 2.1.2),

P{g_i² > t} = P{|g| > √t} ∼ exp(−(√t)²/2) = exp(−t/2),

an exponential tail, strictly heavier than sub-gaussian, so Hoeffding (Theorem 2.6.2) cannot be applied to ‖g‖₂. This section treats distributions with at least exponential tail decay; Section 2.8 proves a Hoeffding-type analog for them. The development parallels Section 2.5.

<a id="pdf-681b6f3d947f-p039-b004"></a>
<!-- pdf-source: page=39; block=4; confidence=0.90 -->
**Proposition 2.7.1 (Sub-exponential properties).** Let X be a random variable. The following properties are equivalent, with the parameters K_i > 0 in each differing by at most an absolute constant factor (precisely: there is an absolute constant C such that property i implies property j with parameter K_j ≤ CK_i for any two properties i,j). [The list of equivalent properties continues beyond this page.]

<a id="pdf-681b6f3d947f-p040-b001"></a>
<!-- pdf-source: page=40; block=1; confidence=0.96 -->
**Proposition 2.7.1 (continued).** For a random variable $X$ the following are equivalent, with parameters $K_i$ differing by at most an absolute constant factor:

- (a) Tail bound: $\mathbb{P}\{|X|\ge t\}\le 2\exp(-t/K_1)$ for all $t\ge 0$.
- (b) Moment growth: $\|X\|_{L^p}=(\mathbb{E}|X|^p)^{1/p}\le K_2\,p$ for all $p\ge 1$.
- (c) MGF of $|X|$: $\mathbb{E}\exp(\lambda|X|)\le\exp(K_3\lambda)$ for all $0\le\lambda\le 1/K_3$.
- (d) MGF of $|X|$ bounded at a point: $\mathbb{E}\exp(|X|/K_4)\le 2$.

Moreover, if $\mathbb{E}X=0$, then (a)–(d) are also equivalent to:
- (e) MGF of $X$: $\mathbb{E}\exp(\lambda X)\le\exp(K_5^2\lambda^2)$ for all $|\lambda|\le 1/K_5$.

<a id="pdf-681b6f3d947f-p040-b002"></a>
<!-- pdf-source: page=40; block=2; confidence=0.95 -->
**Proof (b ⇒ e).** WLOG $K_2=1$. Taylor-expanding and using $\mathbb{E}X=0$: $\mathbb{E}\exp(\lambda X)=1+\sum_{p\ge 2}\lambda^p\,\mathbb{E}[X^p]/p!$. Property (b) gives $\mathbb{E}[X^p]\le p^p$ and Stirling gives $p!\ge (p/e)^p$, so
$$\mathbb{E}\exp(\lambda X)\le 1+\sum_{p\ge 2}(e\lambda)^p=1+\frac{(e\lambda)^2}{1-e\lambda}$$
provided $|e\lambda|<1$. If $|e\lambda|\le 1/2$ this is $\le 1+2e^2\lambda^2\le\exp(2e^2\lambda^2)$. Hence $\mathbb{E}\exp(\lambda X)\le\exp(2e^2\lambda^2)$ for $|\lambda|\le 1/(2e)$, giving (e) with $K_5=2e$.

**(e ⇒ b).** WLOG $K_5=1$. Uses the numeric inequality $|x|^p\le p^p(e^x+e^{-x})$ (continued on next page).

<a id="pdf-681b6f3d947f-p041-b001"></a>
<!-- pdf-source: page=41; block=1; confidence=0.96 -->
**Proof (e ⇒ b, cont.).** The inequality $|x|^p\le p^p(e^x+e^{-x})$ holds for all $x\in\mathbb{R}$, $p>0$ (verify by dividing by $p^p$ and taking $p$-th roots). Setting $x=X$ and taking expectations: $\mathbb{E}|X|^p\le p^p(\mathbb{E}e^X+\mathbb{E}e^{-X})$. Property (e) gives $\mathbb{E}e^X\le e$ and $\mathbb{E}e^{-X}\le e$, so $\mathbb{E}|X|^p\le 2e\,p^p$, yielding (b) with $K_2=2e$. $\square$

<a id="pdf-681b6f3d947f-p041-b002"></a>
<!-- pdf-source: page=41; block=2; confidence=0.95 -->
**Exercise 2.7.2.** Prove the equivalence of properties (a)–(d) in Proposition 2.7.1 by adapting the proof of Proposition 2.5.2.

<a id="pdf-681b6f3d947f-p041-b003"></a>
<!-- pdf-source: page=41; block=3; confidence=0.95 -->
**Exercise 2.7.3.** For distributions with tail decay $\exp(-ct^\alpha)$ or faster ($\alpha=2$: sub-gaussian; $\alpha=1$: sub-exponential), state and prove an analog of Proposition 2.7.1.

<a id="pdf-681b6f3d947f-p041-b004"></a>
<!-- pdf-source: page=41; block=4; confidence=0.95 -->
**Exercise 2.7.4.** Argue that the bound in property (c) cannot be extended to all $|\lambda|\le 1/K_3$.

<a id="pdf-681b6f3d947f-p041-b005"></a>
<!-- pdf-source: page=41; block=5; confidence=0.96 -->
**Definition 2.7.5 (Sub-exponential random variables).** $X$ is sub-exponential if it satisfies one of the equivalent properties (a)–(d) of Proposition 2.7.1. Its sub-exponential norm $\|X\|_{\psi_1}$ is the smallest $K_3$ in property (c):
$$\|X\|_{\psi_1}=\inf\{t>0:\mathbb{E}\exp(|X|/t)\le 2\}.\qquad(2.21)$$

<a id="pdf-681b6f3d947f-p041-b006"></a>
<!-- pdf-source: page=41; block=6; confidence=0.93 -->
Every sub-gaussian distribution is sub-exponential, and the square of a sub-gaussian variable is sub-exponential.

<a id="pdf-681b6f3d947f-p041-b007"></a>
<!-- pdf-source: page=41; block=7; confidence=0.97 -->
**Lemma 2.7.6.** $X$ is sub-gaussian iff $X^2$ is sub-exponential, and $\|X^2\|_{\psi_1}=\|X\|_{\psi_2}^2$.

<a id="pdf-681b6f3d947f-p041-b008"></a>
<!-- pdf-source: page=41; block=8; confidence=0.96 -->
**Proof.** $\|X^2\|_{\psi_1}$ is the infimum of $K>0$ with $\mathbb{E}\exp(X^2/K)\le 2$, while $\|X\|_{\psi_2}$ is the infimum of $L>0$ with $\mathbb{E}\exp(X^2/L^2)\le 2$; these coincide under $K=L^2$. $\square$

<a id="pdf-681b6f3d947f-p041-b009"></a>
<!-- pdf-source: page=41; block=9; confidence=0.97 -->
**Lemma 2.7.7.** If $X,Y$ are sub-gaussian, then $XY$ is sub-exponential and $\|XY\|_{\psi_1}\le\|X\|_{\psi_2}\|Y\|_{\psi_2}$.

<a id="pdf-681b6f3d947f-p042-b001"></a>
<!-- pdf-source: page=42; block=1; confidence=0.95 -->
**Proof.** WLOG $\|X\|_{\psi_2}=\|Y\|_{\psi_2}=1$, so the claim is: $\mathbb{E}\exp(X^2)\le 2$ and $\mathbb{E}\exp(Y^2)\le 2$ (2.22) imply $\mathbb{E}\exp(|XY|)\le 2$. By Young's inequality $ab\le a^2/2+b^2/2$,
$$\mathbb{E}\exp(|XY|)\le\mathbb{E}\exp\!\Big(\tfrac{X^2}{2}+\tfrac{Y^2}{2}\Big)=\mathbb{E}\big[\exp(\tfrac{X^2}{2})\exp(\tfrac{Y^2}{2})\big]\le\tfrac12\mathbb{E}\big[\exp(X^2)+\exp(Y^2)\big]\le\tfrac12(2+2)=2,$$
using Young's inequality again and (2.22). $\square$

<a id="pdf-681b6f3d947f-p042-b002"></a>
<!-- pdf-source: page=42; block=2; confidence=0.95 -->
**Example 2.7.8.** Sub-exponential variables include all sub-gaussians and their squares (e.g. $g^2$ for $g\sim N(\mu,\sigma)$), and the exponential and Poisson distributions. For $X\sim\mathrm{Exp}(\lambda)$, $\lambda>0$ (nonnegative with $\mathbb{P}\{X\ge t\}=e^{-\lambda t}$, $t\ge 0$): $\mathbb{E}X=1/\lambda$, $\mathrm{Var}(X)=1/\lambda^2$, $\|X\|_{\psi_1}=C/\lambda$.

<a id="pdf-681b6f3d947f-p042-b003"></a>
<!-- pdf-source: page=42; block=3; confidence=0.92 -->
**Remark 2.7.9 (MGF near the origin).** The same local MGF bound appears near the origin for sub-gaussian and sub-exponential distributions (property (e) in Propositions 2.5.2 and 2.7.1). For any mean-zero, unit-variance (assume bounded) $X$, the two-term Taylor approximation gives, as $\lambda\to 0$,
$$\mathbb{E}\exp(\lambda X)\approx\mathbb{E}\big[1+\lambda X+\tfrac{\lambda^2 X^2}{2}+o(\lambda^2 X^2)\big]=1+\tfrac{\lambda^2}{2}\approx e^{\lambda^2/2}.$$
For $N(0,1)$ this approximation [text truncated].

<a id="pdf-681b6f3d947f-p043-b001"></a>
<!-- pdf-source: page=43; block=1; confidence=0.95 -->
Recap of MGF bounds: for sub-gaussian distributions the bound (cf. (2.12)) holds for all λ (Proposition 2.5.2), characterizing them; for sub-exponential distributions the bound holds only for small λ (Proposition 2.7.1), characterizing them. No general bound exists for large λ — e.g. for X ∼ Exp(1) the MGF is infinite for λ ≥ 1.

<a id="pdf-681b6f3d947f-p043-b002"></a>
<!-- pdf-source: page=43; block=2; confidence=0.97 -->
**Exercise 2.7.10 (Centering).** Prove the sub-exponential analog of the Centering Lemma 2.6.8: $\|X - \mathbb{E}X\|_{\psi_1} \le C\|X\|_{\psi_1}$.

<a id="pdf-681b6f3d947f-p043-b003"></a>
<!-- pdf-source: page=43; block=3; confidence=0.97 -->
**Section 2.7.1 — Orlicz spaces.** A function $\psi:[0,\infty)\to[0,\infty)$ is an **Orlicz function** if it is convex, increasing, and satisfies $\psi(0)=0$ and $\psi(x)\to\infty$ as $x\to\infty$.

<a id="pdf-681b6f3d947f-p043-b004"></a>
<!-- pdf-source: page=43; block=4; confidence=0.97 -->
**Definition.** For an Orlicz function $\psi$, the **Orlicz norm** of a random variable $X$ is $\|X\|_\psi := \inf\{t>0 : \mathbb{E}\,\psi(|X|/t) \le 1\}$. The **Orlicz space** $L_\psi = L_\psi(\Omega,\Sigma,\mathbb{P})$ consists of all random variables $X$ with finite Orlicz norm: $L_\psi := \{X : \|X\|_\psi < \infty\}$.

<a id="pdf-681b6f3d947f-p043-b005"></a>
<!-- pdf-source: page=43; block=5; confidence=0.96 -->
**Exercise 2.7.11.** Show that $\|X\|_\psi$ is indeed a norm on $L_\psi$. It can further be shown that $L_\psi$ is complete, hence a Banach space.

<a id="pdf-681b6f3d947f-p043-b006"></a>
<!-- pdf-source: page=43; block=6; confidence=0.97 -->
**Example 2.7.12 ($L^p$ space).** For $\psi(x)=x^p$ (an Orlicz function for $p\ge 1$), the resulting Orlicz space $L_\psi$ is the classical space $L^p$.

<a id="pdf-681b6f3d947f-p043-b007"></a>
<!-- pdf-source: page=43; block=7; confidence=0.97 -->
**Example 2.7.13 ($L_{\psi_2}$ space).** For $\psi_2(x):=e^{x^2}-1$ (an Orlicz function), the induced Orlicz norm equals the sub-gaussian norm $\|\cdot\|_{\psi_2}$ defined in (2.13), and the space $L_{\psi_2}$ consists of all sub-gaussian random variables.

<a id="pdf-681b6f3d947f-p044-b001"></a>
<!-- pdf-source: page=44; block=1; confidence=0.96 -->
**Remark 2.7.14.** $L_\infty \subset L_{\psi_2} \subset L^p$ for every $p\in[1,\infty)$. The first inclusion follows from Property ii of Proposition 2.5.2, the second from bound (2.17). Thus the sub-gaussian space $L_{\psi_2}$ is smaller than every $L^p$ but larger than $L_\infty$.

<a id="pdf-681b6f3d947f-p044-b002"></a>
<!-- pdf-source: page=44; block=2; confidence=0.98 -->
**Theorem 2.8.1 (Bernstein's inequality).** Let $X_1,\dots,X_N$ be independent, mean-zero, sub-exponential random variables. Then for every $t\ge 0$,
$$\mathbb{P}\left\{\left|\sum_{i=1}^N X_i\right| \ge t\right\} \le 2\exp\left[-c\,\min\!\left(\frac{t^2}{\sum_{i=1}^N \|X_i\|_{\psi_1}^2},\ \frac{t}{\max_i \|X_i\|_{\psi_1}}\right)\right],$$
where $c>0$ is an absolute constant.

<a id="pdf-681b6f3d947f-p044-b003"></a>
<!-- pdf-source: page=44; block=3; confidence=0.96 -->
**Proof.** For $S=\sum_{i=1}^N X_i$, proceed as in Theorems 2.2.2 and 2.3.1: multiply $S\ge t$ by $\lambda$, exponentiate, apply Markov's inequality and independence, giving (2.23): $\mathbb{P}\{S\ge t\} \le e^{-\lambda t}\prod_{i=1}^N \mathbb{E}\exp(\lambda X_i)$. By property e of Proposition 2.7.1, if $|\lambda| \le \frac{c}{\max_i \|X_i\|_{\psi_1}}$ then $\mathbb{E}\exp(\lambda X_i) \le \exp(C\lambda^2\|X_i\|_{\psi_1}^2)$ (2.24). Substituting gives $\mathbb{P}\{S\ge t\} \le \exp(-\lambda t + C\lambda^2\sigma^2)$ with $\sigma^2=\sum_{i=1}^N \|X_i\|_{\psi_1}^2$. Minimizing over $\lambda$ subject to (2.24), the optimal choice is $\lambda=\min\!\left(\frac{t}{2C\sigma^2},\ \frac{c}{\max_i\|X_i\|_{\psi_1}}\right)$, yielding $\mathbb{P}\{S\ge t\} \le \exp\left[-\min\!\left(\frac{t^2}{4C\sigma^2},\ \frac{ct}{2\max_i\|X_i\|_{\psi_1}}\right)\right]$. [continued on next page]

<a id="pdf-681b6f3d947f-p045-b001"></a>
<!-- pdf-source: page=45; block=1; confidence=0.96 -->
**Proof (concluded).** Repeating the argument for $-X_i$ gives the same bound for $\mathbb{P}\{-S\ge t\}$; combining the two tail bounds completes the proof. $\square$

<a id="pdf-681b6f3d947f-p045-b002"></a>
<!-- pdf-source: page=45; block=2; confidence=0.98 -->
**Theorem 2.8.2 (Bernstein's inequality).** Let $X_1,\dots,X_N$ be independent, mean-zero, sub-exponential random variables and $a=(a_1,\dots,a_N)\in\mathbb{R}^N$. Then for every $t\ge 0$,
$$\mathbb{P}\left\{\left|\sum_{i=1}^N a_i X_i\right| \ge t\right\} \le 2\exp\left[-c\,\min\!\left(\frac{t^2}{K^2\|a\|_2^2},\ \frac{t}{K\|a\|_\infty}\right)\right],$$
where $K=\max_i\|X_i\|_{\psi_1}$. (Obtained by applying Theorem 2.8.1 to $a_iX_i$.)

<a id="pdf-681b6f3d947f-p045-b003"></a>
<!-- pdf-source: page=45; block=3; confidence=0.97 -->
**Corollary 2.8.3 (Bernstein's inequality).** With $a_i=1/N$: for independent, mean-zero, sub-exponential $X_1,\dots,X_N$ and every $t\ge 0$,
$$\mathbb{P}\left\{\left|\frac{1}{N}\sum_{i=1}^N X_i\right| \ge t\right\} \le 2\exp\left[-c\,\min\!\left(\frac{t^2}{K^2},\ \frac{t}{K}\right)N\right],$$
where $K=\max_i\|X_i\|_{\psi_1}$. This is a quantitative form of the law of large numbers for $\frac1N\sum X_i$.

<a id="pdf-681b6f3d947f-p045-b004"></a>
<!-- pdf-source: page=45; block=4; confidence=0.94 -->
Comparison with Hoeffding's inequality (Theorem 2.6.2): Bernstein's bound has two tails, behaving like a mixture of sub-gaussian and sub-exponential distributions. The sub-exponential tail is produced by the single term $X_i$ with maximal norm, contributing a tail of magnitude $\exp(-ct/\|X_i\|_{\psi_1})$ (analogous to the two-regime behavior in Chernoff's inequality, Remark 2.3.7). Normalizing as in the CLT and applying Theorem 2.8.2 gives
$$\mathbb{P}\left\{\left|\frac{1}{\sqrt N}\sum_{i=1}^N X_i\right| \ge t\right\} \le \begin{cases} 2\exp(-ct^2), & t\le C\sqrt N,\\ 2\exp(-t\sqrt N), & t\ge C\sqrt N,\end{cases}$$
(with constants absorbing the dependence on $K$). In the small-deviation regime $t\le C\sqrt N$ the tail is sub-gaussian, as for a normal distribution of constant variance.

<a id="pdf-681b6f3d947f-p046-b001"></a>
<!-- pdf-source: page=46; block=1; confidence=0.82 -->
The sub-gaussian domain widens as $N$ grows (stronger CLT); for large deviations $t \gtrsim C\sqrt{N}$ the sum has a heavier sub-exponential tail, attributable to a single term $X_i$ (illustrated in Figure 2.3).

<a id="pdf-681b6f3d947f-p046-b002"></a>
<!-- pdf-source: page=46; block=2; confidence=0.90 -->
Figure 2.3: Bernstein's inequality for a sum of sub-exponential variables yields a mixture of two tails — sub-gaussian for small deviations, sub-exponential for large deviations.

<a id="pdf-681b6f3d947f-p046-b003"></a>
<!-- pdf-source: page=46; block=3; confidence=0.90 -->
A strengthening of Bernstein's inequality sensitive to the variance of the sum holds under the stronger assumption that the $X_i$ are bounded.

<a id="pdf-681b6f3d947f-p046-b004"></a>
<!-- pdf-source: page=46; block=4; confidence=0.95 -->
**Theorem 2.8.4 (Bernstein's inequality for bounded distributions).** Let $X_1,\dots,X_N$ be independent, mean-zero random variables with $|X_i| \le K$ for all $i$. Then for every $t \ge 0$,
$$\mathbb{P}\Big\{\Big|\sum_{i=1}^N X_i\Big| \ge t\Big\} \le 2\exp\!\left(-\frac{t^2/2}{\sigma^2 + Kt/3}\right),$$
where $\sigma^2 = \sum_{i=1}^N \mathbb{E}\,X_i^2$ is the variance of the sum.

<a id="pdf-681b6f3d947f-p046-b005"></a>
<!-- pdf-source: page=46; block=5; confidence=0.93 -->
**Exercise 2.8.5 (A bound on MGF).** For a mean-zero $X$ with $|X| \le K$, prove $\mathbb{E}\exp(\lambda X) \le \exp(g(\lambda)\,\mathbb{E}\,X^2)$ where $g(\lambda) = \dfrac{\lambda^2/2}{1 - |\lambda|K/3}$, provided $|\lambda| < 3/K$. Hint: use the numeric inequality $e^z \le 1 + z + \dfrac{z^2/2}{1 - |z|/3}$ valid for $|z| < 3$, apply with $z = \lambda X$, and take expectations.

<a id="pdf-681b6f3d947f-p046-b006"></a>
<!-- pdf-source: page=46; block=6; confidence=0.95 -->
**Exercise 2.8.6.** Deduce Theorem 2.8.4 from the MGF bound in Exercise 2.8.5. Hint: follow the proof of Theorem 2.8.1.

<a id="pdf-681b6f3d947f-p047-b001"></a>
<!-- pdf-source: page=47; block=1; confidence=0.97 -->
# 2.9 Notes

<a id="pdf-681b6f3d947f-p047-b002"></a>
<!-- pdf-source: page=47; block=2; confidence=0.90 -->
Concentration inequalities are treated further in Chapter 5. References given for versions of Hoeffding's, Chernoff's, and Bernstein's inequalities. Proposition 2.1.2 (normal-tail bounds) is from [72, Thm 1.4]; the Berry–Esseen CLT (Theorem 2.1.3) with an extra factor 3 appears in [72, Sec. 2.4.d], and the best known factor is $\approx 0.47$ [120].

<a id="pdf-681b6f3d947f-p047-b003"></a>
<!-- pdf-source: page=47; block=3; confidence=0.90 -->
Two omitted inequalities are noted. First, the bounded differences (McDiarmid's) inequality, which applies to general functions of independent random variables and generalizes Hoeffding's inequality (Theorem 2.2.6).

<a id="pdf-681b6f3d947f-p047-b004"></a>
<!-- pdf-source: page=47; block=4; confidence=0.94 -->
**Theorem 2.9.1 (Bounded differences inequality).** Let $X_1,\dots,X_N$ be independent random variables and $f:\mathbb{R}^n \to \mathbb{R}$ measurable such that $f(x)$ changes by at most $c_i > 0$ under an arbitrary change of a single coordinate of $x$. Then for any $t > 0$,
$$\mathbb{P}\{f(X) - \mathbb{E}f(X) \ge t\} \le \exp\!\left(-\frac{2t^2}{\sum_{i=1}^N c_i^2}\right),$$
where $X = (X_1,\dots,X_n)$. (Remains valid for $X_i$ in an abstract set $\mathcal{X}$ with $f:\mathcal{X}\to\mathbb{R}$.)

<a id="pdf-681b6f3d947f-p047-b005"></a>
<!-- pdf-source: page=47; block=5; confidence=0.90 -->
Second, Bennett's inequality, a generalization of Chernoff's inequality.

<a id="pdf-681b6f3d947f-p047-b006"></a>
<!-- pdf-source: page=47; block=6; confidence=0.94 -->
**Theorem 2.9.2 (Bennett's inequality).** Let $X_1,\dots,X_N$ be independent with $|X_i - \mathbb{E}X_i| \le K$ almost surely for every $i$. Then for any $t > 0$,
$$\mathbb{P}\Big\{\sum_{i=1}^N (X_i - \mathbb{E}X_i) \ge t\Big\} \le \exp\!\left(-\frac{\sigma^2}{K^2}\,h\!\Big(\frac{Kt}{\sigma^2}\Big)\right),$$
where $\sigma^2 = \sum_{i=1}^N \mathrm{Var}(X_i)$ and $h(u) = (1+u)\log(1+u) - u$.

<a id="pdf-681b6f3d947f-p047-b007"></a>
<!-- pdf-source: page=47; block=7; confidence=0.85 -->
Small-deviation regime $u := Kt/\sigma^2 \ll 1$: $h(u) \approx u^2$, giving an approximately Gaussian tail $\approx \exp(-t^2/\sigma^2)$. Large-deviation regime: $h(u) \ge \tfrac{1}{2}u\log u$, giving a Poisson-like tail $(\sigma^2/Kt)^{t/2K}$.

<a id="pdf-681b6f3d947f-p047-b008"></a>
<!-- pdf-source: page=47; block=8; confidence=0.90 -->
Footnote 10: Theorem 2.9.1 holds for $X_i$ in an abstract set $\mathcal{X}$ with $f:\mathcal{X}\to\mathbb{R}$. Footnote 11: the bounded-change condition means for any index $i$ and any $x_1,\dots,x_n,x_i'$, $|f(x_1,\dots,x_{i-1},x_i,x_{i+1},\dots,x_n) - f(x_1,\dots,x_{i-1},x_i',x_{i+1},\dots,x_n)| \le c_i$.

<a id="pdf-681b6f3d947f-p048-b001"></a>
<!-- pdf-source: page=48; block=1; confidence=0.92 -->
Both the bounded differences and Bennett's inequalities are provable by the same MGF-bounding method as Hoeffding's (Theorem 2.2.2) and Chernoff's (Theorem 2.3.1) inequalities, a method pioneered by Sergei Bernstein in the 1920s–30s. The Chernoff presentation of Section 2.3 mostly follows [152, Chapter 4].

<a id="pdf-681b6f3d947f-p048-b002"></a>
<!-- pdf-source: page=48; block=2; confidence=0.93 -->
Section 2.4 introduces random graphs; [26, 107] give comprehensive introductions to random graph theory.

<a id="pdf-681b6f3d947f-p048-b003"></a>
<!-- pdf-source: page=48; block=3; confidence=0.93 -->
Sections 2.5–2.8 mostly follow [222]; see [78, Chapter 7] for more elaborate results. For sharp versions of Khintchine's inequalities (Exercises 2.6.5–2.6.7) and related results, see [195, 95, 118, 155].

<a id="pdf-681b6f3d947f-p049-b001"></a>
<!-- pdf-source: page=49; block=1; confidence=0.98 -->
# Chapter 3. Random vectors in high dimensions

<a id="pdf-681b6f3d947f-p049-b002"></a>
<!-- pdf-source: page=49; block=2; confidence=0.95 -->
Studies distributions of random vectors $X=(X_1,\dots,X_n)\in\mathbb{R}^n$ with $n$ large (e.g. gene-expression data, $n\sim10^4$). Motivation: high dimensions contain exponentially more room (a side-2 cube has $2^n$ times the volume of a unit cube), the "curse of dimensionality." Chapter roadmap: Section 3.1 shows the Euclidean norm $\lVert X\rVert_2$ of a vector with independent coordinates concentrates about its mean; Section 3.2 covers high-dimensional examples (multivariate normal, spherical, Bernoulli, frames) and PCA; Section 3.5 proves Grothendieck's inequality with an application to semidefinite optimization.

<a id="pdf-681b6f3d947f-p050-b001"></a>
<!-- pdf-source: page=50; block=1; confidence=0.95 -->
Roadmap continued: semidefinite relaxations of hard problems analyzed via Grothendieck's inequality; Section 3.6 gives the Goemans–Williamson randomized approximation algorithm for maximum cut; Section 3.7 gives an alternative proof of Grothendieck's inequality (with nearly the best known constant) via the kernel trick.

<a id="pdf-681b6f3d947f-p050-b002"></a>
<!-- pdf-source: page=50; block=2; confidence=0.98 -->
## 3.1 Concentration of the norm

<a id="pdf-681b6f3d947f-p050-b003"></a>
<!-- pdf-source: page=50; block=3; confidence=0.96 -->
For independent coordinates $X_i$ with zero mean and unit variance, $\mathbb{E}\lVert X\rVert_2^2=\sum_{i=1}^n\mathbb{E}X_i^2=n$, so one expects $\lVert X\rVert_2\approx\sqrt{n}$; the theorem shows $\lVert X\rVert_2$ is close to $\sqrt{n}$ with high probability.

<a id="pdf-681b6f3d947f-p050-b004"></a>
<!-- pdf-source: page=50; block=4; confidence=0.97 -->
**Theorem 3.1.1 (Concentration of the norm).** Let $X=(X_1,\dots,X_n)\in\mathbb{R}^n$ have independent, sub-gaussian coordinates $X_i$ with $\mathbb{E}X_i^2=1$. Then
$$\big\lVert\,\lVert X\rVert_2-\sqrt{n}\,\big\rVert_{\psi_2}\le CK^2,$$
where $K=\max_i\lVert X_i\rVert_{\psi_2}$ and $C$ is an absolute constant.

<a id="pdf-681b6f3d947f-p050-b005"></a>
<!-- pdf-source: page=50; block=5; confidence=0.95 -->
**Proof.** Assume WLOG $K\ge1$. Apply Bernstein's inequality to the normalized mean-zero sum $\frac{1}{n}\lVert X\rVert_2^2-1=\frac{1}{n}\sum_{i=1}^n(X_i^2-1)$. Since $X_i$ is sub-gaussian, $X_i^2-1$ is sub-exponential with $\lVert X_i^2-1\rVert_{\psi_1}\le C\lVert X_i^2\rVert_{\psi_1}$ (by centering, Exercise 2.7.10) $=C\lVert X_i\rVert_{\psi_2}^2$ (by Lemma 2.7.6) $\le CK^2$.

<a id="pdf-681b6f3d947f-p050-b006"></a>
<!-- pdf-source: page=50; block=6; confidence=0.90 -->
Footnote: positive absolute constants are henceforth denoted $C,c,C_1,c_1$ without explicit mention.

<a id="pdf-681b6f3d947f-p051-b001"></a>
<!-- pdf-source: page=51; block=1; confidence=0.95 -->
**Proof (continued).** By Bernstein's inequality (Corollary 2.8.3), for all $u\ge0$:
$$\mathbb{P}\Big\{\big|\tfrac{1}{n}\lVert X\rVert_2^2-1\big|\ge u\Big\}\le 2\exp\!\Big(-\tfrac{cn}{K^4}\min(u^2,u)\Big)\tag{3.1}$$
(using $K^4\ge K^2$ since $K\ge1$). Use the elementary fact for $z\ge0$:
$$|z-1|\ge\delta\ \Rightarrow\ |z^2-1|\ge\max(\delta,\delta^2).\tag{3.2}$$
Then for $\delta\ge0$:
$$\mathbb{P}\Big\{\big|\tfrac{1}{\sqrt{n}}\lVert X\rVert_2-1\big|\ge\delta\Big\}\le\mathbb{P}\Big\{\big|\tfrac{1}{n}\lVert X\rVert_2^2-1\big|\ge\max(\delta,\delta^2)\Big\}\le 2\exp\!\Big(-\tfrac{cn}{K^4}\delta^2\Big),$$
by (3.2) and (3.1) with $u=\max(\delta,\delta^2)$. Substituting $t=\delta\sqrt{n}$ gives the sub-gaussian tail
$$\mathbb{P}\big\{\,|\lVert X\rVert_2-\sqrt{n}|\ge t\,\big\}\le 2\exp\!\Big(-\tfrac{ct^2}{K^4}\Big)\quad\forall t\ge0,\tag{3.3}$$
which (per Section 2.5.2) is equivalent to the theorem's conclusion. $\square$

<a id="pdf-681b6f3d947f-p051-b002"></a>
<!-- pdf-source: page=51; block=2; confidence=0.93 -->
**Remark 3.1.2 (Deviation).** With high probability $X$ lies within constant distance of the sphere of radius $\sqrt{n}$. Intuition: $S_n:=\lVert X\rVert_2^2$ has mean $n$ and standard deviation $O(\sqrt{n})$, so $S_n=n\pm O(\sqrt{n})$ and $\lVert X\rVert_2=\sqrt{n\pm O(\sqrt{n})}=\sqrt{n}\pm O(1)$.

<a id="pdf-681b6f3d947f-p051-b003"></a>
<!-- pdf-source: page=51; block=3; confidence=0.95 -->
**Remark 3.1.3 (Anisotropic distributions).** A generalization of Theorem 3.1.1 to anisotropic random vectors is proved later as Theorem 6.3.2.

<a id="pdf-681b6f3d947f-p051-b004"></a>
<!-- pdf-source: page=51; block=4; confidence=0.95 -->
**Exercise 3.1.4 (Expectation of the norm).** (a) Deduce from Theorem 3.1.1 that $\sqrt{n}-CK^2\le\mathbb{E}\lVert X\rVert_2\le\sqrt{n}+CK^2$. (b) Can $CK^2$ be replaced by $o(1)$ (vanishing as $n\to\infty$)?

<a id="pdf-681b6f3d947f-p052-b001"></a>
<!-- pdf-source: page=52; block=1; confidence=0.95 -->
Figure 3.2: concentration of the norm of a random vector $X$ in $\mathbb{R}^n$; while $\|X\|_2^2$ deviates by $O(\sqrt{n})$ around $n$, $\|X\|_2$ deviates by $O(1)$ around $\sqrt{n}$.

<a id="pdf-681b6f3d947f-p052-b002"></a>
<!-- pdf-source: page=52; block=2; confidence=0.97 -->
**Exercise 3.1.5 (Variance of the norm).** Deduce from Theorem 3.1.1 that $\mathrm{Var}(\|X\|_2) \le CK^4$. Hint: use Exercise 3.1.4.

<a id="pdf-681b6f3d947f-p052-b003"></a>
<!-- pdf-source: page=52; block=3; confidence=0.95 -->
Remark: the previous result holds not only for sub-gaussian distributions but for all distributions with bounded fourth moment.

<a id="pdf-681b6f3d947f-p052-b004"></a>
<!-- pdf-source: page=52; block=4; confidence=0.90 -->
**Exercise 3.1.6 (Variance of the norm under finite moment assumptions).** Let $X=(X_1,\dots,X_n)\in\mathbb{R}^n$ have independent coordinates $X_i$ with $\mathbb{E}X_i^2=1$ and $\mathbb{E}X_i^4\le K^4$. Show $\mathrm{Var}(\|X\|_2)\le CK^4$. Hint: check $\mathbb{E}(\|X\|_2^2-n)^2\le K^4 n$ by expansion, giving $\mathbb{E}(\|X\|_2-\sqrt{n})^2\le K^4$; then replace $\sqrt{n}$ by $\mathbb{E}\|X\|_2$ as in Exercise 3.1.4.

<a id="pdf-681b6f3d947f-p052-b005"></a>
<!-- pdf-source: page=52; block=5; confidence=0.95 -->
**Exercise 3.1.7 (Small ball probabilities).** Let $X=(X_1,\dots,X_n)\in\mathbb{R}^n$ have independent coordinates $X_i$ with continuous distributions whose densities are uniformly bounded by $1$. Show that for any $\varepsilon>0$,
$$\mathbb{P}\{\|X\|_2\le \varepsilon\sqrt{n}\}\le (C\varepsilon)^n.$$
Hint: this does not follow from Exercise 2.2.10, but can be proved by a similar argument.

<a id="pdf-681b6f3d947f-p052-b006"></a>
<!-- pdf-source: page=52; block=6; confidence=0.95 -->
**3.2 Covariance matrices and principal component analysis.** Transition from random variables with independent coordinates toward more general distributions; recalls basic notions of high-dimensional distributions.

<a id="pdf-681b6f3d947f-p053-b001"></a>
<!-- pdf-source: page=53; block=1; confidence=0.96 -->
The covariance matrix of a random vector $X\in\mathbb{R}^n$ generalizes variance:
$$\mathrm{cov}(X)=\mathbb{E}(X-\mu)(X-\mu)^T=\mathbb{E}XX^T-\mu\mu^T,\quad \mu=\mathbb{E}X,$$
an $n\times n$ symmetric positive semidefinite matrix. Compare the scalar case $\mathrm{Var}(Z)=\mathbb{E}(Z-\mu)^2=\mathbb{E}Z^2-\mu^2$. Entrywise, $\mathrm{cov}(X)_{ij}=\mathbb{E}(X_i-\mathbb{E}X_i)(X_j-\mathbb{E}X_j)$.

<a id="pdf-681b6f3d947f-p053-b002"></a>
<!-- pdf-source: page=53; block=2; confidence=0.96 -->
The second moment matrix is $\Sigma=\Sigma(X)=\mathbb{E}XX^T$, generalizing $\mathbb{E}Z^2$. By translation ($X\to X-\mu$) one may assume zero mean, so that $\mathrm{cov}(X)=\Sigma(X)$; hence one focuses on $\Sigma$.

<a id="pdf-681b6f3d947f-p053-b003"></a>
<!-- pdf-source: page=53; block=3; confidence=0.96 -->
$\Sigma$ is $n\times n$ symmetric positive semidefinite; by the spectral theorem its eigenvalues $s_i$ are real and non-negative, and
$$\Sigma=\sum_{i=1}^n s_i u_i u_i^T,$$
with eigenvectors $u_i\in\mathbb{R}^n$, terms arranged so the $s_i$ are decreasing.

<a id="pdf-681b6f3d947f-p053-b004"></a>
<!-- pdf-source: page=53; block=4; confidence=0.93 -->
**3.2.1 Principal component analysis.** The spectral decomposition of $\Sigma$ is central when $X$ represents data; the eigenvector $u_1$ of the largest eigenvalue $s_1$ gives the first principal direction, the direction of greatest spread.

<a id="pdf-681b6f3d947f-p054-b001"></a>
<!-- pdf-source: page=54; block=1; confidence=0.93 -->
$u_1$ is the direction in which the distribution is most extended (most variability); $u_2$ (next eigenvalue $s_2$) gives the next principal direction explaining remaining variation, and so on (Figure 3.3).

<a id="pdf-681b6f3d947f-p054-b002"></a>
<!-- pdf-source: page=54; block=2; confidence=0.92 -->
Figure 3.3: illustration of PCA with 200 sample points from a distribution in $\mathbb{R}^2$; covariance matrix $\Sigma$ has eigenvalues $s_i$ and eigenvectors $u_i$.

<a id="pdf-681b6f3d947f-p054-b003"></a>
<!-- pdf-source: page=54; block=3; confidence=0.92 -->
Often only a few eigenvalues $s_i$ are large (informative) and the rest are small (noise), so data in $\mathbb{R}^n$ is essentially low-dimensional, clustering near the subspace $E$ spanned by the first few principal components.

<a id="pdf-681b6f3d947f-p054-b004"></a>
<!-- pdf-source: page=54; block=4; confidence=0.92 -->
PCA computes the first few principal components and projects the data onto their span $E$, reducing dimension; for two- or three-dimensional $E$ this enables visualization.

<a id="pdf-681b6f3d947f-p054-b005"></a>
<!-- pdf-source: page=54; block=5; confidence=0.93 -->
**3.2.2 Isotropy.** Isotropy generalizes the unit-variance assumption to higher dimensions.

<a id="pdf-681b6f3d947f-p054-b006"></a>
<!-- pdf-source: page=54; block=6; confidence=0.97 -->
**Definition 3.2.1 (Isotropic random vectors).** A random vector $X$ in $\mathbb{R}^n$ is isotropic if
$$\Sigma(X)=\mathbb{E}XX^T=I_n,$$
where $I_n$ is the identity matrix in $\mathbb{R}^n$.

<a id="pdf-681b6f3d947f-p054-b007"></a>
<!-- pdf-source: page=54; block=7; confidence=0.95 -->
Any random variable $X$ with positive variance reduces by translation and dilation to the standard score $Z=\dfrac{X-\mu}{\sqrt{\mathrm{Var}(X)}}$, having zero mean and unit variance.

<a id="pdf-681b6f3d947f-p055-b001"></a>
<!-- pdf-source: page=55; block=1; confidence=0.97 -->
**Exercise 3.2.2 (Reduction to isotropy).** (a) For a mean-zero isotropic random vector $Z$ in $\mathbb{R}^n$, fixed $\mu \in \mathbb{R}^n$, and fixed symmetric PSD matrix $\Sigma$, verify that $X := \mu + \Sigma^{1/2} Z$ has mean $\mu$ and covariance $\operatorname{cov}(X) = \Sigma$. (b) For a random vector $X$ with mean $\mu$ and invertible covariance $\Sigma = \operatorname{cov}(X)$, verify that $Z := \Sigma^{-1/2}(X - \mu)$ is mean-zero and isotropic. This lets one assume WLOG that random vectors are zero-mean and isotropic.

<a id="pdf-681b6f3d947f-p055-b002"></a>
<!-- pdf-source: page=55; block=2; confidence=0.98 -->
### 3.2.3 Properties of isotropic distributions

<a id="pdf-681b6f3d947f-p055-b003"></a>
<!-- pdf-source: page=55; block=3; confidence=0.98 -->
**Lemma 3.2.3 (Characterization of isotropy).** A random vector $X$ in $\mathbb{R}^n$ is isotropic if and only if $\mathbb{E}\langle X, x\rangle^2 = \|x\|_2^2$ for all $x \in \mathbb{R}^n$.

<a id="pdf-681b6f3d947f-p055-b004"></a>
<!-- pdf-source: page=55; block=4; confidence=0.97 -->
**Proof.** Symmetric $n\times n$ matrices $A, B$ are equal iff $x^T A x = x^T B x$ for all $x$. Hence $X$ is isotropic iff $x^T(\mathbb{E} X X^T) x = x^T I_n x$ for all $x$. The left side equals $\mathbb{E}\langle X, x\rangle^2$ and the right side equals $\|x\|_2^2$. $\square$

<a id="pdf-681b6f3d947f-p055-b005"></a>
<!-- pdf-source: page=55; block=5; confidence=0.93 -->
For unit $x$, $\langle X, x\rangle$ is the one-dimensional marginal of $X$ onto direction $x$; a mean-zero $X$ is isotropic iff all such marginals have unit variance, i.e. the distribution is spread evenly in all directions.

<a id="pdf-681b6f3d947f-p055-b006"></a>
<!-- pdf-source: page=55; block=6; confidence=0.98 -->
**Lemma 3.2.4.** If $X$ is isotropic in $\mathbb{R}^n$, then $\mathbb{E}\|X\|_2^2 = n$. Moreover, if $X, Y$ are independent isotropic random vectors in $\mathbb{R}^n$, then $\mathbb{E}\langle X, Y\rangle^2 = n$.

<a id="pdf-681b6f3d947f-p056-b001"></a>
<!-- pdf-source: page=56; block=1; confidence=0.97 -->
**Proof.** First part: $\mathbb{E}\|X\|_2^2 = \mathbb{E}\, X^T X = \mathbb{E}\operatorname{tr}(X^T X) = \mathbb{E}\operatorname{tr}(X X^T) = \operatorname{tr}(\mathbb{E} X X^T) = \operatorname{tr}(I_n) = n$ (using the cyclic property of trace, linearity, and isotropy). Second part: by the law of total expectation, $\mathbb{E}\langle X, Y\rangle^2 = \mathbb{E}_Y \mathbb{E}_X[\langle X, Y\rangle^2 \mid Y]$. Applying Lemma 3.2.3 with $x = Y$, the inner expectation equals $\|Y\|_2^2$, so $\mathbb{E}\langle X, Y\rangle^2 = \mathbb{E}_Y \|Y\|_2^2 = n$ by the first part. $\square$

<a id="pdf-681b6f3d947f-p056-b002"></a>
<!-- pdf-source: page=56; block=2; confidence=0.90 -->
**Remark 3.2.5 (Almost orthogonality of independent vectors).** Normalizing $\bar{X} = X/\|X\|_2$, $\bar{Y} = Y/\|Y\|_2$, Lemma 3.2.4 suggests $\|X\|_2 \asymp \sqrt{n}$, $\|Y\|_2 \asymp \sqrt{n}$, and $\langle X, Y\rangle \asymp \sqrt{n}$ with high probability, giving $|\langle \bar{X}, \bar{Y}\rangle| \asymp 1/\sqrt{n}$. Thus independent isotropic random vectors are nearly orthogonal in high dimensions. (Footnote: not fully rigorous since the lemma concerns expectations; Theorem 3.1.1 on concentration of the norm makes it rigorous.)

<a id="pdf-681b6f3d947f-p056-b003"></a>
<!-- pdf-source: page=56; block=3; confidence=0.92 -->
Figure 3.4: independent isotropic random vectors tend to be almost orthogonal in high dimensions but not in low dimensions; on the plane the average angle is $\pi/4$, while in high dimensions it is close to $\pi/2$.

<a id="pdf-681b6f3d947f-p057-b001"></a>
<!-- pdf-source: page=57; block=1; confidence=0.90 -->
In low dimensions this fails: two random independent uniform directions on the plane have mean angle $\pi/4$. In higher dimensions there is more room, so random directions tend to be almost orthogonal.

<a id="pdf-681b6f3d947f-p057-b002"></a>
<!-- pdf-source: page=57; block=2; confidence=0.97 -->
**Exercise 3.2.6 (Distance between independent isotropic vectors).** For independent, mean-zero, isotropic random vectors $X, Y$ in $\mathbb{R}^n$, verify that $\mathbb{E}\|X - Y\|_2^2 = 2n$.

<a id="pdf-681b6f3d947f-p057-b003"></a>
<!-- pdf-source: page=57; block=3; confidence=0.97 -->
## 3.3 Examples of high-dimensional distributions

Several basic examples of isotropic high-dimensional distributions.

<a id="pdf-681b6f3d947f-p057-b004"></a>
<!-- pdf-source: page=57; block=4; confidence=0.95 -->
### 3.3.1 Spherical and Bernoulli distributions

The coordinates of an isotropic vector are uncorrelated but not necessarily independent. **Spherical distribution:** $X$ is uniformly distributed on the Euclidean sphere in $\mathbb{R}^n$ centered at the origin with radius $\sqrt{n}$, i.e. $X \sim \mathrm{Unif}(\sqrt{n}\, S^{n-1})$. (Footnote: uniform means $\mathbb{P}\{X \in E\}$ equals the ratio of $(n-1)$-dimensional areas of $E$ and $S^{n-1}$ for Borel $E \subset S^{n-1}$.)

<a id="pdf-681b6f3d947f-p057-b005"></a>
<!-- pdf-source: page=57; block=5; confidence=0.97 -->
**Exercise 3.3.1.** Show that the spherically distributed $X$ is isotropic, and argue that its coordinates are not independent.

<a id="pdf-681b6f3d947f-p057-b006"></a>
<!-- pdf-source: page=57; block=6; confidence=0.96 -->
**Symmetric Bernoulli distribution:** $X = (X_1, \dots, X_n)$ with independent symmetric Bernoulli coordinates, equivalently $X \sim \mathrm{Unif}(\{-1, 1\}^n)$; this distribution is isotropic. More generally, any $X = (X_1, \dots, X_n)$ with independent, zero-mean, unit-variance coordinates is isotropic in $\mathbb{R}^n$.

<a id="pdf-681b6f3d947f-p058-b001"></a>
<!-- pdf-source: page=58; block=1; confidence=1.00 -->
## 3.3.2 Multivariate normal

<a id="pdf-681b6f3d947f-p058-b002"></a>
<!-- pdf-source: page=58; block=2; confidence=0.97 -->
**Definition (standard normal).** A random vector $g=(g_1,\dots,g_n)$ has the standard normal distribution $g\sim N(0,I_n)$ in $\mathbb{R}^n$ if the coordinates $g_i$ are independent $N(0,1)$. Its density is the product of $n$ standard normal densities:
$$f(x)=\prod_{i=1}^n \frac{1}{\sqrt{2\pi}}e^{-x_i^2/2}=\frac{1}{(2\pi)^{n/2}}e^{-\|x\|_2^2/2},\quad x\in\mathbb{R}^n. \tag{3.4}$$
The standard normal distribution is isotropic.

<a id="pdf-681b6f3d947f-p058-b003"></a>
<!-- pdf-source: page=58; block=3; confidence=0.96 -->
The density (3.4) is rotation invariant, since $f(x)$ depends only on $\|x\|$, not the direction of $x$.

<a id="pdf-681b6f3d947f-p058-b004"></a>
<!-- pdf-source: page=58; block=4; confidence=0.99 -->
**Proposition 3.3.2 (Rotation invariance).** For $g\sim N(0,I_n)$ and a fixed orthogonal matrix $U$, one has $Ug\sim N(0,I_n)$.

<a id="pdf-681b6f3d947f-p058-b005"></a>
<!-- pdf-source: page=58; block=5; confidence=0.97 -->
**Exercise 3.3.3 (Rotation invariance).** Deduce from rotation invariance:
(a) For $g\sim N(0,I_n)$ and fixed $u\in\mathbb{R}^n$: $\langle g,u\rangle\sim N(0,\|u\|_2^2)$.
(b) For independent $X_i\sim N(0,\sigma_i^2)$: $\sum_{i=1}^n X_i\sim N(0,\sigma^2)$ with $\sigma^2=\sum_{i=1}^n\sigma_i^2$.
(c) For an $m\times n$ Gaussian matrix $G$ (independent $N(0,1)$ entries) and a fixed unit vector $u\in\mathbb{R}^n$: $Gu\sim N(0,I_m)$.

<a id="pdf-681b6f3d947f-p058-b006"></a>
<!-- pdf-source: page=58; block=6; confidence=0.96 -->
**Definition (general normal).** Given $\mu\in\mathbb{R}^n$ and an invertible positive semidefinite $n\times n$ matrix $\Sigma$, the vector $X:=\mu+\Sigma^{1/2}Z$ (with $Z\sim N(0,I_n)$) has mean $\mu$ and covariance $\Sigma(X)=\Sigma$; it is denoted $X\sim N(\mu,\Sigma)$. Equivalently, $X\sim N(\mu,\Sigma)$ iff $Z:=\Sigma^{-1/2}(X-\mu)\sim N(0,I_n)$.

<a id="pdf-681b6f3d947f-p059-b001"></a>
<!-- pdf-source: page=59; block=1; confidence=0.97 -->
**Density of $N(\mu,\Sigma)$.** By change of variables,
$$f_X(x)=\frac{1}{(2\pi)^{n/2}\det(\Sigma)^{1/2}}e^{-(x-\mu)^T\Sigma^{-1}(x-\mu)/2},\quad x\in\mathbb{R}^n. \tag{3.5}$$

<a id="pdf-681b6f3d947f-p059-b002"></a>
<!-- pdf-source: page=59; block=2; confidence=0.95 -->
For $X\sim N(\mu,\Sigma)$, the coordinates are independent iff they are uncorrelated (in which case $\Sigma=I_n$).

<a id="pdf-681b6f3d947f-p059-b003"></a>
<!-- pdf-source: page=59; block=3; confidence=0.95 -->
**Exercise 3.3.4 (Characterization).** Show $X\in\mathbb{R}^n$ has a multivariate normal distribution iff every one-dimensional marginal $\langle X,\theta\rangle$, $\theta\in\mathbb{R}^n$, is univariate normal. Hint: use Cramér–Wold's theorem (one-dimensional marginal distributions determine the joint distribution uniquely).

<a id="pdf-681b6f3d947f-p059-b004"></a>
<!-- pdf-source: page=59; block=4; confidence=0.90 -->
Figure 3.5: densities of the isotropic $N(0,I_2)$ and a non-isotropic $N(0,\Sigma)$.

<a id="pdf-681b6f3d947f-p059-b005"></a>
<!-- pdf-source: page=59; block=5; confidence=0.96 -->
**Exercise 3.3.5.** Let $X\sim N(0,I_n)$.
(a) For fixed $u,v\in\mathbb{R}^n$: $\mathbb{E}\,\langle X,u\rangle\langle X,v\rangle=\langle u,v\rangle$. (3.6)
(b) With $X_u:=\langle X,u\rangle\sim N(0,\|u\|_2^2)$, check $\|X_u-X_v\|_{L^2}=\|u-v\|_2$ for fixed $u,v$, where $\|\cdot\|_{L^2}$ is the norm in the Hilbert space $L^2$ of random variables from (1.1).

<a id="pdf-681b6f3d947f-p059-b006"></a>
<!-- pdf-source: page=59; block=6; confidence=0.96 -->
**Exercise 3.3.6.** For an $m\times n$ Gaussian matrix $G$ (independent $N(0,1)$ entries) and unit orthogonal $u,v\in\mathbb{R}^n$, prove $Gu$ and $Gv$ are independent $N(0,I_m)$ vectors. Hint: reduce to $u,v$ collinear with canonical basis vectors.

<a id="pdf-681b6f3d947f-p060-b001"></a>
<!-- pdf-source: page=60; block=1; confidence=0.96 -->
## 3.3.3 Similarity of normal and spherical distributions

In high dimensions $N(0,I_n)$ is not concentrated near the origin but in a thin spherical shell of width $O(1)$ around the sphere of radius $\sqrt{n}$. The concentration inequality (3.3) for the norm of $g\sim N(0,I_n)$ gives
$$\mathbb{P}\Big\{\big|\|g\|_2-\sqrt{n}\big|\ge t\Big\}\le 2\exp(-ct^2)\quad\text{for all }t\ge 0. \tag{3.7}$$

<a id="pdf-681b6f3d947f-p060-b002"></a>
<!-- pdf-source: page=60; block=2; confidence=0.97 -->
**Exercise 3.3.7 (Normal and spherical distributions).** Represent $g\sim N(0,I_n)$ in polar form $g=r\theta$, with $r=\|g\|_2$ and direction $\theta=g/\|g\|_2$. Prove:
(a) $r$ and $\theta$ are independent;
(b) $\theta$ is uniformly distributed on the unit sphere $S^{n-1}$.

<a id="pdf-681b6f3d947f-p060-b003"></a>
<!-- pdf-source: page=60; block=3; confidence=0.96 -->
Since (3.7) gives $r=\|g\|_2\approx\sqrt{n}$ with high probability, $g\approx\sqrt{n}\,\theta\sim\mathrm{Unif}(\sqrt{n}\,S^{n-1})$, i.e.
$$N(0,I_n)\approx \mathrm{Unif}\big(\sqrt{n}\,S^{n-1}\big). \tag{3.8}$$
Illustrated in Figure 3.6.

<a id="pdf-681b6f3d947f-p060-b004"></a>
<!-- pdf-source: page=60; block=4; confidence=0.94 -->
## 3.3.4 Frames

**Definition (coordinate distribution).** Let $X$ be uniform on $\{\sqrt{n}\,e_i:i=1,\dots,n\}$, where $\{e_i\}_{i=1}^n$ is the canonical basis of $\mathbb{R}^n$:
$$X\sim\mathrm{Unif}\{\sqrt{n}\,e_i:i=1,\dots,n\}.$$
Then $X$ is isotropic. Gaussian is the most convenient ("best") high-dimensional distribution; the coordinate distribution is the most discrete ("worst"). A general class of discrete, isotropic distributions arises in signal processing as frames.

<a id="pdf-681b6f3d947f-p061-b001"></a>
<!-- pdf-source: page=61; block=1; confidence=0.90 -->
Figure 3.6: in high dimensions the standard normal distribution is nearly the uniform distribution on the sphere of radius √n.

<a id="pdf-681b6f3d947f-p061-b002"></a>
<!-- pdf-source: page=61; block=2; confidence=0.98 -->
**Definition 3.3.8.** A *frame* is a set of vectors $\{u_i\}_{i=1}^N$ in $\mathbb{R}^n$ satisfying an approximate Parseval identity: there exist *frame bounds* $A,B>0$ with $A\|x\|_2^2 \le \sum_{i=1}^N \langle u_i,x\rangle^2 \le B\|x\|_2^2$ for all $x\in\mathbb{R}^n$. If $A=B$ the frame is called *tight*.

<a id="pdf-681b6f3d947f-p061-b003"></a>
<!-- pdf-source: page=61; block=3; confidence=0.97 -->
**Exercise 3.3.9.** Show $\{u_i\}_{i=1}^N$ is a tight frame in $\mathbb{R}^n$ with bound $A$ iff $\sum_{i=1}^N u_i u_i^{\mathsf T} = A I_n$ (3.9). Hint: proceed as in the proof of Lemma 3.2.3.

<a id="pdf-681b6f3d947f-p061-b004"></a>
<!-- pdf-source: page=61; block=4; confidence=0.96 -->
Multiplying (3.9) by $x$ gives the *frame expansion* $\sum_{i=1}^N \langle u_i,x\rangle\, u_i = Ax$ for all $x\in\mathbb{R}^n$ (3.10). For an orthonormal basis this is the classical basis expansion, holding with $A=1$.

<a id="pdf-681b6f3d947f-p061-b005"></a>
<!-- pdf-source: page=61; block=5; confidence=0.93 -->
Tight frames generalize orthonormal bases without requiring linear independence. Any orthonormal basis is a tight frame, as is the "Mercedes-Benz frame" of three equidistant points on a circle in $\mathbb{R}^2$. This motivates linking tight frames to isotropic distributions.

<a id="pdf-681b6f3d947f-p061-b006"></a>
<!-- pdf-source: page=61; block=6; confidence=0.80 -->
**Lemma 3.3.10 (Tight frames and isotropic distributions).** *(a)* Consider a tight frame $\{u_i\}_{i=1}^N$ in $\mathbb{R}^n$ ... [part (a) is cut off mid-sentence at the bottom of this page and continues on the next page].

<a id="pdf-681b6f3d947f-p062-b001"></a>
<!-- pdf-source: page=62; block=1; confidence=0.90 -->
Figure 3.7: equidistant points on a circle forming a tight frame in $\mathbb{R}^2$ (the Mercedes-Benz frame).

<a id="pdf-681b6f3d947f-p062-b002"></a>
<!-- pdf-source: page=62; block=2; confidence=0.97 -->
**Lemma 3.3.10 (Tight frames and isotropic distributions).** *(a)* Let $\{u_i\}_{i=1}^N$ be a tight frame in $\mathbb{R}^n$ with bounds $A=B$, and let $X\sim\mathrm{Unif}\{u_i: i=1,\dots,N\}$. Then $(N/A)^{1/2}X$ is isotropic in $\mathbb{R}^n$. *(b)* Let $X$ be isotropic in $\mathbb{R}^n$ taking finitely many values $x_i$ with probabilities $p_i$, $i=1,\dots,N$. Then $u_i:=\sqrt{p_i}\,x_i$ form a tight frame with bounds $A=B=1$.

<a id="pdf-681b6f3d947f-p062-b003"></a>
<!-- pdf-source: page=62; block=3; confidence=0.96 -->
**Proof.** (1) WLOG $A=N$; then (3.9) gives $\sum_{i=1}^N u_i u_i^{\mathsf T}=N I_n$. Dividing by $N$ and reading $\tfrac1N\sum_{i=1}^N$ as an expectation shows $X$ is isotropic. (2) Isotropy means $\mathbb{E}\,XX^{\mathsf T}=\sum_{i=1}^N p_i x_i x_i^{\mathsf T}=I_n$; setting $u_i:=\sqrt{p_i}\,x_i$ yields (3.9) with $A=1$. $\square$

<a id="pdf-681b6f3d947f-p062-b004"></a>
<!-- pdf-source: page=62; block=4; confidence=0.95 -->
**3.3.5 Isotropic convex sets.** A bounded convex set $K\subset\mathbb{R}^n$ with non-empty interior is a *convex body*. Let $X\sim\mathrm{Unif}(K)$, uniform w.r.t. normalized volume on $K$.

<a id="pdf-681b6f3d947f-p063-b001"></a>
<!-- pdf-source: page=63; block=1; confidence=0.95 -->
Assume $\mathbb{E}X=0$ (translate $K$); let $\Sigma$ be the covariance of $X$. By Exercise 3.2.2, $Z:=\Sigma^{-1/2}X$ is isotropic, and $Z\sim\mathrm{Unif}(\Sigma^{-1/2}K)$. Thus $T:=\Sigma^{-1/2}$ makes the uniform distribution on $TK$ isotropic; $TK$ is itself called an isotropic body, a well-conditioned version of $K$ with $T$ as preconditioner.

<a id="pdf-681b6f3d947f-p063-b002"></a>
<!-- pdf-source: page=63; block=2; confidence=0.90 -->
Figure 3.8: convex body $K$ mapped to isotropic body $TK$ via preconditioner $T=\Sigma^{-1/2}$ from the covariance $\Sigma$ of $K$.

<a id="pdf-681b6f3d947f-p063-b003"></a>
<!-- pdf-source: page=63; block=3; confidence=0.92 -->
**3.4 Sub-gaussian distributions in higher dimensions.** Extending the notion from Section 2.5, guided by Exercise 3.3.4: $X$ is normal in $\mathbb{R}^n$ iff all one-dimensional marginals $\langle X,x\rangle$ are normal.

<a id="pdf-681b6f3d947f-p063-b004"></a>
<!-- pdf-source: page=63; block=4; confidence=0.98 -->
**Definition 3.4.1 (Sub-gaussian random vectors).** A random vector $X$ in $\mathbb{R}^n$ is *sub-gaussian* if the marginals $\langle X,x\rangle$ are sub-gaussian for all $x\in\mathbb{R}^n$. Its sub-gaussian norm is $\|X\|_{\psi_2}=\sup_{x\in S^{n-1}}\|\langle X,x\rangle\|_{\psi_2}$.

<a id="pdf-681b6f3d947f-p063-b005"></a>
<!-- pdf-source: page=63; block=5; confidence=0.85 -->
**Lemma 3.4.2 (Sub-gaussian distributions with independent coordinates).** A random vector with independent sub-gaussian coordinates is sub-gaussian [statement is truncated at "Let ..." on this page and completed on the following page].

<a id="pdf-681b6f3d947f-p064-b001"></a>
<!-- pdf-source: page=64; block=1; confidence=0.95 -->
**Lemma 3.4.2.** Let $X=(X_1,\dots,X_n)\in\mathbb{R}^n$ be a random vector with independent, mean-zero, sub-gaussian coordinates $X_i$. Then $X$ is a sub-gaussian random vector and
$$\|X\|_{\psi_2}\le C\max_{i\le n}\|X_i\|_{\psi_2}.$$

<a id="pdf-681b6f3d947f-p064-b002"></a>
<!-- pdf-source: page=64; block=2; confidence=0.95 -->
**Proof.** Uses that a sum of independent sub-gaussians is sub-gaussian (Proposition 2.6.1). For a fixed unit vector $x=(x_1,\dots,x_n)\in S^{n-1}$,
$$\|\langle X,x\rangle\|_{\psi_2}^2=\Big\|\sum_{i=1}^n x_iX_i\Big\|_{\psi_2}^2\le C\sum_{i=1}^n x_i^2\|X_i\|_{\psi_2}^2\le C\max_{i\le n}\|X_i\|_{\psi_2}^2,$$
the last step using $\sum_{i=1}^n x_i^2=1$. $\qquad\blacksquare$

<a id="pdf-681b6f3d947f-p064-b003"></a>
<!-- pdf-source: page=64; block=3; confidence=0.92 -->
**Exercise 3.4.3.** Clarifies the role of independence in Lemma 3.4.2. (1) If $X=(X_1,\dots,X_n)$ has sub-gaussian coordinates $X_i$ (no independence assumed), show $X$ is a sub-gaussian random vector. (2) Find an example of a random vector $X$ with $\|X\|_{\psi_2}\gg\max_{i\le n}\|X_i\|_{\psi_2}$.

<a id="pdf-681b6f3d947f-p064-b004"></a>
<!-- pdf-source: page=64; block=4; confidence=0.90 -->
**3.4.1 Gaussian and Bernoulli distributions.** The multivariate normal $N(\mu,\Sigma)$ is sub-gaussian. The standard normal vector $X\sim N(0,I_n)$ satisfies $\|X\|_{\psi_2}\le C$ (all one-dimensional marginals are $N(0,1)$). The multivariate symmetric Bernoulli distribution has independent symmetric Bernoulli coordinates, so Lemma 3.4.2 gives $\|X\|_{\psi_2}\le C$.

<a id="pdf-681b6f3d947f-p064-b005"></a>
<!-- pdf-source: page=64; block=5; confidence=0.88 -->
**3.4.2 Discrete distributions.** Extreme example (from Section 3.3.4): the coordinate distribution — a random vector $X$ uniformly distributed on the set $\{\sqrt{n}\,e_i : i=1,\dots,n\}$, where $e_i$ are the canonical basis vectors in $\mathbb{R}^n$.

<a id="pdf-681b6f3d947f-p065-b001"></a>
<!-- pdf-source: page=65; block=1; confidence=0.90 -->
Every distribution supported on a finite set is formally sub-gaussian, so $X$ is sub-gaussian. Unlike the Gaussian and Bernoulli cases, the coordinate distribution has a very large sub-gaussian norm.

<a id="pdf-681b6f3d947f-p065-b002"></a>
<!-- pdf-source: page=65; block=2; confidence=0.93 -->
**Exercise 3.4.4.** Show that for the coordinate distribution $\|X\|_{\psi_2}\asymp\sqrt{n/\log n}$. (Such a large norm makes it useless to treat $X$ as sub-gaussian.)

<a id="pdf-681b6f3d947f-p065-b003"></a>
<!-- pdf-source: page=65; block=3; confidence=0.90 -->
More generally, discrete distributions are not good sub-gaussian distributions unless supported on exponentially large sets.

<a id="pdf-681b6f3d947f-p065-b004"></a>
<!-- pdf-source: page=65; block=4; confidence=0.92 -->
**Exercise 3.4.5.** Let $X$ be an isotropic random vector supported in a finite set $T\subset\mathbb{R}^n$. Show that for $X$ to be sub-gaussian with $\|X\|_{\psi_2}=O(1)$, the cardinality must be exponentially large: $|T|\ge e^{cn}$. This rules out frames (Section 3.3.4) as good sub-gaussian distributions unless they have exponentially many terms.

<a id="pdf-681b6f3d947f-p065-b005"></a>
<!-- pdf-source: page=65; block=5; confidence=0.90 -->
**3.4.3 Uniform distribution on the sphere.** Independent coordinates are not necessary for a good sub-gaussian vector. The uniform distribution on the sphere of radius $\sqrt{n}$ (Section 3.3.1) is shown to be sub-gaussian by reducing it to $N(0,I_n)$.

<a id="pdf-681b6f3d947f-p065-b006"></a>
<!-- pdf-source: page=65; block=6; confidence=0.95 -->
**Theorem 3.4.6 (Uniform distribution on the sphere is sub-gaussian).** Let $X\sim\mathrm{Unif}(\sqrt{n}\,S^{n-1})$ be uniformly distributed on the Euclidean sphere in $\mathbb{R}^n$ centered at the origin with radius $\sqrt{n}$. Then $X$ is sub-gaussian and $\|X\|_{\psi_2}\le C$.

<a id="pdf-681b6f3d947f-p065-b007"></a>
<!-- pdf-source: page=65; block=7; confidence=0.93 -->
**Proof.** Take $g\sim N(0,I_n)$. Since $g/\|g\|_2$ is uniform on $S^{n-1}$ (Exercise 3.3.7), by rescaling $X\sim\mathrm{Unif}(\sqrt{n}\,S^{n-1})$ is represented as
$$X=\sqrt{n}\,\frac{g}{\|g\|_2}.$$
It remains to show all one-dimensional marginals $\langle X,x\rangle$ are sub-gaussian.

<a id="pdf-681b6f3d947f-p066-b001"></a>
<!-- pdf-source: page=66; block=1; confidence=0.93 -->
**Proof (continued).** By rotation invariance take $x=(1,0,\dots,0)$, so $\langle X,x\rangle=X_1$. Bound the tail
$$p(t):=\mathbb{P}\{|X_1|\ge t\}=\mathbb{P}\Big\{\tfrac{|g_1|}{\|g\|_2}\ge\tfrac{t}{\sqrt{n}}\Big\}.$$
Concentration of norm (Theorem 3.1.1) gives $\big\|\,\|g\|_2-\sqrt{n}\,\big\|_{\psi_2}\le C$, so the event $E:=\{\|g\|_2\ge\sqrt{n}/2\}$ has complement of probability $\mathbb{P}(E^c)\le 2\exp(-cn)$ by (2.14) — equation (3.11). Then
$$p(t)\le\mathbb{P}\Big\{\tfrac{|g_1|}{\|g\|_2}\ge\tfrac{t}{\sqrt{n}}\text{ and }E\Big\}+\mathbb{P}(E^c)\le\mathbb{P}\{|g_1|\ge t/2\text{ and }E\}+2\exp(-cn)\le 2\exp(-t^2/8)+2\exp(-cn),$$
using the definition of $E$, (3.11), and the sub-gaussian tail (2.3). If $t\le\sqrt{n}$ then $2\exp(-cn)\le 2\exp(-ct^2/8)$, giving $p(t)\le 4\exp(-c'{t^2})$. If $t>\sqrt{n}$ then $p(t)=0$ since $|X_1|\le\|X\|_2=\sqrt{n}$. By the characterization of sub-gaussian distributions (Proposition 2.5.2, Remark 2.5.3) the proof is complete. $\qquad\blacksquare$

<a id="pdf-681b6f3d947f-p066-b002"></a>
<!-- pdf-source: page=66; block=2; confidence=0.93 -->
**Exercise 3.4.7 (Uniform distribution on the Euclidean ball).** Extend Theorem 3.4.6 to the uniform distribution on the ball $B(0,\sqrt{n})\subset\mathbb{R}^n$: show that $X\sim\mathrm{Unif}(B(0,\sqrt{n}))$ is sub-gaussian with $\|X\|_{\psi_2}\le C$.

<a id="pdf-681b6f3d947f-p067-b001"></a>
<!-- pdf-source: page=67; block=1; confidence=0.97 -->
## 3.4 Sub-gaussian distributions in higher dimensions

<a id="pdf-681b6f3d947f-p067-b002"></a>
<!-- pdf-source: page=67; block=2; confidence=0.95 -->
**Remark 3.4.8 (Projective limit theorem).** Relates Theorem 3.4.6 to the projective central limit theorem: marginals of the uniform distribution on the sphere become asymptotically normal. Precisely, if $X \sim \mathrm{Unif}(\sqrt{n}\,S^{n-1})$ then for any fixed unit vector $x$, $\langle X, x\rangle \to N(0,1)$ in distribution as $n\to\infty$. Theorem 3.4.6 is a concentration version of this, analogous to Hoeffding's inequality (Section 2.2) as a concentration version of the classical CLT.

<a id="pdf-681b6f3d947f-p067-b003"></a>
<!-- pdf-source: page=67; block=3; confidence=0.90 -->
*Figure 3.9.* Projection of the uniform distribution on the sphere of radius $\sqrt{n}$ onto a line converges to $N(0,1)$ as $n\to\infty$.

<a id="pdf-681b6f3d947f-p067-b004"></a>
<!-- pdf-source: page=67; block=4; confidence=0.93 -->
### 3.4.4 Uniform distribution on convex sets

For a convex body $K$ and isotropic $X \sim \mathrm{Unif}(K)$, one asks whether $X$ is always sub-gaussian. It holds for some bodies — e.g. the Euclidean ball of radius $\sqrt{n}$ (Exercise 3.4.7) and the unit cube $[-1,1]^n$ (Lemma 3.4.2) — but fails for others.

<a id="pdf-681b6f3d947f-p067-b005"></a>
<!-- pdf-source: page=67; block=5; confidence=0.94 -->
**Exercise 3.4.9.** For the $\ell_1$-ball $K := \{x\in\mathbb{R}^n : \|x\|_1 \le r\}$: (a) show $\mathrm{Unif}(K)$ is isotropic for some $r \asymp n$; (b) show its sub-gaussian norm is not bounded by an absolute constant as $n$ grows.

<a id="pdf-681b6f3d947f-p067-b006"></a>
<!-- pdf-source: page=67; block=6; confidence=0.90 -->
**Result (general isotropic convex body).** For general isotropic convex body $K$, $X \sim \mathrm{Unif}(K)$ has all sub-exponential marginals: $\|\langle X, x\rangle\|_{\psi_1} \le C$ for all unit vectors $x$ [statement continues on next page].

<a id="pdf-681b6f3d947f-p068-b001"></a>
<!-- pdf-source: page=68; block=1; confidence=0.92 -->
The bound $\|\langle X,x\rangle\|_{\psi_1}\le C$ holds for all unit vectors $x$. It follows from C. Borell's lemma, itself a consequence of the Brunn–Minkowski inequality; see [81, Section 2.2.b3].

<a id="pdf-681b6f3d947f-p068-b002"></a>
<!-- pdf-source: page=68; block=2; confidence=0.94 -->
**Exercise 3.4.10.** Show the concentration inequality of Theorem 3.1.1 may fail for a general isotropic sub-gaussian random vector $X$, so independence of the coordinates is essential in that result.

<a id="pdf-681b6f3d947f-p068-b003"></a>
<!-- pdf-source: page=68; block=3; confidence=0.93 -->
## 3.5 Application: Grothendieck's inequality and semidefinite programming

Uses high-dimensional Gaussian distributions to give a probabilistic proof of Grothendieck's inequality, later applied to computationally hard problems.

<a id="pdf-681b6f3d947f-p068-b004"></a>
<!-- pdf-source: page=68; block=4; confidence=0.96 -->
**Theorem 3.5.1 (Grothendieck's inequality).** Let $(a_{ij})$ be an $m\times n$ real matrix such that $\left|\sum_{i,j} a_{ij} x_i y_j\right| \le 1$ for all $x_i, y_j \in \{-1,1\}$. Then for any Hilbert space $H$ and vectors $u_i, v_j \in H$ with $\|u_i\|=\|v_j\|=1$,
$$\left|\sum_{i,j} a_{ij}\langle u_i, v_j\rangle\right| \le K,$$
where $K \le 1.783$ is an absolute constant.

<a id="pdf-681b6f3d947f-p068-b005"></a>
<!-- pdf-source: page=68; block=5; confidence=0.93 -->
Two probabilistic proofs are given: the one in this section yields $K \le 288$; Section 3.7 gives $K \le 1.783$.

<a id="pdf-681b6f3d947f-p068-b006"></a>
<!-- pdf-source: page=68; block=6; confidence=0.94 -->
**Exercise 3.5.2.** (a) The hypothesis is equivalent to
$$\left|\sum_{i,j} a_{ij} x_i y_j\right| \le \max_i |x_i|\cdot \max_j |y_j| \quad (3.12)$$
for all real $x_i, y_j$. (b) The conclusion is equivalent to
$$\left|\sum_{i,j} a_{ij}\langle u_i, v_j\rangle\right| \le K \max_i \|u_i\|\cdot \max_j \|v_j\| \quad (3.13)$$
[continues next page for any Hilbert space $H$ and vectors $u_i, v_j \in H$].

<a id="pdf-681b6f3d947f-p069-b001"></a>
<!-- pdf-source: page=69; block=1; confidence=0.90 -->
### 3.5 Application: Grothendieck's inequality and semidefinite programming (continued)

Equation (3.13) holds for any Hilbert space $H$ and vectors $u_i, v_j \in H$.

<a id="pdf-681b6f3d947f-p069-b002"></a>
<!-- pdf-source: page=69; block=2; confidence=0.94 -->
**Proof of Theorem 3.5.1 (with $K\le 288$). Step 1: Reductions.** The inequality is trivial if $K$ may depend on $A=(a_{ij})$ (e.g. $K=\sum_{ij}|a_{ij}|$). Let $K=K(A)$ be the smallest constant making (3.13) valid for given $A$, all $H$, and all $u_i,v_j$; the goal is to show $K$ is independent of $A, m, n$. Without loss of generality take $H=\mathbb{R}^N$ with the Euclidean norm $\|\cdot\|_2$, and fix $u_i, v_j \in \mathbb{R}^N$ realizing the smallest $K$:
$$\sum_{i,j} a_{ij}\langle u_i, v_j\rangle = K, \qquad \|u_i\|_2 = \|v_j\|_2 = 1.$$

<a id="pdf-681b6f3d947f-p069-b003"></a>
<!-- pdf-source: page=69; block=3; confidence=0.94 -->
**Step 2: Introducing randomness.** Realize the vectors via Gaussians $U_i := \langle g, u_i\rangle$, $V_j := \langle g, v_j\rangle$ with $g \sim N(0, I_N)$. Then $U_i, V_j$ are standard normal with $\mathbb{E}\, U_i V_j = \langle u_i, v_j\rangle$, so
$$K = \sum_{i,j} a_{ij}\langle u_i, v_j\rangle = \mathbb{E}\sum_{i,j} a_{ij} U_i V_j. \quad (3.14)$$
If $U_i, V_j$ were bounded a.s. by $R$, then (3.12) (rescaled) would give $\left|\sum_{i,j} a_{ij} U_i V_j\right| \le R^2$ a.s., hence $K \le R^2$.

<a id="pdf-681b6f3d947f-p069-b004"></a>
<!-- pdf-source: page=69; block=4; confidence=0.93 -->
**Step 3: Truncation.** Since $U_i, V_j \sim N(0,1)$ are not bounded, fix $R \ge 1$ and decompose $U_i = U_i^- + U_i^+$ with $U_i^- = U_i \mathbf{1}_{\{|U_i|\le R\}}$, $U_i^+ = U_i \mathbf{1}_{\{|U_i|>R\}}$, and similarly $V_j = V_j^- + V_j^+$. The parts $U_i^-, V_j^-$ are bounded by $R$; the remainders are small in $L^2$: by Exercise 2.1.4,
$$\|U_i^+\|_{L^2}^2 \le 2\left(R + \tfrac{1}{R}\right)\tfrac{1}{\sqrt{2\pi}}\, e^{-R^2/2} < \tfrac{4}{R^2}. \quad (3.15)$$

<a id="pdf-681b6f3d947f-p069-b005"></a>
<!-- pdf-source: page=69; block=5; confidence=0.92 -->
*Footnote 4.* Replace $H$ by the subspace spanned by the $u_i, v_j$, of dimension at most $N := m+n$; since all $N$-dimensional Hilbert spaces are isometric (in particular to $\mathbb{R}^N$ with $\|\cdot\|_2$), the reduction is justified.

<a id="pdf-681b6f3d947f-p070-b001"></a>
<!-- pdf-source: page=70; block=1; confidence=0.95 -->
**Step 4 (Breaking up the sum).** From (3.14), K = E Σ_{i,j} a_{ij}(U_i^- + U_i^+)(V_j^- + V_j^+); expanding yields four sums, bounded separately. **S₁ := E Σ a_{ij}U_i^- V_j^-:** since U_i^-, V_j^- are bounded a.s. by R, assumption (3.12) gives S₁ ≤ R². **S₂ := E Σ a_{ij}U_i^+ V_j^-:** because U_i^+ is unbounded, view U_i^+ and V_j^- as elements of the Hilbert space L² with ⟨X,Y⟩_{L²} = E XY, so S₂ = Σ a_{ij}⟨U_i^+, V_j^-⟩_{L²} (3.16). By (3.15), ‖U_i^+‖_{L²} < 2/R and ‖V_j^-‖_{L²} ≤ ‖V_j‖_{L²} = 1; applying conclusion (3.13) with H = L² gives S₂ ≤ K·(2/R). The remaining sums S₃ := E Σ a_{ij}U_i^- V_j^+ and S₄ := E Σ a_{ij}U_i^+ V_j^+ are bounded like S₂. (Applying Grothendieck's inequality here is valid because K was fixed at the start as the optimal such constant.)

<a id="pdf-681b6f3d947f-p070-b002"></a>
<!-- pdf-source: page=70; block=2; confidence=0.97 -->
**Step 5 (Putting everything together).** Combining the four bounds in (3.14) gives K ≤ R² + 6K/R. Choosing R = 12 and solving yields K ≤ 288, which proves the theorem.

<a id="pdf-681b6f3d947f-p070-b003"></a>
<!-- pdf-source: page=70; block=3; confidence=0.93 -->
**Exercise 3.5.3 (Symmetric matrices, x_i = y_i).** Deduce this symmetric version of Grothendieck's inequality. Let A = (a_{ij}) be a symmetric n×n real matrix that is either positive semidefinite or has zero diagonal, and suppose |Σ_{i,j} a_{ij}x_i x_j| ≤ 1 for all x_i ∈ {−1,1}. Then for any Hilbert space H and unit vectors u_i, v_j ∈ H (‖u_i‖ = ‖v_j‖ = 1), |Σ_{i,j} a_{ij}⟨u_i, v_j⟩| ≤ 2K (3.17), where K is the absolute Grothendieck constant. *Hint:* use the polarization identity ⟨Ax,y⟩ = ⟨Au,u⟩ − ⟨Av,v⟩ with u = (x+y)/2, v = (x−y)/2. (Statement completes on page 71.)

<a id="pdf-681b6f3d947f-p071-b001"></a>
<!-- pdf-source: page=71; block=1; confidence=0.90 -->
**3.5.1 Semidefinite programming.** Computationally hard problems can be relaxed to tractable semidefinite programs, with Grothendieck's inequality certifying the quality of the relaxation.

<a id="pdf-681b6f3d947f-p071-b002"></a>
<!-- pdf-source: page=71; block=2; confidence=0.96 -->
**Definition 3.5.4 (Semidefinite program).** An optimization problem of the form: maximize ⟨A, X⟩ subject to X ⪰ 0 and ⟨B_i, X⟩ = b_i for i = 1,…,m (3.18), where A and B_i are given n×n matrices, b_i are given reals, and the variable X ranges over n×n symmetric positive semidefinite matrices (X ⪰ 0). The inner product is the canonical one on n×n matrices, ⟨A, X⟩ = tr(AᵀX) = Σ_{i,j=1}^n A_{ij}X_{ij} (3.19).

<a id="pdf-681b6f3d947f-p071-b003"></a>
<!-- pdf-source: page=71; block=3; confidence=0.93 -->
Minimizing rather than maximizing in (3.18) is still an SDP (replace A by −A). Every SDP is a convex program: it maximizes the linear functional ⟨A,X⟩ over the convex set of PSD matrices intersected with the affine constraints ⟨B_i,X⟩ = b_i, hence is algorithmically tractable (e.g. via interior point methods).

<a id="pdf-681b6f3d947f-p072-b001"></a>
<!-- pdf-source: page=72; block=1; confidence=0.95 -->
**Semidefinite relaxations.** Consider the integer optimization problem: maximize Σ_{i,j=1}^n A_{ij}x_i x_j subject to x_i = ±1 for i = 1,…,n (3.20), where A is a given symmetric n×n matrix. Its feasible set is the 2^n vectors x ∈ {−1,1}^n, so exhaustive search is exponential; (3.20) is NP-hard in general.

<a id="pdf-681b6f3d947f-p072-b002"></a>
<!-- pdf-source: page=72; block=2; confidence=0.95 -->
To relax (3.20), replace each scalar x_i = ±1 by a unit vector X_i ∈ ℝ^n, giving: maximize Σ_{i,j=1}^n A_{ij}⟨X_i, X_j⟩ subject to ‖X_i‖₂ = 1 for i = 1,…,n (3.21).

<a id="pdf-681b6f3d947f-p072-b003"></a>
<!-- pdf-source: page=72; block=3; confidence=0.94 -->
**Exercise 3.5.5.** Show that problem (3.21) is equivalent to the semidefinite program: maximize ⟨A, X⟩ subject to X ⪰ 0 and X_{ii} = 1 for i = 1,…,n (3.22). *Hint:* use the Gram matrix of the X_i (entries ⟨X_i, X_j⟩), and describe how to translate a solution of (3.22) back into one of (3.21).

<a id="pdf-681b6f3d947f-p072-b004"></a>
<!-- pdf-source: page=72; block=4; confidence=0.96 -->
**Theorem 3.5.6.** Let A be a symmetric positive semidefinite n×n matrix. Let INT(A) be the maximum of the integer problem (3.20) and SDP(A) the maximum of the semidefinite problem (3.21). Then INT(A) ≤ SDP(A) ≤ 2K·INT(A), where K ≤ 1.783 is the Grothendieck constant.

<a id="pdf-681b6f3d947f-p072-b005"></a>
<!-- pdf-source: page=72; block=5; confidence=0.94 -->
**Proof.** The bound INT(A) ≤ SDP(A) follows by taking X_i = (x_i, 0, 0, …, 0)ᵀ. The bound SDP(A) ≤ 2K·INT(A) follows from Grothendieck's inequality for symmetric matrices (Exercise 3.5.3), after arguing that the absolute values may be dropped. (It remains nonobvious how to compute x_i attaining this approximate value; discussion continues beyond the supplied pages.)

<a id="pdf-681b6f3d947f-p073-b001"></a>
<!-- pdf-source: page=73; block=1; confidence=0.90 -->
Notes that a solution of (3.21) can be rounded into labels $x_i=\pm1$ approximately solving (3.20); this is illustrated on the NP-hard maximum cut problem.

<a id="pdf-681b6f3d947f-p073-b002"></a>
<!-- pdf-source: page=73; block=2; confidence=0.93 -->
**Exercise 3.5.7.** For an $m\times n$ matrix $A$, formulate as a semidefinite program the problem: maximize $\sum_{i,j} A_{ij}\langle X_i, Y_j\rangle$ subject to $\|X_i\|_2=\|Y_j\|_2=1$ for all $i,j$, over $X_i,Y_j\in\mathbb{R}^k$, $k\in\mathbb{N}$. Hint: write the objective as $\tfrac12\operatorname{tr}(\tilde A ZZ^\mathsf{T})$ with $\tilde A=\begin{bmatrix}0&A\\A^\mathsf{T}&0\end{bmatrix}$, $Z=\begin{bmatrix}X\\Y\end{bmatrix}$ whose rows are $X_i^\mathsf{T}$ and $Y_j^\mathsf{T}$; then identify matrices $ZZ^\mathsf{T}$ with unit rows as the symmetric positive semidefinite matrices with all diagonal entries equal to $1$.

<a id="pdf-681b6f3d947f-p073-b003"></a>
<!-- pdf-source: page=73; block=3; confidence=0.97 -->
**Section 3.6 — Application: Maximum cut for graphs.** Uses semidefinite relaxation for the NP-hard maximum cut problem.

<a id="pdf-681b6f3d947f-p073-b004"></a>
<!-- pdf-source: page=73; block=4; confidence=0.95 -->
**Subsection 3.6.1 — Graphs and cuts.** An undirected graph $G=(V,E)$ is a vertex set $V$ with an edge set $E$ of unordered vertex pairs; here graphs are finite and simple (no loops or multiple edges).

<a id="pdf-681b6f3d947f-p073-b005"></a>
<!-- pdf-source: page=73; block=5; confidence=0.96 -->
**Definition 3.6.1 (Maximum cut).** Partitioning the vertices of $G$ into two disjoint sets, the *cut* is the number of edges crossing between the sets. The *maximum cut* $\mathrm{MAX\text{-}CUT}(G)$ maximizes the cut over all vertex partitions.

<a id="pdf-681b6f3d947f-p073-b006"></a>
<!-- pdf-source: page=73; block=6; confidence=0.95 -->
Figure 3.10 depicts a maximum cut (dashed line) from partitioning vertices into black and white sets, with $\mathrm{MAX\text{-}CUT}(G)=7$.

<a id="pdf-681b6f3d947f-p074-b001"></a>
<!-- pdf-source: page=74; block=1; confidence=0.97 -->
Computing the maximum cut of a graph is NP-hard.

<a id="pdf-681b6f3d947f-p074-b002"></a>
<!-- pdf-source: page=74; block=2; confidence=0.95 -->
**Subsection 3.6.2 — A simple 0.5-approximation algorithm.** Relax maximum cut to a semidefinite program via the method of Section 3.5.1, after translating the problem into linear algebra.

<a id="pdf-681b6f3d947f-p074-b003"></a>
<!-- pdf-source: page=74; block=3; confidence=0.97 -->
**Definition 3.6.2 (Adjacency matrix).** The adjacency matrix $A$ of a graph $G$ on $n$ vertices is the symmetric $n\times n$ matrix with $A_{ij}=1$ if vertices $i,j$ are joined by an edge and $A_{ij}=0$ otherwise.

<a id="pdf-681b6f3d947f-p074-b004"></a>
<!-- pdf-source: page=74; block=4; confidence=0.96 -->
Label vertices $1,\dots,n$; a partition is a sign vector $x=(x_i)\in\{-1,1\}^n$, with $\operatorname{sign}(x_i)$ indicating the subset of vertex $i$. The cut equals the number of edges joining opposite-sign vertices:
$$\mathrm{CUT}(G,x)=\tfrac12\!\!\sum_{i,j:\,x_ix_j=-1}\!\!A_{ij}=\tfrac14\sum_{i,j=1}^n A_{ij}(1-x_ix_j),\tag{3.23}$$
the factor $\tfrac12$ removing double counting of $(i,j)$ and $(j,i)$. Maximizing gives
$$\mathrm{MAX\text{-}CUT}(G)=\tfrac14\max\Big\{\sum_{i,j=1}^n A_{ij}(1-x_ix_j):\ x_i=\pm1\ \forall i\Big\}.\tag{3.24}$$

<a id="pdf-681b6f3d947f-p074-b005"></a>
<!-- pdf-source: page=74; block=5; confidence=0.96 -->
**Proposition 3.6.3 (0.5-approximation algorithm for maximum cut).** Partition the vertices of $G$ uniformly at random over all $2^n$ partitions. Then the expected cut equals $0.5\,|E|\ge 0.5\,\mathrm{MAX\text{-}CUT}(G)$, where $|E|$ is the number of edges.

<a id="pdf-681b6f3d947f-p074-b006"></a>
<!-- pdf-source: page=74; block=6; confidence=0.95 -->
**Proof.** The random cut comes from $x\sim\mathrm{Unif}(\{-1,1\}^n)$ with independent symmetric Bernoulli coordinates. In (3.23), $\mathbb{E}\,x_ix_j=0$ for $i\ne j$, and $A_{ij}=0$ for $i=j$ (no loops). By linearity of expectation,
$$\mathbb{E}\,\mathrm{CUT}(G,x)=\tfrac14\sum_{i,j=1}^n A_{ij}=\tfrac12|E|.$$
(Concluded on the next page.)

<a id="pdf-681b6f3d947f-p075-b001"></a>
<!-- pdf-source: page=75; block=1; confidence=0.94 -->
**Proof (concluded).** This completes the proof of Proposition 3.6.3.

<a id="pdf-681b6f3d947f-p075-b002"></a>
<!-- pdf-source: page=75; block=2; confidence=0.94 -->
**Exercise 3.6.4.** For any $\varepsilon>0$, give a $(0.5-\varepsilon)$-approximation algorithm for maximum cut that always returns a valid cut but may have random running time, and bound the expected running time. Hint: cut $G$ repeatedly and bound the expected number of experiments.

<a id="pdf-681b6f3d947f-p075-b003"></a>
<!-- pdf-source: page=75; block=3; confidence=0.95 -->
**Subsection 3.6.3 — Semidefinite relaxation.** Presents the $0.878$-approximation algorithm of Goemans and Williamson, based on a semidefinite relaxation of (3.24).

<a id="pdf-681b6f3d947f-p075-b004"></a>
<!-- pdf-source: page=75; block=4; confidence=0.95 -->
The semidefinite relaxation of (3.24), motivated by (3.21), is
$$\mathrm{SDP}(G):=\tfrac14\max\Big\{\sum_{i,j=1}^n A_{ij}\big(1-\langle X_i,X_j\rangle\big):\ X_i\in\mathbb{R}^n,\ \|X_i\|_2=1\ \forall i\Big\}.\tag{3.25}$$
It approximates $\mathrm{MAX\text{-}CUT}(G)$ within factor $0.878$, and a solution $(X_i)$ yields an actual partition (labels $x_i=\pm1$) attaining this value.

<a id="pdf-681b6f3d947f-p075-b005"></a>
<!-- pdf-source: page=75; block=5; confidence=0.95 -->
**Randomized rounding.** Choose a random hyperplane through the origin in $\mathbb{R}^n$, splitting the vectors $X_i$ into two parts assigned labels $+1$ and $-1$. Equivalently, draw $g\sim N(0,I_n)$ and set
$$x_i:=\operatorname{sign}\langle X_i,g\rangle,\qquad i=1,\dots,n.\tag{3.26}$$

<a id="pdf-681b6f3d947f-p075-b006"></a>
<!-- pdf-source: page=75; block=6; confidence=0.96 -->
**Theorem 3.6.5 (0.878-approximation algorithm for maximum cut).** Let $G$ have adjacency matrix $A$, and let $x=(x_i)$ result from randomized rounding of the solution $(X_i)$ of the SDP (3.25). Then
$$\mathbb{E}\,\mathrm{CUT}(G,x)\ge 0.878\,\mathrm{SDP}(G)\ge 0.878\,\mathrm{MAX\text{-}CUT}(G).$$

<a id="pdf-681b6f3d947f-p075-b007"></a>
<!-- pdf-source: page=75; block=7; confidence=0.92 -->
The proof rests on an elementary identity, an advanced version of identity (3.6) used for Grothendieck's inequality (Theorem 3.5.1). Footnote: in rounding, any rotation-invariant distribution on $\mathbb{R}^n$ (e.g. uniform on the sphere $S^{n-1}$) may replace the normal distribution.

<a id="pdf-681b6f3d947f-p076-b001"></a>
<!-- pdf-source: page=76; block=1; confidence=0.90 -->
Figure 3.11: illustrates randomized rounding of vectors $X_i \in \mathbb{R}^n$ to labels $x_i = \pm 1$ via a random hyperplane with normal vector $g$; the shown configuration yields $x_1=x_2=x_3=1$, $x_4=x_5=x_6=-1$.

<a id="pdf-681b6f3d947f-p076-b002"></a>
<!-- pdf-source: page=76; block=2; confidence=0.98 -->
**Lemma 3.6.6 (Grothendieck's identity).** For $g \sim N(0, I_n)$ and any fixed $u, v \in S^{n-1}$,
$$\mathbb{E}\,\operatorname{sign}\langle g, u\rangle \operatorname{sign}\langle g, v\rangle = \frac{2}{\pi}\arcsin\langle u, v\rangle.$$

<a id="pdf-681b6f3d947f-p076-b003"></a>
<!-- pdf-source: page=76; block=3; confidence=0.95 -->
**Exercise 3.6.7.** Prove Grothendieck's identity. Hint: show the probability that $\langle g,u\rangle$ and $\langle g,v\rangle$ have opposite signs equals $\alpha/\pi$, where $\alpha \in [0,\pi]$ is the angle between $u$ and $v$; use rotation invariance to reduce to $\mathbb{R}^2$.

<a id="pdf-681b6f3d947f-p076-b004"></a>
<!-- pdf-source: page=76; block=4; confidence=0.97 -->
To linearize the $\arcsin$, use the numeric inequality (3.27), verifiable via software (Figure 3.12):
$$1 - \frac{2}{\pi}\arcsin t = \frac{2}{\pi}\arccos t \ge 0.878\,(1 - t), \qquad t \in [-1, 1]. \tag{3.27}$$

<a id="pdf-681b6f3d947f-p076-b005"></a>
<!-- pdf-source: page=76; block=5; confidence=0.96 -->
**Proof of Theorem 3.6.5.** By (3.23) and linearity of expectation,
$$\mathbb{E}\,\mathrm{CUT}(G, x) = \frac{1}{4}\sum_{i,j=1}^n A_{ij}\,(1 - \mathbb{E}\,x_i x_j).$$
The rounding step (3.26) gives
$$1 - \mathbb{E}\,x_i x_j = 1 - \mathbb{E}\,\operatorname{sign}\langle X_i, g\rangle \operatorname{sign}\langle X_j, g\rangle = 1 - \frac{2}{\pi}\arcsin\langle X_i, X_j\rangle \ge 0.878\,(1 - \langle X_i, X_j\rangle),$$
using Grothendieck's identity (Lemma 3.6.6) and then (3.27).

<a id="pdf-681b6f3d947f-p077-b001"></a>
<!-- pdf-source: page=77; block=1; confidence=0.90 -->
Figure 3.12: plot verifying that $\frac{2}{\pi}\arccos t \ge 0.878\,(1 - t)$ holds for all $t \in [-1, 1]$.

<a id="pdf-681b6f3d947f-p077-b002"></a>
<!-- pdf-source: page=77; block=2; confidence=0.95 -->
**Proof (concl.).** Hence
$$\mathbb{E}\,\mathrm{CUT}(G, x) \ge 0.878 \cdot \frac{1}{4}\sum_{i,j=1}^n A_{ij}\,(1 - \langle X_i, X_j\rangle) = 0.878\,\mathrm{SDP}(G),$$
proving the first inequality. The second is trivial since $\mathrm{SDP}(G) \ge \text{MAX-CUT}(G)$. $\blacksquare$

<a id="pdf-681b6f3d947f-p077-b003"></a>
<!-- pdf-source: page=77; block=3; confidence=0.97 -->
**3.7 Kernel trick, and tightening of Grothendieck's inequality.**

<a id="pdf-681b6f3d947f-p077-b004"></a>
<!-- pdf-source: page=77; block=4; confidence=0.90 -->
An alternative proof of Grothendieck's inequality gives (almost) the best known constant $K \le 1.783$, improving the loose bound from Section 3.5. It is based on Grothendieck's identity (Lemma 3.6.6); the difficulty is the nonlinearity of $\arcsin$. Hypothetically, if $\mathbb{E}\,\operatorname{sign}\langle g,u\rangle\operatorname{sign}\langle g,v\rangle = \frac{2}{\pi}\langle u,v\rangle$ (linear), then
$$\frac{2}{\pi}\sum_{i,j} a_{ij}\langle u_i, v_j\rangle = \sum_{i,j} a_{ij}\,\mathbb{E}\,\operatorname{sign}\langle g, u_i\rangle\operatorname{sign}\langle g, v_j\rangle \le 1,$$
applying the hypothesis of Grothendieck's inequality with $x_i = \operatorname{sign}\langle g,u_i\rangle$, $y_j = \operatorname{sign}\langle g, v_j\rangle$, yielding $K \le \pi/2 \approx 1.57$. This is invalid because of the actual nonlinear $\frac{2}{\pi}\arcsin\langle u,v\rangle$; the fix is to represent $\frac{2}{\pi}\arcsin\langle u,v\rangle$ as a linear inner product $\langle u', v'\rangle$ of transformed vectors (the kernel trick).

<a id="pdf-681b6f3d947f-p078-b001"></a>
<!-- pdf-source: page=78; block=1; confidence=0.90 -->
The transformed vectors live in a Hilbert space $H$; this method is the kernel trick. One explicitly constructs nonlinear maps $u' = \Phi(u)$, $v' = \Psi(v)$, described using tensors (a higher-dimensional generalization of matrices).

<a id="pdf-681b6f3d947f-p078-b002"></a>
<!-- pdf-source: page=78; block=2; confidence=0.97 -->
**Definition 3.7.1 (Tensors).** A $k$-th order tensor $(a_{i_1\ldots i_k})$ is a $k$-dimensional array of reals. The canonical inner product on $\mathbb{R}^{n_1\times\cdots\times n_k}$ is
$$\langle A, B\rangle := \sum_{i_1,\ldots,i_k} a_{i_1\ldots i_k} b_{i_1\ldots i_k}. \tag{3.28}$$

<a id="pdf-681b6f3d947f-p078-b003"></a>
<!-- pdf-source: page=78; block=3; confidence=0.96 -->
**Example 3.7.2.** Scalars, vectors, matrices are tensors. For $m\times n$ matrices, (3.28) specializes (cf. (3.19)) to $\langle A, B\rangle = \operatorname{tr}(A^T B) = \sum_{i=1}^m\sum_{j=1}^n A_{ij} B_{ij}$.

<a id="pdf-681b6f3d947f-p078-b004"></a>
<!-- pdf-source: page=78; block=4; confidence=0.96 -->
**Example 3.7.3 (Rank-one tensors).** A vector $u \in \mathbb{R}^n$ defines the $k$-th order tensor product $u^{\otimes k} := (u_{i_1}\cdots u_{i_k}) \in \mathbb{R}^{n\times\cdots\times n}$. For $k=2$, $u\otimes u = (u_i u_j)_{i,j=1}^n = uu^T$. Tensor products $u\otimes v\otimes\cdots\otimes z$ of distinct vectors are defined analogously.

<a id="pdf-681b6f3d947f-p078-b005"></a>
<!-- pdf-source: page=78; block=5; confidence=0.97 -->
**Exercise 3.7.4.** Show that for any $u, v \in \mathbb{R}^n$ and $k \in \mathbb{N}$, $\langle u^{\otimes k}, v^{\otimes k}\rangle = \langle u, v\rangle^k$.

<a id="pdf-681b6f3d947f-p078-b006"></a>
<!-- pdf-source: page=78; block=6; confidence=0.94 -->
Consequence: the nonlinear form $\langle u,v\rangle^k$ is a linear inner product in another space — there exist a Hilbert space $H$ and $\Phi:\mathbb{R}^n\to H$ with $\langle\Phi(u),\Phi(v)\rangle = \langle u,v\rangle^k$; here $H$ is the space of $k$-th order tensors and $\Phi(u)=u^{\otimes k}$.

<a id="pdf-681b6f3d947f-p078-b007"></a>
<!-- pdf-source: page=78; block=7; confidence=0.90 -->
**Exercise 3.7.5.** (Statement truncated in source; extends the kernel representation to more general nonlinearities.)

<a id="pdf-681b6f3d947f-p079-b001"></a>
<!-- pdf-source: page=79; block=1; confidence=0.98 -->
## 3.7 Kernel trick, and tightening of Grothendieck's inequality

<a id="pdf-681b6f3d947f-p079-b002"></a>
<!-- pdf-source: page=79; block=2; confidence=0.95 -->
**Exercise 3.7.5.** (a) Show there exist a Hilbert space $H$ and $\Phi:\mathbb{R}^n\to H$ with $\langle\Phi(u),\Phi(v)\rangle = 2\langle u,v\rangle^2 + 5\langle u,v\rangle^3$ for all $u,v\in\mathbb{R}^n$ (hint: $H=\mathbb{R}^{n\times n}\oplus\mathbb{R}^{n\times n\times n}$). (b) For a polynomial $f:\mathbb{R}\to\mathbb{R}$ with non-negative coefficients, construct $H,\Phi$ with $\langle\Phi(u),\Phi(v)\rangle = f(\langle u,v\rangle)$. (c) Same for any real analytic $f$ with non-negative coefficients, i.e. $f(x)=\sum_{k=0}^\infty a_k x^k$ (3.29) with $a_k\ge 0$ for all $k$.

<a id="pdf-681b6f3d947f-p079-b003"></a>
<!-- pdf-source: page=79; block=3; confidence=0.94 -->
**Exercise 3.7.6.** For any real analytic $f:\mathbb{R}\to\mathbb{R}$ (coefficients in (3.29) possibly negative), show there exist a Hilbert space $H$ and $\Phi,\Psi:\mathbb{R}^n\to H$ with $\langle\Phi(u),\Psi(v)\rangle = f(\langle u,v\rangle)$ for all $u,v\in\mathbb{R}^n$. Moreover, $\|\Phi(u)\|^2=\|\Psi(u)\|^2=\sum_{k=0}^\infty |a_k|\,\|u\|_2^{2k}$. Hint: build $\Phi$ as in Exercise 3.7.5, encoding the signs of $a_k$ into $\Psi$.

<a id="pdf-681b6f3d947f-p079-b004"></a>
<!-- pdf-source: page=79; block=4; confidence=0.95 -->
Specialize the kernel trick to the non-linearity $\tfrac{2}{\pi}\arcsin\langle u,v\rangle$ appearing in Grothendieck's identity.

<a id="pdf-681b6f3d947f-p079-b005"></a>
<!-- pdf-source: page=79; block=5; confidence=0.96 -->
**Lemma 3.7.7.** There exist a Hilbert space $H$ and transformations $\Phi,\Psi:S^{n-1}\to S(H)$ (with $S(H)$ the unit sphere of $H$) such that
$$\tfrac{2}{\pi}\arcsin\langle\Phi(u),\Psi(v)\rangle = \beta\langle u,v\rangle \quad\text{for all }u,v\in S^{n-1}, \tag{3.30}$$
where $\beta=\tfrac{2}{\pi}\ln(1+\sqrt{2})$.

<a id="pdf-681b6f3d947f-p079-b006"></a>
<!-- pdf-source: page=79; block=6; confidence=0.94 -->
**Proof.** Rewrite (3.30) as
$$\langle\Phi(u),\Psi(v)\rangle = \sin\!\left(\tfrac{\beta\pi}{2}\langle u,v\rangle\right). \tag{3.31}$$
Exercise 3.7.6 supplies the Hilbert space $H$ and maps $\Phi,\Psi:\mathbb{R}^n\to H$ satisfying (3.31); it remains to fix $\beta$ so that unit vectors map to unit vectors. *(continues on p. 80)*

<a id="pdf-681b6f3d947f-p080-b001"></a>
<!-- pdf-source: page=80; block=1; confidence=0.95 -->
**Proof (cont.).** Using the Taylor series $\sinh t = t+\tfrac{t^3}{3!}+\tfrac{t^5}{5!}+\cdots$ and $\sin t = t-\tfrac{t^3}{3!}+\tfrac{t^5}{5!}-\cdots$, Exercise 3.7.6 gives for every $u\in S^{n-1}$
$$\|\Phi(u)\|^2=\|\Psi(u)\|^2=\sinh\!\left(\tfrac{\beta\pi}{2}\right).$$
This equals $1$ when $\beta:=\tfrac{2}{\pi}\operatorname{arcsinh}(1)=\tfrac{2}{\pi}\ln(1+\sqrt{2})$. $\blacksquare$

<a id="pdf-681b6f3d947f-p080-b002"></a>
<!-- pdf-source: page=80; block=2; confidence=0.95 -->
Grothendieck's inequality (Theorem 3.5.1) now holds with constant $K\le \tfrac{1}{\beta}=\tfrac{\pi}{2\ln(1+\sqrt{2})}\approx 1.783$.

<a id="pdf-681b6f3d947f-p080-b003"></a>
<!-- pdf-source: page=80; block=3; confidence=0.93 -->
**Proof of Theorem 3.5.1.** WLOG $u_i,v_j\in S^{N-1}$ (same reduction as in Section 3.5). Lemma 3.7.7 gives unit vectors $u_i'=\Phi(u_i)$, $v_j'=\Psi(v_j)$ in a Hilbert space $H$ with $\tfrac{2}{\pi}\arcsin\langle u_i',v_j'\rangle = \beta\langle u_i,v_j\rangle$ for all $i,j$. WLOG $H=\mathbb{R}^M$. Then
$$\beta\sum_{i,j}a_{ij}\langle u_i,v_j\rangle = \sum_{i,j}a_{ij}\cdot\tfrac{2}{\pi}\arcsin\langle u_i',v_j'\rangle = \sum_{i,j}a_{ij}\,\mathbb{E}\,\operatorname{sign}\langle g,u_i'\rangle\operatorname{sign}\langle g,v_j'\rangle \le 1,$$
by Lemma 3.6.6, swapping sum and expectation and applying the Grothendieck hypothesis with $x_i=\operatorname{sign}\langle g,u_i'\rangle$, $y_j=\operatorname{sign}\langle g,v_j'\rangle$. This gives the inequality for $K\le 1/\beta$. $\blacksquare$

<a id="pdf-681b6f3d947f-p080-b004"></a>
<!-- pdf-source: page=80; block=4; confidence=0.92 -->
### 3.7.1 Kernels and feature maps

Motivating question: which other non-linearities can the kernel trick handle? Let $K:X\times X\to\mathbb{R}$ be a function of two variables on a set $X$. *(continues on p. 81)*

<a id="pdf-681b6f3d947f-p081-b001"></a>
<!-- pdf-source: page=81; block=1; confidence=0.95 -->
Question: when do there exist a Hilbert space $H$ and $\Phi:X\to H$ with
$$\langle\Phi(u),\Phi(v)\rangle = K(u,v)\quad\text{for all }u,v\in X? \tag{3.32}$$
By Mercer's and Moore–Aronszajn's theorems, the necessary and sufficient condition is that $K$ be a **positive semidefinite kernel**: for any finite $u_1,\dots,u_N\in X$, the matrix $(K(u_i,u_j))_{i,j=1}^N$ is symmetric and positive semidefinite. $\Phi$ is the **feature map**, and $H$ is the (unique) reproducing kernel Hilbert space built from $K$.

<a id="pdf-681b6f3d947f-p081-b002"></a>
<!-- pdf-source: page=81; block=2; confidence=0.94 -->
Common positive semidefinite kernels on $\mathbb{R}^n$: the **Gaussian (RBF) kernel** $K(u,v)=\exp\!\left(-\tfrac{\|u-v\|_2^2}{2\sigma^2}\right)$, $\sigma>0$; and the **polynomial kernel** $K(u,v)=(\langle u,v\rangle+r)^k$, $r>0$, $k\in\mathbb{N}$. In ML the kernel trick (3.32) lets linear methods handle non-linear models; the explicit $H$ and $\Phi$ are usually not needed, since (3.32) computes $K(u,v)$ directly.

<a id="pdf-681b6f3d947f-p081-b003"></a>
<!-- pdf-source: page=81; block=3; confidence=0.93 -->
## 3.8 Notes

Theorem 3.1.1 (concentration of the norm of random vectors) is known but hard to locate; the more general Theorem 6.3.2, valid for anisotropic random vectors, is proved later. Whether the quadratic dependence on $K$ in Theorem 3.1.1 is optimal is unknown. For random vectors with dependent coordinates — in particular $X$ uniform in a convex set $K$ — norm concentration is a central problem in geometric functional analysis; see [93, Section 2] and [36, Chapter 12].

<a id="pdf-681b6f3d947f-p082-b001"></a>
<!-- pdf-source: page=82; block=1; confidence=0.90 -->
Bibliographic notes. Cramér-Wold's theorem (Exercise 3.3.4) follows from uniqueness of characteristic functions. Frames generalize orthogonal bases (signal processing / compression). Random vectors uniform on convex sets are treated in Sections 3.3.5 and 3.4.4. The sub-gaussian random vector material of Section 3.4 follows reference [222], with an alternative geometric proof of Theorem 3.4.6 available elsewhere.

<a id="pdf-681b6f3d947f-p082-b002"></a>
<!-- pdf-source: page=82; block=2; confidence=0.95 -->
Grothendieck's inequality (Theorem 3.5.1), proved by Grothendieck in 1953, originally gave the constant bound $K \le \sinh(\pi/2) \approx 2.30$. Krivine's argument (second proof, Section 3.7) yields $K \le \dfrac{\pi}{2\ln(1+\sqrt{2})} \approx 1.783$, the best known explicit bound. It is known the true optimal constant is strictly smaller than Krivine's bound, but no explicit value is known.

<a id="pdf-681b6f3d947f-p082-b003"></a>
<!-- pdf-source: page=82; block=3; confidence=0.95 -->
Notes on semidefinite relaxations of hard optimization problems and the use of Grothendieck's inequality in analyzing them. The maximum cut presentation (Section 3.6) follows standard references; the semidefinite approach was introduced by Goemans and Williamson (1995), whose approximation ratio $\dfrac{2}{\pi}\min_{0\le\theta\le\pi}\dfrac{\theta}{1-\cos\theta} \approx 0.878$ remains the best known for max-cut and is optimal if the Unique Games Conjecture holds. Section 3.7 gives Krivine's proof and briefly discusses kernel methods / reproducing kernel Hilbert spaces.

<a id="pdf-681b6f3d947f-p083-b001"></a>
<!-- pdf-source: page=83; block=1; confidence=0.92 -->
**Chapter 4. Random matrices.** Introduction to the non-asymptotic theory of random matrices. Overview: Section 4.1 reviews singular values and matrix norms; Section 4.2 introduces nets, covering/packing numbers, and metric entropy; Sections 4.4 and 4.6 develop the ε-net argument, giving an operator-norm bound (Theorem 4.4.5) and a two-sided bound on all singular values (Theorem 4.6.1). Applications: spectral clustering for network communities (4.5), covariance estimation (4.7), and spectral clustering of geometric point sets (4.7.1).

<a id="pdf-681b6f3d947f-p083-b002"></a>
<!-- pdf-source: page=83; block=2; confidence=0.90 -->
**Section 4.1 (Preliminaries on matrices).** Recalls the singular value decomposition and introduces two matrix norms — operator and Frobenius — and their relationships.

<a id="pdf-681b6f3d947f-p083-b003"></a>
<!-- pdf-source: page=83; block=3; confidence=0.95 -->
**Definition (SVD).** For a real $m\times n$ matrix $A$, the singular value decomposition is
$$A = \sum_{i=1}^{r} s_i u_i v_i^{\mathsf T}, \qquad r = \operatorname{rank}(A). \tag{4.1}$$
The non-negative $s_i = s_i(A)$ are the singular values; $u_i \in \mathbb{R}^m$ the left singular vectors; $v_i \in \mathbb{R}^n$ the right singular vectors. Extending by $s_i = 0$ for $r < i \le n$, the singular values are arranged non-increasingly: $s_1 \ge s_2 \ge \cdots \ge s_n \ge 0$.

<a id="pdf-681b6f3d947f-p084-b001"></a>
<!-- pdf-source: page=84; block=1; confidence=0.95 -->
**Singular values and eigenvectors.** The left singular vectors $u_i$ are orthonormal eigenvectors of $AA^{\mathsf T}$ and the right singular vectors $v_i$ are orthonormal eigenvectors of $A^{\mathsf T}A$. The singular values are the square roots of the eigenvalues:
$$s_i(A) = \sqrt{\lambda_i(AA^{\mathsf T})} = \sqrt{\lambda_i(A^{\mathsf T}A)}.$$
If $A$ is symmetric, then $s_i(A) = |\lambda_i(A)|$, and both left and right singular vectors are eigenvectors of $A$.

<a id="pdf-681b6f3d947f-p084-b002"></a>
<!-- pdf-source: page=84; block=2; confidence=0.94 -->
**Courant-Fischer min-max theorem.** For a symmetric $A$ with eigenvalues in non-increasing order,
$$\lambda_i(A) = \max_{\dim E = i} \ \min_{x \in S(E)} \langle Ax, x\rangle, \tag{4.2}$$
where the max is over $i$-dimensional subspaces $E \subseteq \mathbb{R}^n$ and $S(E)$ is the unit sphere of $E$. Correspondingly, for singular values,
$$s_i(A) = \max_{\dim E = i} \ \min_{x \in S(E)} \|Ax\|_2.$$

<a id="pdf-681b6f3d947f-p084-b003"></a>
<!-- pdf-source: page=84; block=3; confidence=0.95 -->
**Exercise 4.1.1.** For an invertible $A = \sum_{i=1}^{n} s_i u_i v_i^{\mathsf T}$, verify that $A^{-1} = \sum_{i=1}^{n} \frac{1}{s_i} v_i u_i^{\mathsf T}$.

<a id="pdf-681b6f3d947f-p084-b004"></a>
<!-- pdf-source: page=84; block=4; confidence=0.93 -->
**Definition (operator / spectral norm).** Writing $\ell_2^m$ for $\mathbb{R}^m$ with the Euclidean norm, $A$ acts as a linear operator $\ell_2^n \to \ell_2^m$. Its operator (spectral) norm is
$$\|A\| = \max_{x \in \mathbb{R}^n\setminus\{0\}} \frac{\|Ax\|_2}{\|x\|_2} = \max_{x \in S^{n-1}} \|Ax\|_2 = \max_{x \in S^{n-1},\, y \in S^{m-1}} \langle Ax, y\rangle.$$

<a id="pdf-681b6f3d947f-p085-b001"></a>
<!-- pdf-source: page=85; block=1; confidence=0.95 -->
Operator norm equals largest singular value: $s_1(A)=\|A\|$. The smallest singular value $s_n(A)$ is nonzero only for tall matrices ($m\ge n$); then $A$ has full rank $n$ iff $s_n(A)>0$. For full-rank $A$, $s_n(A)=1/\|A^+\|$, where $A^+$ is the Moore–Penrose pseudoinverse and $\|A^+\|$ is the norm of $A^{-1}$ restricted to the image of $A$.

<a id="pdf-681b6f3d947f-p085-b002"></a>
<!-- pdf-source: page=85; block=2; confidence=0.99 -->
## 4.1.3 Frobenius norm

<a id="pdf-681b6f3d947f-p085-b003"></a>
<!-- pdf-source: page=85; block=3; confidence=0.95 -->
**Definition (Frobenius / Hilbert–Schmidt norm).** For $A=(A_{ij})$, $\|A\|_F=\left(\sum_{i=1}^m\sum_{j=1}^n |A_{ij}|^2\right)^{1/2}$; this is the Euclidean norm on $\mathbb{R}^{m\times n}$. In terms of singular values, $\|A\|_F=\left(\sum_{i=1}^r s_i(A)^2\right)^{1/2}$. The canonical inner product is $\langle A,B\rangle=\mathrm{tr}(A^TB)=\sum_{i=1}^m\sum_{j=1}^n A_{ij}B_{ij}$ (4.3), which generates it: $\|A\|_F^2=\langle A,A\rangle$. Writing $s=(s_1,\dots,s_r)$, $\|A\|=\|s\|_\infty$ and $\|A\|_F=\|s\|_2$; using $\|s\|_\infty\le\|s\|_2\le\sqrt{r}\,\|s\|_\infty$ gives the sharp relation $\|A\|\le\|A\|_F\le\sqrt{r}\,\|A\|$ (4.4).

<a id="pdf-681b6f3d947f-p086-b001"></a>
<!-- pdf-source: page=86; block=1; confidence=0.97 -->
**Exercise 4.1.2.** Prove that the singular values $s_i$ of any matrix $A$ satisfy $s_i\le \tfrac{1}{\sqrt{i}}\|A\|_F$.

<a id="pdf-681b6f3d947f-p086-b002"></a>
<!-- pdf-source: page=86; block=2; confidence=0.99 -->
## 4.1.4 Low-rank approximation

<a id="pdf-681b6f3d947f-p086-b003"></a>
<!-- pdf-source: page=86; block=3; confidence=0.95 -->
**Theorem (Eckart–Young–Mirsky).** For the best rank-$k$ approximation ($k<r=\mathrm{rank}(A)$) of $A$ minimizing the distance in operator (or Frobenius) norm, the minimizer is the truncated SVD $A_k=\sum_{i=1}^k s_i u_i v_i^T$, i.e. $\|A-A_k\|=\min_{\mathrm{rank}(A')\le k}\|A-A'\|$. The same holds for the Frobenius norm and any unitarily invariant norm; $A_k$ is the best rank-$k$ approximation of $A$.

<a id="pdf-681b6f3d947f-p086-b004"></a>
<!-- pdf-source: page=86; block=4; confidence=0.96 -->
**Exercise 4.1.3 (Best rank $k$ approximation).** Express $\|A-A_k\|^2$ and $\|A-A_k\|_F^2$ in terms of the singular values $s_i$ of $A$.

<a id="pdf-681b6f3d947f-p086-b005"></a>
<!-- pdf-source: page=86; block=5; confidence=0.99 -->
## 4.1.5 Approximate isometries

<a id="pdf-681b6f3d947f-p086-b006"></a>
<!-- pdf-source: page=86; block=6; confidence=0.94 -->
$s_1(A)$ and $s_n(A)$ are respectively the smallest $M$ and largest $m$ making $m\|x\|_2\le\|Ax\|_2\le M\|x\|_2$ for all $x\in\mathbb{R}^n$ (4.5). Applied to $x-y$ with best bounds: $s_n(A)\|x-y\|_2\le\|Ax-Ay\|_2\le s_1(A)\|x-y\|_2$. Thus $A:\mathbb{R}^n\to\mathbb{R}^m$ changes distances by a factor between $s_n(A)$ and $s_1(A)$, controlling geometric distortion. Distance-preserving matrices are isometries.

<a id="pdf-681b6f3d947f-p087-b001"></a>
<!-- pdf-source: page=87; block=1; confidence=0.95 -->
**Exercise 4.1.4 (Isometries).** For an $m\times n$ matrix $A$ with $m\ge n$, prove equivalence of: (a) $A^TA=I_n$; (b) $P:=AA^T$ is an orthogonal projection in $\mathbb{R}^m$ onto an $n$-dimensional subspace; (c) $A$ is an isometry (isometric embedding $\mathbb{R}^n\to\mathbb{R}^m$): $\|Ax\|_2=\|x\|_2$ for all $x$; (d) all singular values equal 1, i.e. $s_n(A)=s_1(A)=1$. (Footnote: $P$ is a projection if $P^2=P$, orthogonal if image and kernel are orthogonal.)

<a id="pdf-681b6f3d947f-p087-b002"></a>
<!-- pdf-source: page=87; block=2; confidence=0.97 -->
**Lemma 4.1.5 (Approximate isometries).** Let $A$ be $m\times n$ and $\delta>0$. If $\|A^TA-I_n\|\le\max(\delta,\delta^2)$, then $(1-\delta)\|x\|_2\le\|Ax\|_2\le(1+\delta)\|x\|_2$ for all $x\in\mathbb{R}^n$ (4.6). Consequently all singular values lie in $[1-\delta,1+\delta]$: $1-\delta\le s_n(A)\le s_1(A)\le 1+\delta$ (4.7).

<a id="pdf-681b6f3d947f-p087-b003"></a>
<!-- pdf-source: page=87; block=3; confidence=0.95 -->
**Proof.** WLOG $\|x\|_2=1$. By assumption, $\max(\delta,\delta^2)\ge|\langle(A^TA-I_n)x,x\rangle|=|\,\|Ax\|_2^2-1\,|$. Applying the elementary inequality $\max(|z-1|,|z-1|^2)\le|z^2-1|$ for $z\ge0$ (4.8) with $z=\|Ax\|_2$ gives $|\,\|Ax\|_2-1\,|\le\delta$, proving (4.6), which implies (4.7). $\square$

<a id="pdf-681b6f3d947f-p087-b004"></a>
<!-- pdf-source: page=87; block=4; confidence=0.97 -->
**Exercise 4.1.6 (Approximate isometries).** Prove the converse to Lemma 4.1.5: if (4.7) holds, then $\|A^TA-I_n\|\le 3\max(\delta,\delta^2)$.

<a id="pdf-681b6f3d947f-p088-b001"></a>
<!-- pdf-source: page=88; block=1; confidence=0.95 -->
**Remark 4.1.7 (Projections vs. isometries).** For an n×m matrix Q, QQ^T = I_n iff P := Q^T Q is an orthogonal projection in R^m onto an n-dimensional subspace; then Q itself is called a projection from R^m onto R^n. A is an isometric embedding of R^n into R^m iff A^T is a projection from R^m onto R^n; analogously, an approximate isometry A has an approximate projection A^T.

<a id="pdf-681b6f3d947f-p088-b002"></a>
<!-- pdf-source: page=88; block=2; confidence=0.96 -->
**Exercise 4.1.8 (Isometries and projections from unitary matrices).** For a fixed unitary matrix U, show that any sub-matrix of U formed by selecting a subset of its columns is an isometry, and any sub-matrix formed by selecting a subset of its rows is a projection.

<a id="pdf-681b6f3d947f-p088-b003"></a>
<!-- pdf-source: page=88; block=3; confidence=0.95 -->
## 4.2 Nets, covering numbers and packing numbers

Introduces the ε-net argument for analyzing random matrices and relates ε-nets to covering, packing, entropy, volume, and coding.

<a id="pdf-681b6f3d947f-p088-b004"></a>
<!-- pdf-source: page=88; block=4; confidence=0.95 -->
**Definition 4.2.1 (ε-net).** In a metric space (T, d), given K ⊂ T and ε > 0, a subset N ⊆ K is an ε-net of K if every point of K lies within distance ε of some point of N: ∀x ∈ K ∃x_0 ∈ N : d(x, x_0) ≤ ε. Equivalently, K is covered by balls of radius ε centered at points of N. Canonical example: T = R^n with Euclidean distance d(x, y) = ‖x − y‖_2 (eq. 4.9).

<a id="pdf-681b6f3d947f-p088-b005"></a>
<!-- pdf-source: page=88; block=5; confidence=0.96 -->
**Definition 4.2.2 (Covering numbers).** The covering number N(K, d, ε) is the smallest cardinality of an ε-net of K; equivalently, the smallest number of closed balls of radius ε with centers in K whose union covers K.

<a id="pdf-681b6f3d947f-p089-b001"></a>
<!-- pdf-source: page=89; block=1; confidence=0.93 -->
**Figure 4.1.** (a) A covering of a pentagon K by seven ε-balls shows N(K, ε) ≤ 7. (b) A packing of K by ten ε/2-balls shows P(K, ε) ≥ 10.

<a id="pdf-681b6f3d947f-p089-b002"></a>
<!-- pdf-source: page=89; block=2; confidence=0.95 -->
**Remark 4.2.3 (Compactness).** A subset K of a complete metric space (T, d) is precompact (its closure is compact) iff N(K, d, ε) < ∞ for every ε > 0; thus N(K, d, ε) is a quantitative measure of compactness.

<a id="pdf-681b6f3d947f-p089-b003"></a>
<!-- pdf-source: page=89; block=3; confidence=0.96 -->
**Definition 4.2.4 (Packing numbers).** A subset N of (T, d) is ε-separated if d(x, y) > ε for all distinct x, y ∈ N. The packing number P(K, d, ε) is the largest cardinality of an ε-separated subset of K ⊂ T.

<a id="pdf-681b6f3d947f-p089-b004"></a>
<!-- pdf-source: page=89; block=4; confidence=0.95 -->
**Exercise 4.2.5 (Packing the balls into K).** (a) If T is a normed space, prove P(K, d, ε) equals the largest number of disjoint closed balls of radius ε/2 with centers in K. (b) Give an example showing (a) may fail in a general metric space.

<a id="pdf-681b6f3d947f-p089-b005"></a>
<!-- pdf-source: page=89; block=5; confidence=0.96 -->
**Lemma 4.2.6 (Nets from separated sets).** If N is a maximal ε-separated subset of K, then N is an ε-net of K. (Maximal = adding any new point destroys ε-separation.)

<a id="pdf-681b6f3d947f-p089-b006"></a>
<!-- pdf-source: page=89; block=6; confidence=0.95 -->
**Proof.** Let x ∈ K. If x ∈ N, take x_0 = x. If x ∉ N, maximality forces N ∪ {x} to fail ε-separation, meaning d(x, x_0) ≤ ε for some x_0 ∈ N. ∎

<a id="pdf-681b6f3d947f-p089-b007"></a>
<!-- pdf-source: page=89; block=7; confidence=0.93 -->
**Remark 4.2.7 (Constructing a net).** Lemma 4.2.6 gives an algorithm: choose x_1 ∈ K arbitrarily, then x_2 ∈ K farther than ε from x_1, then x_3 farther than ε from both x_1, x_2, and so on. If K is compact the algorithm terminates in finite time and yields an ε-net of K.

<a id="pdf-681b6f3d947f-p090-b001"></a>
<!-- pdf-source: page=90; block=1; confidence=0.97 -->
**Lemma 4.2.8 (Equivalence of covering and packing numbers).** For any K ⊂ T and ε > 0: P(K, d, 2ε) ≤ N(K, d, ε) ≤ P(K, d, ε).

<a id="pdf-681b6f3d947f-p090-b002"></a>
<!-- pdf-source: page=90; block=2; confidence=0.95 -->
**Proof.** Upper bound follows from Lemma 4.2.6. Lower bound: take a 2ε-separated set P = {x_i} in K and an ε-net N = {y_j}. Each x_i lies in a closed ε-ball centered at some y_j, and each such ball contains at most one x_i (a closed ε-ball cannot hold two 2ε-separated points), so by pigeonhole |P| ≤ |N|. Since P, N are arbitrary, the lower bound follows. ∎

<a id="pdf-681b6f3d947f-p090-b003"></a>
<!-- pdf-source: page=90; block=3; confidence=0.95 -->
**Exercise 4.2.9 (Allowing centers outside K).** Define the exterior covering number N^ext(K, d, ε) like N(K, d, ε) but without requiring ball centers x_i ∈ K. Prove: N^ext(K, d, ε) ≤ N(K, d, ε) ≤ N^ext(K, d, ε/2).

<a id="pdf-681b6f3d947f-p090-b004"></a>
<!-- pdf-source: page=90; block=4; confidence=0.95 -->
**Exercise 4.2.10 (Monotonicity).** Give a counterexample to: L ⊂ K ⟹ N(L, d, ε) ≤ N(K, d, ε). Then prove the approximate version: L ⊂ K ⟹ N(L, d, ε) ≤ N(K, d, ε/2).

<a id="pdf-681b6f3d947f-p090-b005"></a>
<!-- pdf-source: page=90; block=5; confidence=0.93 -->
### 4.2.1 Covering numbers and volume

Specializes to T = R^n with the Euclidean metric d(x, y) = ‖x − y‖_2 (eq. 4.9), abbreviating N(K, ε) := N(K, d, ε). Notes there is no full equivalence between covering numbers and volume, since flat sets have zero volume but nonzero covering numbers.

<a id="pdf-681b6f3d947f-p091-b001"></a>
<!-- pdf-source: page=91; block=1; confidence=0.95 -->
A useful, often sharp partial equivalence between covering and packing numbers rests on the Minkowski sum of sets in $\mathbb{R}^n$.

<a id="pdf-681b6f3d947f-p091-b002"></a>
<!-- pdf-source: page=91; block=2; confidence=0.98 -->
**Definition 4.2.11 (Minkowski sum).** For $A, B \subseteq \mathbb{R}^n$, the Minkowski sum is $A + B := \{a + b : a \in A,\ b \in B\}$.

<a id="pdf-681b6f3d947f-p091-b003"></a>
<!-- pdf-source: page=91; block=3; confidence=0.95 -->
Figure 4.2: the Minkowski sum of a square and a circle is a square with rounded corners.

<a id="pdf-681b6f3d947f-p091-b004"></a>
<!-- pdf-source: page=91; block=4; confidence=0.96 -->
**Proposition 4.2.12 (Covering numbers and volume).** For $K \subseteq \mathbb{R}^n$ and $\varepsilon > 0$,
$$\frac{|K|}{|\varepsilon B_2^n|} \le \mathcal{N}(K, \varepsilon) \le \mathcal{P}(K, \varepsilon) \le \frac{|K + (\varepsilon/2)B_2^n|}{|(\varepsilon/2)B_2^n|}.$$
Here $|\cdot|$ is volume in $\mathbb{R}^n$, $B_2^n$ is the unit Euclidean ball, and $\varepsilon B_2^n$ is the Euclidean ball of radius $\varepsilon$.

<a id="pdf-681b6f3d947f-p091-b005"></a>
<!-- pdf-source: page=91; block=5; confidence=0.95 -->
**Proof.** The middle inequality is Lemma 4.2.8.

_Lower bound._ Let $N = \mathcal{N}(K, \varepsilon)$; $K$ is covered by $N$ balls of radius $\varepsilon$, so $|K| \le N \cdot |\varepsilon B_2^n|$; divide by $|\varepsilon B_2^n|$.

_Upper bound._ Let $N = \mathcal{P}(K, \varepsilon)$; construct $N$ disjoint closed balls $B(x_i, \varepsilon/2)$ with centers $x_i \in K$. These fit inside $K + (\varepsilon/2)B_2^n$, so $N \cdot |(\varepsilon/2)B_2^n| \le |K + (\varepsilon/2)B_2^n|$, giving the upper bound. $\square$

<a id="pdf-681b6f3d947f-p091-b006"></a>
<!-- pdf-source: page=91; block=6; confidence=0.97 -->
Footnote: $B_2^n = \{x \in \mathbb{R}^n : \|x\|_2 \le 1\}$.

<a id="pdf-681b6f3d947f-p092-b001"></a>
<!-- pdf-source: page=92; block=1; confidence=0.93 -->
The volumetric bound (4.10) implies that covering (and packing) numbers of the Euclidean ball and many other sets grow exponentially in the dimension $n$.

<a id="pdf-681b6f3d947f-p092-b002"></a>
<!-- pdf-source: page=92; block=2; confidence=0.96 -->
**Corollary 4.2.13 (Covering numbers of the Euclidean ball).** For any $\varepsilon > 0$,
$$\left(\tfrac{1}{\varepsilon}\right)^n \le \mathcal{N}(B_2^n, \varepsilon) \le \left(\tfrac{2}{\varepsilon} + 1\right)^n.$$
The same upper bound holds for the unit Euclidean sphere $S^{n-1}$.

<a id="pdf-681b6f3d947f-p092-b003"></a>
<!-- pdf-source: page=92; block=3; confidence=0.95 -->
**Proof.** Lower bound: from Proposition 4.2.12 with $|\varepsilon B_2^n| = \varepsilon^n |B_2^n|$. Upper bound: from Proposition 4.2.12,
$$\mathcal{N}(B_2^n, \varepsilon) \le \frac{|(1+\varepsilon/2)B_2^n|}{|(\varepsilon/2)B_2^n|} = \frac{(1+\varepsilon/2)^n}{(\varepsilon/2)^n} = \left(\tfrac{2}{\varepsilon}+1\right)^n.$$
The sphere bound follows the same way. $\square$

<a id="pdf-681b6f3d947f-p092-b004"></a>
<!-- pdf-source: page=92; block=4; confidence=0.95 -->
Equation (4.10): for $\varepsilon \in (0, 1]$, $\left(\tfrac{1}{\varepsilon}\right)^n \le \mathcal{N}(B_2^n, \varepsilon) \le \left(\tfrac{3}{\varepsilon}\right)^n$. For $\varepsilon > 1$, $\mathcal{N}(B_2^n, \varepsilon) = 1$.

<a id="pdf-681b6f3d947f-p092-b005"></a>
<!-- pdf-source: page=92; block=5; confidence=0.97 -->
**Definition 4.2.14 (Hamming cube).** The Hamming cube $\{0,1\}^n$ is all binary strings of length $n$. The Hamming distance is $d_H(x, y) := \#\{i : x(i) \ne y(i)\}$ for $x, y \in \{0,1\}^n$ (number of disagreeing bits). With this metric $(\{0,1\}^n, d_H)$ is the Hamming space.

<a id="pdf-681b6f3d947f-p092-b006"></a>
<!-- pdf-source: page=92; block=6; confidence=0.95 -->
**Exercise 4.2.15.** Verify $d_H$ is a metric.

**Exercise 4.2.16 (Covering/packing numbers of the Hamming cube).** For $K = \{0,1\}^n$ and integer $m \in [0, n]$, prove
$$\frac{2^n}{\sum_{k=0}^{m}\binom{n}{k}} \le \mathcal{N}(K, d_H, m) \le \mathcal{P}(K, d_H, m) \le \frac{2^n}{\sum_{k=0}^{\lfloor m/2 \rfloor}\binom{n}{k}}.$$
Hint: adapt the volumetric argument, replacing volume by cardinality; use binomial-sum bounds from Exercise 0.0.5.

<a id="pdf-681b6f3d947f-p093-b001"></a>
<!-- pdf-source: page=93; block=1; confidence=0.95 -->
**4.3 Application: error correcting codes.** Covering/packing arguments appear in coding theory; two examples relate covering and packing numbers to complexity and error correction.

<a id="pdf-681b6f3d947f-p093-b002"></a>
<!-- pdf-source: page=93; block=2; confidence=0.93 -->
**4.3.1 Metric entropy and complexity.** Covering/packing numbers measure the complexity of $K$; $\log_2 \mathcal{N}(K, \varepsilon)$ is the metric entropy, shown below to equal the number of bits needed to encode points of $K$.

<a id="pdf-681b6f3d947f-p093-b003"></a>
<!-- pdf-source: page=93; block=3; confidence=0.96 -->
**Proposition 4.3.1 (Metric entropy and coding).** Let $(T, d)$ be a metric space, $K \subset T$, and let $C(K, d, \varepsilon)$ be the smallest number of bits sufficient to specify every $x \in K$ with accuracy $\varepsilon$. Then
$$\log_2 \mathcal{N}(K, d, \varepsilon) \le C(K, d, \varepsilon) \le \lceil \log_2 \mathcal{N}(K, d, \varepsilon/2) \rceil.$$

<a id="pdf-681b6f3d947f-p093-b004"></a>
<!-- pdf-source: page=93; block=4; confidence=0.94 -->
**Proof.** _Lower bound._ If $C(K, d, \varepsilon) \le N$, an encoding maps $K$ to bit strings of length $N$, inducing a partition of $K$ into $\le 2^N$ subsets, each of diameter $\le \varepsilon$, hence each coverable by an $\varepsilon$-ball centered in $K$. So $\mathcal{N}(K, d, \varepsilon) \le 2^N$; take logs.

_Upper bound._ If $\log_2 \mathcal{N}(K, d, \varepsilon/2) \le N$ (integer), there is an $(\varepsilon/2)$-net $\mathcal{N}$ with $|\mathcal{N}| \le 2^N$. Assign each $x \in K$ a closest $x_0 \in \mathcal{N}$, specifiable in $N$ bits. If $x, y$ share $x_0$, then $d(x, y) \le d(x, x_0) + d(y, x_0) \le \varepsilon/2 + \varepsilon/2 = \varepsilon$, so accuracy is $\varepsilon$ and $C(K, d, \varepsilon) \le N$. $\square$

<a id="pdf-681b6f3d947f-p093-b005"></a>
<!-- pdf-source: page=93; block=5; confidence=0.90 -->
**4.3.2 Error correcting codes.** Setup: Alice sends Bob a $k$-letter message, e.g. $x := $ "fill the glass".

Footnote 4: $\operatorname{diam}(K) := \sup\{d(x, y) : x, y \in K\}$.

<a id="pdf-681b6f3d947f-p094-b001"></a>
<!-- pdf-source: page=94; block=1; confidence=0.95 -->
Figure 4.3: Encoding points in $K$ as $N$-bit strings induces a partition of $K$ into at most $2^N$ subsets.

<a id="pdf-681b6f3d947f-p094-b002"></a>
<!-- pdf-source: page=94; block=2; confidence=0.95 -->
Motivation for error correcting codes: an adversary may corrupt Alice's message by changing at most r letters. Redundancy is used to protect the channel — Alice encodes her k-letter message into a longer n-letter message (n > k) so Bob can recover it despite up to r errors.

<a id="pdf-681b6f3d947f-p094-b003"></a>
<!-- pdf-source: page=94; block=3; confidence=0.95 -->
**Example 4.3.2 (Repetition code).** Alice repeats her message several times; Bob applies *majority decoding*, choosing for each letter the value occurring most frequently among its received copies. If the message x is repeated 2r+1 times, majority decoding recovers x exactly even when r letters are corrupted. It is inefficient, using

$$n = (2r+1)k \qquad (4.11)$$

letters to encode a k-letter message.

<a id="pdf-681b6f3d947f-p094-b004"></a>
<!-- pdf-source: page=94; block=4; confidence=0.93 -->
**Definition 4.3.3 (Error correcting code).** Fix integers k, n, r. Consider two maps

$$E : \{0,1\}^k \to \{0,1\}^n, \qquad D : \{0,1\}^n \to \{0,1\}^k.$$

(Definition continues on the next page.)

<a id="pdf-681b6f3d947f-p095-b001"></a>
<!-- pdf-source: page=95; block=1; confidence=0.93 -->
**Definition 4.3.3 (continued).** E and D are *encoding* and *decoding* maps that can correct r errors if $D(y)=x$ for every word $x\in\{0,1\}^k$ and every $y\in\{0,1\}^n$ differing from $E(x)$ in at most r bits. E is an *error correcting code*; its image $E(\{0,1\}^k)$ is the *codebook* (often itself called the code); the elements $E(x)$ are *codewords*. Error correction is related to packing numbers of the Hamming cube $(\{0,1\}^n, d_H)$, with $d_H$ the Hamming metric (Definition 4.2.14).

<a id="pdf-681b6f3d947f-p095-b002"></a>
<!-- pdf-source: page=95; block=2; confidence=0.96 -->
**Lemma 4.3.4 (Error correction and packing).** If positive integers k, n, r satisfy

$$\log_2 P(\{0,1\}^n, d_H, 2r) \ge k,$$

then there exists an error correcting code encoding k-bit strings into n-bit strings that can correct r errors.

<a id="pdf-681b6f3d947f-p095-b003"></a>
<!-- pdf-source: page=95; block=3; confidence=0.95 -->
**Proof.** By assumption there is a subset $N\subset\{0,1\}^n$ with $|N|=2^k$ whose closed radius-r balls centered at its points are disjoint. Define E to be an arbitrary one-to-one map $\{0,1\}^k\to N$ and D a nearest-neighbor decoder. If $y$ differs from $E(x)$ in at most r bits, it lies in the closed r-ball at $E(x)$; disjointness makes $y$ strictly closer to $E(x)$ than to any other codeword, so $D(y)=x$. Footnote: $D(y)=x_0$ where $E(x_0)$ is the closest codeword in N to y, ties broken arbitrarily. $\square$

<a id="pdf-681b6f3d947f-p095-b004"></a>
<!-- pdf-source: page=95; block=4; confidence=0.96 -->
**Theorem 4.3.5 (Guarantees for an error correcting code).** If positive integers k, n, r satisfy

$$n \ge k + 2r\log_2\!\left(\frac{en}{2r}\right),$$

then there exists an error correcting code encoding k-bit strings into n-bit strings that can correct r errors.

<a id="pdf-681b6f3d947f-p095-b005"></a>
<!-- pdf-source: page=95; block=5; confidence=0.93 -->
**Proof.** Passing from packing to covering numbers via Lemma 4.2.8, then applying the covering-number bounds from Exercise 4.2.16 (simplified using Exercise 0.0.5),

$$P(\{0,1\}^n, d_H, 2r) \ge N(\{0,1\}^n, d_H, 2r) \ge 2^n\left(\frac{2r}{en}\right)^{2r}.$$

(Continues on the next page.)

<a id="pdf-681b6f3d947f-p096-b001"></a>
<!-- pdf-source: page=96; block=1; confidence=0.94 -->
**Proof (concluded).** By the hypothesis this quantity is bounded below by $2^k$, so applying Lemma 4.3.4 completes the proof. $\square$

<a id="pdf-681b6f3d947f-p096-b002"></a>
<!-- pdf-source: page=96; block=2; confidence=0.92 -->
Informally, r errors can be corrected with information overhead almost linear in r: $n-k \asymp r\log(n/r)$, much smaller than the repetition code (4.11). E.g. correcting two errors in a twelve-letter message can be done with a 30-letter codeword.

<a id="pdf-681b6f3d947f-p096-b003"></a>
<!-- pdf-source: page=96; block=3; confidence=0.94 -->
**Remark 4.3.6 (Rate).** Define the *rate* and *fraction of errors*

$$R := \frac{k}{n}, \qquad \delta := \frac{r}{n}.$$

Theorem 4.3.5 gives error correcting codes with rate as high as $R \ge 1 - f(2\delta)$, where $f(t) = t\log_2(e/t)$.

<a id="pdf-681b6f3d947f-p096-b004"></a>
<!-- pdf-source: page=96; block=4; confidence=0.90 -->
**Exercise 4.3.7 (Optimality).** (a) Prove the converse of Lemma 4.3.4. (b) Deduce a converse to Theorem 4.3.5, concluding that any error correcting code encoding $k$-bit into $n$-bit strings correcting $r$ errors must have rate $R \le 1 - f(\delta)$, where here $f(t) = t\log_2(1/t)$ as before.

<a id="pdf-681b6f3d947f-p096-b005"></a>
<!-- pdf-source: page=96; block=5; confidence=0.93 -->
**4.4 Upper bounds on random sub-gaussian matrices.** Introduces the non-asymptotic theory of random $m\times n$ matrices A with random entries, concerned with distributions of singular values, eigenvalues (for symmetric A), and eigenvectors. Theorem 4.4.5 will give a first (non-sharp, non-general) bound on the operator norm (largest singular value) of a random matrix with independent sub-gaussian entries, later sharpened in Sections 4.6 and 6.5; first, ε-nets are used to compute operator norms.

<a id="pdf-681b6f3d947f-p097-b001"></a>
<!-- pdf-source: page=97; block=1; confidence=0.90 -->
**Section 4.4 — Upper bounds on random sub-gaussian matrices; 4.4.1 Computing the norm on a net.** ε-nets simplify high-dimensional problems, e.g. computing the operator norm of an m×n matrix A, defined (Section 4.1.2) as ∥A∥ = max_{x∈S^{n−1}} ∥Ax∥₂. Claim: it suffices to control ∥Ax∥₂ over an ε-net of the sphere rather than the whole sphere.

<a id="pdf-681b6f3d947f-p097-b002"></a>
<!-- pdf-source: page=97; block=2; confidence=0.95 -->
**Lemma 4.4.1 (Computing the operator norm on a net).** Let A be an m×n matrix and ε ∈ [0,1). For any ε-net N of the sphere S^{n−1},

sup_{x∈N} ∥Ax∥₂ ≤ ∥A∥ ≤ (1/(1−ε)) · sup_{x∈N} ∥Ax∥₂.

<a id="pdf-681b6f3d947f-p097-b003"></a>
<!-- pdf-source: page=97; block=3; confidence=0.95 -->
**Proof.** Lower bound is trivial since N ⊂ S^{n−1}. For the upper bound, fix x ∈ S^{n−1} with ∥A∥ = ∥Ax∥₂ and choose x₀ ∈ N with ∥x − x₀∥₂ ≤ ε. Then ∥Ax − Ax₀∥₂ = ∥A(x − x₀)∥₂ ≤ ∥A∥∥x − x₀∥₂ ≤ ε∥A∥. By triangle inequality, ∥Ax₀∥₂ ≥ ∥Ax∥₂ − ∥Ax − Ax₀∥₂ ≥ ∥A∥ − ε∥A∥ = (1−ε)∥A∥. Divide by 1−ε. ∎

<a id="pdf-681b6f3d947f-p097-b004"></a>
<!-- pdf-source: page=97; block=4; confidence=0.90 -->
**Exercise 4.4.2.** For x ∈ ℝⁿ and N an ε-net of S^{n−1}, show sup_{y∈N} ⟨x,y⟩ ≤ ∥x∥₂ ≤ (1/(1−ε)) · sup_{y∈N} ⟨x,y⟩.

<a id="pdf-681b6f3d947f-p097-b005"></a>
<!-- pdf-source: page=97; block=5; confidence=0.88 -->
Recall (Section 4.1.2) that ∥A∥ = max_{x∈S^{n−1}, y∈S^{m−1}} ⟨Ax,y⟩, and for symmetric matrices one may take x = y. **Exercise 4.4.3 (Quadratic form on a net).** Let A be an m×n matrix and ε ∈ [0,1/2). [Statement continues on next page.]

<a id="pdf-681b6f3d947f-p098-b001"></a>
<!-- pdf-source: page=98; block=1; confidence=0.90 -->
**Exercise 4.4.3 (continued).** (a) For any ε-net N of S^{n−1} and ε-net M of S^{m−1}, sup_{x∈N, y∈M} ⟨Ax,y⟩ ≤ ∥A∥ ≤ (1/(1−2ε)) · sup_{x∈N, y∈M} ⟨Ax,y⟩. (b) If m=n and A is symmetric, sup_{x∈N} |⟨Ax,x⟩| ≤ ∥A∥ ≤ (1/(1−2ε)) · sup_{x∈N} |⟨Ax,x⟩|. Hint: proceed as in Lemma 4.4.1 using the identity ⟨Ax,y⟩ − ⟨Ax₀,y₀⟩ = ⟨Ax, y−y₀⟩ + ⟨A(x−x₀), y₀⟩.

<a id="pdf-681b6f3d947f-p098-b002"></a>
<!-- pdf-source: page=98; block=2; confidence=0.90 -->
**Exercise 4.4.4 (Deviation of the norm on a net).** Let A be m×n, µ ∈ ℝ, ε ∈ [0,1/2). For any ε-net N of S^{n−1}, sup_{x∈S^{n−1}} |∥Ax∥₂ − µ| ≤ (C/(1−2ε)) · sup_{x∈N} |∥Ax∥₂ − µ|. Hint: WLOG µ = 1; write ∥Ax∥₂² − 1 as the quadratic form ⟨Rx,x⟩ with R = AᵀA − Iₙ and apply Exercise 4.4.3.

<a id="pdf-681b6f3d947f-p098-b003"></a>
<!-- pdf-source: page=98; block=3; confidence=0.90 -->
**4.4.2 The norms of sub-gaussian random matrices.** First random-matrix result: an m×n random matrix A with independent sub-gaussian entries satisfies ∥A∥ ≲ √m + √n with high probability.

<a id="pdf-681b6f3d947f-p098-b004"></a>
<!-- pdf-source: page=98; block=4; confidence=0.95 -->
**Theorem 4.4.5 (Norm of matrices with sub-gaussian entries).** Let A be an m×n random matrix whose entries A_{ij} are independent, mean-zero, sub-gaussian random variables. Then for any t > 0,

∥A∥ ≤ CK(√m + √n + t)

with probability at least 1 − 2exp(−t²), where K = max_{i,j} ∥A_{ij}∥_{ψ₂}.

<a id="pdf-681b6f3d947f-p098-b005"></a>
<!-- pdf-source: page=98; block=5; confidence=0.92 -->
**Proof (ε-net argument).** Strategy: discretize the sphere (approximation), control ⟨Ax,y⟩ for fixed net vectors (concentration), then union bound. **Step 1 — Approximation.** Take ε = 1/4. By Corollary 4.2.13, choose an ε-net N of S^{n−1} and ε-net M of S^{m−1} with |N| ≤ 9ⁿ and |M| ≤ 9^m. (4.12)

<a id="pdf-681b6f3d947f-p099-b001"></a>
<!-- pdf-source: page=99; block=1; confidence=0.93 -->
By Exercise 4.4.3, ∥A∥ ≤ 2 max_{x∈N, y∈M} ⟨Ax,y⟩. (4.13)

**Step 2 — Concentration.** Fix x ∈ N, y ∈ M. Then ⟨Ax,y⟩ = Σ_{i=1}^{n} Σ_{j=1}^{m} A_{ij} x_i y_j is a sum of independent sub-gaussian variables. By Proposition 2.6.1 it is sub-gaussian with ∥⟨Ax,y⟩∥²_{ψ₂} ≤ C Σ_i Σ_j ∥A_{ij}x_i y_j∥²_{ψ₂} ≤ CK² Σ_i Σ_j x_i² y_j² = CK² (Σ_i x_i²)(Σ_j y_j²) = CK². By (2.14), the tail bound is

P{⟨Ax,y⟩ ≥ u} ≤ 2exp(−cu²/K²), u ≥ 0. (4.14)

<a id="pdf-681b6f3d947f-p099-b002"></a>
<!-- pdf-source: page=99; block=2; confidence=0.93 -->
**Step 3 — Union bound.** If max_{x∈N, y∈M} ⟨Ax,y⟩ ≥ u then some x,y in the nets achieve it, so

P{max_{x∈N, y∈M} ⟨Ax,y⟩ ≥ u} ≤ Σ_{x∈N, y∈M} P{⟨Ax,y⟩ ≥ u}.

By (4.14) and the cardinality bounds (4.12) this is ≤ 9^{n+m} · 2exp(−cu²/K²). (4.15) Choose u = CK(√n + √m + t). (4.16) Then u² ≥ C²K²(n+m+t²), and for C large enough cu²/K² ≥ 3(n+m) + t², so

P{max ⟨Ax,y⟩ ≥ u} ≤ 9^{n+m} · 2exp(−3(n+m) − t²) ≤ 2exp(−t²).

Combined with (4.13), P{∥A∥ ≥ 2u} ≤ 2exp(−t²); substituting (4.16) completes the proof. ∎

<a id="pdf-681b6f3d947f-p099-b003"></a>
<!-- pdf-source: page=99; block=3; confidence=0.92 -->
**Exercise 4.4.6 (Expected norm).** Deduce from Theorem 4.4.5 that E∥A∥ ≤ CK(√m + √n).

<a id="pdf-681b6f3d947f-p100-b001"></a>
<!-- pdf-source: page=100; block=1; confidence=0.95 -->
**Exercise 4.4.7 (Optimality).** Assuming the entries $A_{ij}$ in Theorem 4.4.5 have unit variances, prove that for sufficiently large $n$ and $m$, $\mathbb{E}\|A\| \ge \tfrac{1}{4}(\sqrt{m}+\sqrt{n})$. Hint: bound $\|A\|$ below by the Euclidean norm of the first column and first row, then use concentration of the norm (Exercise 3.1.4).

<a id="pdf-681b6f3d947f-p100-b002"></a>
<!-- pdf-source: page=100; block=2; confidence=0.95 -->
Theorem 4.4.5 extends to symmetric matrices, giving $\|A\| \lesssim \sqrt{n}$ with high probability.

<a id="pdf-681b6f3d947f-p100-b003"></a>
<!-- pdf-source: page=100; block=3; confidence=0.98 -->
**Corollary 4.4.8 (Norm of symmetric matrices with sub-gaussian entries).** Let $A$ be an $n\times n$ symmetric random matrix whose entries $A_{ij}$ on and above the diagonal are independent, mean-zero, sub-gaussian. Then for any $t>0$, $\|A\| \le CK(\sqrt{n}+t)$ with probability at least $1-4\exp(-t^2)$, where $K=\max_{i,j}\|A_{ij}\|_{\psi_2}$.

<a id="pdf-681b6f3d947f-p100-b004"></a>
<!-- pdf-source: page=100; block=4; confidence=0.97 -->
**Proof.** Decompose $A=A_+ + A_-$ into upper-triangular part $A_+$ (including the diagonal) and lower-triangular part $A_-$. Theorem 4.4.5 applies to each part separately; by a union bound, $\|A_+\|\le CK(\sqrt{n}+t)$ and $\|A_-\|\le CK(\sqrt{n}+t)$ simultaneously with probability at least $1-4\exp(-t^2)$. The triangle inequality $\|A\|\le\|A_+\|+\|A_-\|$ finishes the proof. $\square$

<a id="pdf-681b6f3d947f-p100-b005"></a>
<!-- pdf-source: page=100; block=5; confidence=0.93 -->
**4.5 Application: community detection in networks.** Random matrix theory is applied to network analysis: real-world networks have communities (clusters of tightly connected vertices), and the community detection problem is to find them accurately and efficiently.

<a id="pdf-681b6f3d947f-p100-b006"></a>
<!-- pdf-source: page=100; block=6; confidence=0.92 -->
**4.5.1 Stochastic Block Model.** A basic probabilistic model of a two-community network, extending the Erdős–Rényi random graph model (Section 2.4).

<a id="pdf-681b6f3d947f-p101-b001"></a>
<!-- pdf-source: page=101; block=1; confidence=0.97 -->
**Definition 4.5.1 (Stochastic block model).** Partition $n$ vertices into two communities of size $n/2$ each. Form a random graph $G$ by connecting each pair of vertices independently with probability $p$ if in the same community and $q$ if in different communities. This distribution is denoted $G(n,p,q)$.

<a id="pdf-681b6f3d947f-p101-b002"></a>
<!-- pdf-source: page=101; block=2; confidence=0.93 -->
If $p=q$ this reduces to the Erdős–Rényi model $G(n,p)$; assume $p>q$, so edges are more likely within communities, giving a community structure (Figure 4.4: $n=200$, $p=1/20$, $q=1/200$).

<a id="pdf-681b6f3d947f-p101-b003"></a>
<!-- pdf-source: page=101; block=3; confidence=0.90 -->
**4.5.2 Expected adjacency matrix.** Identify $G$ with its adjacency matrix $A$ (Definition 3.6.2). For $G\sim G(n,p,q)$, $A$ is a random matrix.

<a id="pdf-681b6f3d947f-p101-b004"></a>
<!-- pdf-source: page=101; block=4; confidence=0.92 -->
Split $A=D+R$ where $D=\mathbb{E}A$ is the deterministic "signal" and $R$ is the "noise". Entries $A_{ij}$ are Bernoulli, $\mathrm{Ber}(p)$ or $\mathrm{Ber}(q)$ per community membership, so entries of $D$ equal $p$ or $q$ accordingly. $D$ is computed to reveal community structure via its eigenstructure.

<a id="pdf-681b6f3d947f-p102-b001"></a>
<!-- pdf-source: page=102; block=1; confidence=0.90 -->
Grouping same-community vertices together, for $n=4$ the matrix $D=\mathbb{E}A$ is the $4\times4$ block matrix with $p$ in the two diagonal $2\times2$ blocks and $q$ in the off-diagonal blocks: $\begin{pmatrix}p&p&q&q\\p&p&q&q\\q&q&p&p\\q&q&p&p\end{pmatrix}$.

<a id="pdf-681b6f3d947f-p102-b002"></a>
<!-- pdf-source: page=102; block=2; confidence=0.95 -->
**Exercise 4.5.2.** Show $D$ has rank $2$ with non-zero eigenvalues and eigenvectors (4.17): $\lambda_1=\big(\tfrac{p+q}{2}\big)n$ with $u_1=(1,\dots,1)^\top$ (all ones), and $\lambda_2=\big(\tfrac{p-q}{2}\big)n$ with $u_2=(1,\dots,1,-1,\dots,-1)^\top$ ($+1$ on the first community, $-1$ on the second).

<a id="pdf-681b6f3d947f-p102-b003"></a>
<!-- pdf-source: page=102; block=3; confidence=0.93 -->
The second eigenvector $u_2$ encodes the community structure: knowing $u_2$ identifies communities from the signs/sizes of its coefficients. Since $D=\mathbb{E}A$ is unknown, only the noisy $A=D+R$ is available. Signal level $\|D\|=\lambda_1\asymp n$; by Corollary 4.4.8 the noise satisfies (4.18) $\|R\|\le C\sqrt{n}$ with probability at least $1-4e^{-n}$. Thus for large $n$, $R\ll D$, so $A\approx D$ and $A$ can substitute for $D$, justified by perturbation theory.

<a id="pdf-681b6f3d947f-p102-b004"></a>
<!-- pdf-source: page=102; block=4; confidence=0.92 -->
**4.5.3 Perturbation theory.** Describes how eigenvalues and eigenvectors change under matrix perturbations.

<a id="pdf-681b6f3d947f-p102-b005"></a>
<!-- pdf-source: page=102; block=5; confidence=0.97 -->
**Theorem 4.5.3 (Weyl's inequality).** For any symmetric matrices $S$ and $T$ of the same dimensions, $\max_i |\lambda_i(S)-\lambda_i(T)| \le \|S-T\|$. Hence the operator norm controls stability of the spectrum.

<a id="pdf-681b6f3d947f-p102-b006"></a>
<!-- pdf-source: page=102; block=6; confidence=0.95 -->
**Exercise 4.5.4.** Deduce Weyl's inequality from the Courant–Fischer min-max characterization of eigenvalues (4.2).

<a id="pdf-681b6f3d947f-p103-b001"></a>
<!-- pdf-source: page=103; block=1; confidence=0.95 -->
Eigenvector analogues of eigenvalue perturbation bounds require tracking the same eigenvector before and after perturbation; if λ_i(S) and λ_{i+1}(S) are too close the perturbation may swap their order. Remedy: assume the eigenvalues of S are well separated.

<a id="pdf-681b6f3d947f-p103-b002"></a>
<!-- pdf-source: page=103; block=2; confidence=0.95 -->
**Theorem 4.5.5 (Davis–Kahan).** Let S, T be symmetric matrices of the same dimension. Fix i and assume the i-th largest eigenvalue of S is well separated: min_{j≠i} |λ_i(S) − λ_j(S)| = δ > 0. Then the angle (in [0, π/2]) between the eigenvectors of S and T for the i-th largest eigenvalues satisfies

sin ∠(v_i(S), v_i(T)) ≤ 2‖S − T‖ / δ.

Stated without proof.

<a id="pdf-681b6f3d947f-p103-b003"></a>
<!-- pdf-source: page=103; block=3; confidence=0.90 -->
Consequence of Davis–Kahan: the unit eigenvectors are close up to a sign, i.e. ∃ θ ∈ {−1, 1} with

‖v_i(S) − θ v_i(T)‖₂ ≤ 2^{3/2} ‖S − T‖ / δ.   (4.19)

(Left as a check.)

<a id="pdf-681b6f3d947f-p103-b004"></a>
<!-- pdf-source: page=103; block=4; confidence=0.98 -->
## 4.5.4 Spectral Clustering

<a id="pdf-681b6f3d947f-p103-b005"></a>
<!-- pdf-source: page=103; block=5; confidence=0.92 -->
**Derivation.** Apply Davis–Kahan with S = D, T = A = D + R for the second largest eigenvalue. λ_2 must be separated from 0 and λ_1; the separation is

δ = min(λ_2, λ_1 − λ_2) = min((p−q)/2, q)·n =: μn.

Using bound (4.18) on R = T − S and (4.19), there is a sign θ ∈ {−1, 1} with

‖v_2(D) − θ v_2(A)‖₂ ≤ C√n / (μn) = C / (μ√n),

with probability ≥ 1 − 4e^{−n}. The eigenvectors u_i(D) from (4.17) have norm √n; multiplying both sides by √n gives, in that normalization,

‖u_2(D) − θ u_2(A)‖₂ ≤ C/μ.

<a id="pdf-681b6f3d947f-p104-b001"></a>
<!-- pdf-source: page=104; block=1; confidence=0.90 -->
**Derivation (cont.).** Most coefficient signs of θ v_2(A) and v_2(D) agree. From the previous bound,

Σ_{j=1}^n |u_2(D)_j − θ u_2(A)_j|² ≤ C/μ².   (4.20)

By (4.17) the coefficients u_2(D)_j are all ±1, so each coordinate j where the signs of θ v_2(A)_j and v_2(D)_j disagree contributes ≥ 1 to the sum. Hence the number of disagreeing signs is ≤ C/μ².

<a id="pdf-681b6f3d947f-p104-b002"></a>
<!-- pdf-source: page=104; block=2; confidence=0.95 -->
Thus v_2(A) accurately estimates v_2 = v_2(D) of (4.17), whose signs identify the two communities; this method is called spectral clustering.

<a id="pdf-681b6f3d947f-p104-b003"></a>
<!-- pdf-source: page=104; block=3; confidence=0.95 -->
**Spectral Clustering Algorithm.** Input: graph G. Output: partition of vertices into two communities.
1. Compute the adjacency matrix A of G.
2. Compute the eigenvector v_2(A) for the second largest eigenvalue of A.
3. Partition vertices by the signs of the coefficients of v_2(A) (if v_2(A)_j > 0, vertex j into first community, otherwise second).

<a id="pdf-681b6f3d947f-p104-b004"></a>
<!-- pdf-source: page=104; block=4; confidence=0.95 -->
**Theorem 4.5.6 (Spectral clustering for the stochastic block model).** Let G ∼ G(n, p, q) with p > q and min(q, p − q) = μ > 0. Then with probability ≥ 1 − 4e^{−n} the spectral clustering algorithm identifies the communities of G correctly up to C/μ² misclassified vertices.

<a id="pdf-681b6f3d947f-p104-b005"></a>
<!-- pdf-source: page=104; block=5; confidence=0.95 -->
Spectral clustering correctly classifies all but a constant number of vertices, provided the graph is dense enough (q ≥ const) and within-/across-community probabilities are well separated (p − q ≥ const).

<a id="pdf-681b6f3d947f-p104-b006"></a>
<!-- pdf-source: page=104; block=6; confidence=0.98 -->
# 4.6 Two-sided bounds on sub-gaussian matrices

<a id="pdf-681b6f3d947f-p104-b007"></a>
<!-- pdf-source: page=104; block=7; confidence=0.95 -->
Recall Theorem 4.4.5: for an m × n matrix A with independent sub-gaussian entries, s_1(A) ≤ C(√m + √n) with high probability. This result will be improved in two ways.

<a id="pdf-681b6f3d947f-p105-b001"></a>
<!-- pdf-source: page=105; block=1; confidence=0.95 -->
Two improvements: (1) sharper two-sided bounds on the whole spectrum, √m − C√n ≤ s_i(A) ≤ √m + C√n, showing a tall matrix (m ≫ n) is an approximate isometry; (2) relaxing independence of entries to independence of rows, so the rows of A are sub-gaussian random vectors (relevant when rows are independent high-dimensional samples but columns/coordinates are not).

<a id="pdf-681b6f3d947f-p105-b002"></a>
<!-- pdf-source: page=105; block=2; confidence=0.92 -->
**Theorem 4.6.1 (Two-sided bound on sub-gaussian matrices).** Let A be an m × n matrix whose rows A_i are independent, mean-zero, sub-gaussian isotropic random vectors in ℝⁿ. Then for any t ≥ 0,

√m − CK²(√n + t) ≤ s_n(A) ≤ s_1(A) ≤ √m + CK²(√n + t)   (4.21)

with probability ≥ 1 − 2exp(−t²), where K = max_i ‖A_i‖_{ψ₂}. A stronger conclusion is proved:

‖(1/m) AᵀA − I_n‖ ≤ K² max(δ, δ²),  where δ = C(√(n/m) + t/√m).   (4.22)

By Lemma 4.1.5, (4.22) implies (4.21).

<a id="pdf-681b6f3d947f-p105-b003"></a>
<!-- pdf-source: page=105; block=3; confidence=0.90 -->
**Proof.** Prove (4.22) by an ε-net argument (as in Theorem 4.4.5, but using Bernstein's inequality instead of Hoeffding's).

**Step 1: Approximation.** By Corollary 4.2.13, take a (1/4)-net N of the unit sphere S^{n−1} with |N| ≤ 9ⁿ. By Exercise 4.4.3,

‖(1/m) AᵀA − I_n‖ ≤ 2 max_{x∈N} |⟨((1/m)AᵀA − I_n) x, x⟩| = 2 max_{x∈N} |(1/m)‖Ax‖₂² − 1|.

So it suffices to show, with the required probability,

max_{x∈N} |(1/m)‖Ax‖₂² − 1| ≤ ε/2,  where ε := K² max(δ, δ²).

<a id="pdf-681b6f3d947f-p106-b001"></a>
<!-- pdf-source: page=106; block=1; confidence=0.94 -->
**Step 2 (Concentration).** Fix $x\in S^{n-1}$ and write $\|Ax\|_2^2=\sum_{i=1}^m\langle A_i,x\rangle^2=\sum_{i=1}^m X_i^2$ (4.23), where $A_i$ are the rows of $A$. The $A_i$ are independent, isotropic, sub-gaussian with $\|A_i\|_{\psi_2}\le K$, so $X_i=\langle A_i,x\rangle$ are independent sub-gaussian with $\mathbb{E}X_i^2=1$, $\|X_i\|_{\psi_2}\le K$; hence $X_i^2-1$ are independent, mean-zero, sub-exponential with $\|X_i^2-1\|_{\psi_1}\le CK^2$. Bernstein's inequality (Corollary 2.8.3) gives $\mathbb{P}\{|\tfrac1m\|Ax\|_2^2-1|\ge\varepsilon/2\}\le 2\exp[-c_1\min(\varepsilon^2/K^4,\varepsilon/K^2)m]=2\exp[-c_1\delta^2 m]\le 2\exp[-c_1 C^2(n+t^2)]$, using $\varepsilon/K^2=\max(\delta,\delta^2)$, the definition of $\delta$ in (4.22), and $(a+b)^2\ge a^2+b^2$ for $a,b\ge0$.

<a id="pdf-681b6f3d947f-p106-b002"></a>
<!-- pdf-source: page=106; block=2; confidence=0.95 -->
**Step 3 (Union bound).** Unfix $x$ over the net $N$, whose cardinality is $\le 9^n$: $\mathbb{P}\{\max_{x\in N}|\tfrac1m\|Ax\|_2^2-1|\ge\varepsilon/2\}\le 9^n\cdot 2\exp[-c_1 C^2(n+t^2)]\le 2\exp(-t^2)$, provided the absolute constant $C$ in (4.22) is large enough. By Step 1 this completes the proof of the theorem.

<a id="pdf-681b6f3d947f-p106-b003"></a>
<!-- pdf-source: page=106; block=3; confidence=0.95 -->
**Exercise 4.6.2.** Deduce from (4.22) that $\mathbb{E}\,\big\|\tfrac1m A^{\mathsf T}A-I_n\big\|\le CK^2\big(\sqrt{n/m}+n/m\big)$. Hint: use the integral identity from Lemma 1.2.1.

<a id="pdf-681b6f3d947f-p106-b004"></a>
<!-- pdf-source: page=106; block=4; confidence=0.95 -->
**Exercise 4.6.3.** Deduce from Theorem 4.6.1 the expectation bounds $\sqrt{m}-CK^2\sqrt{n}\le \mathbb{E}\,s_n(A)\le \mathbb{E}\,s_1(A)\le \sqrt{m}+CK^2\sqrt{n}$.

<a id="pdf-681b6f3d947f-p106-b005"></a>
<!-- pdf-source: page=106; block=5; confidence=0.95 -->
**Exercise 4.6.4.** Give a simpler proof of Theorem 4.6.1 using Theorem 3.1.1 for a concentration bound on $\|Ax\|_2$ and Exercise 4.4.4 to reduce to a union bound over a net.

<a id="pdf-681b6f3d947f-p107-b001"></a>
<!-- pdf-source: page=107; block=1; confidence=0.98 -->
## 4.7 Application: covariance estimation and clustering

<a id="pdf-681b6f3d947f-p107-b002"></a>
<!-- pdf-source: page=107; block=2; confidence=0.92 -->
Motivation: estimate the covariance matrix of an unknown distribution in $\mathbb{R}^n$ from samples $X_1,\dots,X_m$ so that (via the Davis–Kahan theorem 4.5.5 and PCA) principal components can be recovered. Let $X$ have zero mean with covariance $\Sigma=\mathbb{E}\,XX^{\mathsf T}$ (the second moment matrix in general). The sample covariance matrix is $\Sigma_m=\tfrac1m\sum_{i=1}^m X_iX_i^{\mathsf T}$. It is unbiased, $\mathbb{E}\,\Sigma_m=\Sigma$, and by the law of large numbers (Theorem 1.3.1) $\Sigma_m\to\Sigma$ almost surely as $m\to\infty$. Question: how large must $m$ be for $\Sigma_m\approx\Sigma$ with high probability? At least $m\gtrsim n$ is needed, and $m\asymp n$ suffices.

<a id="pdf-681b6f3d947f-p107-b003"></a>
<!-- pdf-source: page=107; block=3; confidence=0.93 -->
**Theorem 4.7.1 (Covariance estimation).** Let $X$ be a sub-gaussian random vector in $\mathbb{R}^n$: there exists $K\ge 1$ such that $\|\langle X,x\rangle\|_{\psi_2}\le K\|\langle X,x\rangle\|_{L^2}$ for all $x\in\mathbb{R}^n$ (4.24). (Here $\|\langle X,x\rangle\|_{L^2}^2=\mathbb{E}\langle X,x\rangle^2=\langle\Sigma x,x\rangle$.)

<a id="pdf-681b6f3d947f-p108-b001"></a>
<!-- pdf-source: page=108; block=1; confidence=0.95 -->
**Theorem 4.7.1 (continued).** Then for every positive integer $m$, $\mathbb{E}\,\|\Sigma_m-\Sigma\|\le CK^2\big(\sqrt{n/m}+n/m\big)\,\|\Sigma\|$.

<a id="pdf-681b6f3d947f-p108-b002"></a>
<!-- pdf-source: page=108; block=2; confidence=0.94 -->
**Proof.** Reduce to isotropic position (assuming $\Sigma$ invertible): there exist independent isotropic $Z,Z_1,\dots,Z_m$ with $X=\Sigma^{1/2}Z$, $X_i=\Sigma^{1/2}Z_i$ (Exercise 3.2.2), and (4.24) gives $\|Z\|_{\psi_2}\le K$, $\|Z_i\|_{\psi_2}\le K$. Then $\|\Sigma_m-\Sigma\|=\|\Sigma^{1/2}R_m\Sigma^{1/2}\|\le\|R_m\|\,\|\Sigma\|$ where $R_m:=\tfrac1m\sum_{i=1}^m Z_iZ_i^{\mathsf T}-I_n$ (4.25). Forming the $m\times n$ matrix $A$ with rows $Z_i^{\mathsf T}$ gives $\tfrac1m A^{\mathsf T}A-I_n=R_m$; applying Theorem 4.6.1 (via Exercise 4.6.2) yields $\mathbb{E}\,\|R_m\|\le CK^2(\sqrt{n/m}+n/m)$. Substituting into (4.25) completes the proof.

<a id="pdf-681b6f3d947f-p108-b003"></a>
<!-- pdf-source: page=108; block=3; confidence=0.94 -->
**Remark 4.7.2 (Sample complexity).** For any $\varepsilon\in(0,1)$, the bound $\mathbb{E}\,\|\Sigma_m-\Sigma\|\le\varepsilon\|\Sigma\|$ (good relative error) holds once $m\asymp\varepsilon^{-2}n$; i.e. accurate estimation requires sample size proportional to the dimension.

<a id="pdf-681b6f3d947f-p108-b004"></a>
<!-- pdf-source: page=108; block=4; confidence=0.95 -->
**Exercise 4.7.3 (Tail bound).** Check that for any $u\ge 0$, $\|\Sigma_m-\Sigma\|\le CK^2\big(\sqrt{(n+u)/m}+(n+u)/m\big)\|\Sigma\|$ with probability at least $1-2e^{-u}$.

<a id="pdf-681b6f3d947f-p109-b001"></a>
<!-- pdf-source: page=109; block=1; confidence=0.98 -->
## 4.7.1 Application: clustering of point sets

<a id="pdf-681b6f3d947f-p109-b002"></a>
<!-- pdf-source: page=109; block=2; confidence=0.90 -->
Motivation: partition a point set in $\mathbb{R}^n$ into a few clusters, where points within a cluster tend to be closer to each other than to points in other clusters. A probabilistic two-community model of point sets is introduced to study the clustering problem, illustrating Theorem 4.7.1.

<a id="pdf-681b6f3d947f-p109-b003"></a>
<!-- pdf-source: page=109; block=3; confidence=0.97 -->
**Definition 4.7.4 (Gaussian mixture model).** Generate $m$ random points in $\mathbb{R}^n$: flip a fair coin; on heads draw from $N(\mu, I_n)$, on tails from $N(-\mu, I_n)$. Equivalently, take the random vector $X = \theta\mu + g$, where $\theta$ is a symmetric Bernoulli random variable, $g \sim N(0, I_n)$, and $\theta, g$ are independent. A sample $X_1,\dots,X_m$ of i.i.d. copies of $X$ is distributed according to this Gaussian mixture model with means $\mu$ and $-\mu$.

<a id="pdf-681b6f3d947f-p109-b004"></a>
<!-- pdf-source: page=109; block=4; confidence=0.90 -->
Given a sample from the Gaussian mixture model, the goal is to label each point's cluster via a spectral clustering variant. Since the distribution of $X$ is not isotropic but stretched along $\mu$, $\mu$ is approximated by the first principal component of the data; projecting points onto the line spanned by $\mu$ and reading off the sign classifies them. (Figure 4.5: simulation of the two-cluster mixture.)

<a id="pdf-681b6f3d947f-p110-b001"></a>
<!-- pdf-source: page=110; block=1; confidence=0.96 -->
**Spectral Clustering Algorithm.** Input: points $X_1,\dots,X_m \in \mathbb{R}^n$. Output: partition into two clusters.
1. Compute the sample covariance matrix $\Sigma_m = \frac{1}{m}\sum_{i=1}^m X_i X_i^{\mathsf T}$.
2. Compute the eigenvector $v = v_1(\Sigma_m)$ corresponding to the largest eigenvalue of $\Sigma_m$.
3. Partition by the sign of $\langle v, X_i\rangle$: if $\langle v, X_i\rangle > 0$ assign $X_i$ to the first community, otherwise to the second.

<a id="pdf-681b6f3d947f-p110-b002"></a>
<!-- pdf-source: page=110; block=2; confidence=0.95 -->
**Theorem 4.7.5 (Guarantees of spectral clustering of the Gaussian mixture model).** Let $X_1,\dots,X_m \in \mathbb{R}^n$ be drawn from the Gaussian mixture model with two communities of means $\mu$ and $-\mu$. Let $\varepsilon > 0$ satisfy $\|\mu\|_2 \ge C\sqrt{\log(1/\varepsilon)}$. If the sample size satisfies $m \ge \left(\dfrac{n}{\|\mu\|_2}\right)^{c}$ for an appropriate absolute constant $c>0$, then with probability at least $1 - 4e^{-n}$ the Spectral Clustering Algorithm identifies the communities correctly up to $\varepsilon m$ misclassified points.

<a id="pdf-681b6f3d947f-p110-b003"></a>
<!-- pdf-source: page=110; block=3; confidence=0.93 -->
**Exercise 4.7.6 (Spectral clustering of the Gaussian mixture model).** Prove Theorem 4.7.5 via: (a) compute the covariance matrix $\Sigma$ of $X$ and note its top eigenvector is parallel to $\mu$; (b) use covariance estimation results to show $\Sigma_m$ is close to $\Sigma$ for large $m$; (c) apply the Davis–Kahan Theorem 4.5.5 to deduce $v = v_1(\Sigma_m)$ is close to the direction of $\mu$; (d) conclude the signs of $\langle \mu, X_i\rangle$ predict the community well; (e) since $v \approx \mu$, conclude the same for $v$.

<a id="pdf-681b6f3d947f-p110-b004"></a>
<!-- pdf-source: page=110; block=4; confidence=0.98 -->
## 4.8 Notes

<a id="pdf-681b6f3d947f-p110-b005"></a>
<!-- pdf-source: page=110; block=5; confidence=0.90 -->
Covering/packing numbers and metric entropy (Section 4.2) are studied in asymptotic geometric analysis; sources [11, Ch. 4], [168]. Section 4.3.2 gives basic error-correcting-code results; [216] is a fuller coding-theory reference. Theorem 4.3.5 is a simplified version of the Gilbert–Varshamov bound on the rate of error correcting codes.

<a id="pdf-681b6f3d947f-p111-b001"></a>
<!-- pdf-source: page=111; block=1; confidence=0.95 -->
The proof of Theorem 4.3.5 uses a binomial-sum bound (Exercise 0.0.5). Tightening it gives the Gilbert–Varshamov bound: there exist codes with rate $R \ge 1 - h(2\delta) - o(1)$, where $h(x) = -x\log_2 x + (1-x)\log_2(1-x)$ is the binary entropy function. Similarly tightening Exercise 4.3.7 gives, for any error correcting code, the Hamming bound $R \le 1 - h(\delta)$.

<a id="pdf-681b6f3d947f-p111-b002"></a>
<!-- pdf-source: page=111; block=2; confidence=0.90 -->
Non-asymptotic random matrix theory (Sections 4.4, 4.6) follows [222]. Section 4.5 applies it to networks; see [158] for network analysis. Stochastic block models (Definition 4.5.1) introduced in [103]; community detection references [158, 77, 141, 230, 157, 96, 1, 27, 55, 128, 94, 108]. Davis–Kahan's Theorem 4.5.5 originally in [60], with extensions and alternative proofs in [226, 229, 225], [21, Sec. VII.3], [188, Ch. V].

<a id="pdf-681b6f3d947f-p111-b003"></a>
<!-- pdf-source: page=111; block=3; confidence=0.90 -->
Covariance estimation (Section 4.7) follows [222], with more general results in Section 9.2.3; further references [222, 174, 119, 43, 131, 53]. Clustering of Gaussian mixture models (Section 4.7.1) is studied in statistics and CS; see [153, Ch. 6] and [112, 154, 19, 104, 10, 89].

<a id="pdf-681b6f3d947f-p112-b001"></a>
<!-- pdf-source: page=112; block=1; confidence=0.95 -->
**Chapter 5. Concentration without independence.** Introduces approaches to concentration not based on independence: deriving concentration from isoperimetric inequalities (§5.1, sphere; §5.2, other settings), the Johnson–Lindenstrauss Lemma via sphere concentration (§5.3), and matrix concentration (§5.4) including matrix Bernstein's inequality (extending §2.8), with applications to community detection and covariance estimation (§5.5–5.6).

<a id="pdf-681b6f3d947f-p112-b002"></a>
<!-- pdf-source: page=112; block=2; confidence=0.94 -->
**§5.1 Concentration of Lipschitz functions on the sphere.** Poses the question: for $X\sim N(0,I_n)$ and $f:\mathbb{R}^n\to\mathbb{R}$, when does $f(X)\approx \mathbb{E}f(X)$ with high probability? Easy for linear $f$ (then $f(X)$ is normal, cf. Exercise 3.3.3, Proposition 2.1.2). Arbitrary $f$ cannot concentrate, but non-wildly-oscillating $f$ may; the Lipschitz condition rules out wild oscillation.

<a id="pdf-681b6f3d947f-p113-b001"></a>
<!-- pdf-source: page=113; block=1; confidence=0.97 -->
**Definition 5.1.1 (Lipschitz functions).** For metric spaces $(X,d_X)$, $(Y,d_Y)$, a map $f:X\to Y$ is Lipschitz if there exists $L\in\mathbb{R}$ with $d_Y(f(u),f(v))\le L\,d_X(u,v)$ for all $u,v\in X$. The infimum of such $L$ is the Lipschitz norm $\|f\|_{\mathrm{Lip}}$.

<a id="pdf-681b6f3d947f-p113-b002"></a>
<!-- pdf-source: page=113; block=2; confidence=0.95 -->
Functions with $\|f\|_{\mathrm{Lip}}\le 1$ are called contractions. Lipschitz functions form an intermediate class between uniformly continuous and differentiable functions.

<a id="pdf-681b6f3d947f-p113-b003"></a>
<!-- pdf-source: page=113; block=3; confidence=0.96 -->
**Exercise 5.1.2.** Prove: (a) every Lipschitz function is uniformly continuous; (b) every differentiable $f:\mathbb{R}^n\to\mathbb{R}$ is Lipschitz with $\|f\|_{\mathrm{Lip}}\le \sup_{x\in\mathbb{R}^n}\|\nabla f(x)\|_2$; (c) give a non-Lipschitz but uniformly continuous $f:[-1,1]\to\mathbb{R}$; (d) give a non-differentiable but Lipschitz $f:[-1,1]\to\mathbb{R}$.

<a id="pdf-681b6f3d947f-p113-b004"></a>
<!-- pdf-source: page=113; block=4; confidence=0.96 -->
**Exercise 5.1.3.** Prove: (a) for fixed $\theta\in\mathbb{R}^n$, $f(x)=\langle x,\theta\rangle$ is Lipschitz on $\mathbb{R}^n$ with $\|f\|_{\mathrm{Lip}}=\|\theta\|_2$; (b) an $m\times n$ matrix $A:(\mathbb{R}^n,\|\cdot\|_2)\to(\mathbb{R}^m,\|\cdot\|_2)$ is Lipschitz with $\|A\|_{\mathrm{Lip}}=\|A\|$; (c) any norm $f(x)=\|x\|$ on $(\mathbb{R}^n,\|\cdot\|_2)$ is Lipschitz, with $\|f\|_{\mathrm{Lip}}$ the smallest $L$ satisfying $\|x\|\le L\|x\|_2$ for all $x$.

<a id="pdf-681b6f3d947f-p114-b001"></a>
<!-- pdf-source: page=114; block=1; confidence=0.95 -->
**Theorem 5.1.4 (Concentration of Lipschitz functions on the sphere).** Let $X\sim\mathrm{Unif}(\sqrt{n}\,S^{n-1})$ (uniform on the Euclidean sphere of radius $\sqrt{n}$) and $f:\sqrt{n}\,S^{n-1}\to\mathbb{R}$ Lipschitz. Then $\|f(X)-\mathbb{E}f(X)\|_{\psi_2}\le C\|f\|_{\mathrm{Lip}}$. Equivalently, for every $t\ge 0$, $\ \mathbb{P}\{|f(X)-\mathbb{E}f(X)|\ge t\}\le 2\exp(-ct^2/\|f\|_{\mathrm{Lip}}^2)$.

<a id="pdf-681b6f3d947f-p114-b002"></a>
<!-- pdf-source: page=114; block=2; confidence=0.93 -->
**§5.1.2 Concentration via isoperimetric inequalities.** Proof strategy: the linear case holds since $X\sim\mathrm{Unif}(\sqrt{n}\,S^{n-1})$ is sub-gaussian (Theorem 3.4.6). For general non-linear Lipschitz $f$, argue it concentrates at least as strongly as a linear function by comparing areas of sub-level sets $\{x:f(x)\le a\}$ — spherical caps for linear $f$ — using an isoperimetric inequality.

<a id="pdf-681b6f3d947f-p114-b003"></a>
<!-- pdf-source: page=114; block=3; confidence=0.96 -->
**Theorem 5.1.5 (Isoperimetric inequality on $\mathbb{R}^n$).** Among all subsets $A\subset\mathbb{R}^n$ of given volume, Euclidean balls have minimal area. Moreover, for any $\varepsilon>0$, Euclidean balls minimize the volume of the $\varepsilon$-neighborhood $A_\varepsilon:=\{x\in\mathbb{R}^n:\exists y\in A,\ \|x-y\|_2\le\varepsilon\}=A+\varepsilon B_2^n$. Letting $\varepsilon\to0$, the "moreover" part implies the first.

<a id="pdf-681b6f3d947f-p114-b004"></a>
<!-- pdf-source: page=114; block=4; confidence=0.93 -->
An analogous isoperimetric inequality holds on $S^{n-1}$, with minimizers being spherical caps (neighborhoods of a single point). Let $\sigma_{n-1}$ denote the normalized ($(n-1)$-dimensional Lebesgue) area on $S^{n-1}$. A closed spherical cap centered at $a\in S^{n-1}$ of radius $\varepsilon$ is $C(a,\varepsilon)=\{x\in S^{n-1}:\|x-a\|_2\le\varepsilon\}$. (Theorem 5.1.4 holds for both geodesic and Euclidean metrics; proved for Euclidean, extended in Exercise 5.1.11.)

<a id="pdf-681b6f3d947f-p115-b001"></a>
<!-- pdf-source: page=115; block=1; confidence=0.95 -->
**Section 5.1.** Concentration of Lipschitz functions on the sphere. Figure 5.1: the isoperimetric inequality in ℝⁿ states that among sets A of given volume, Euclidean balls minimize the volume of the ε-neighborhood Aε.

<a id="pdf-681b6f3d947f-p115-b002"></a>
<!-- pdf-source: page=115; block=2; confidence=0.97 -->
**Theorem 5.1.6 (Isoperimetric inequality on the sphere).** For ε > 0, among all sets A ⊂ Sⁿ⁻¹ with given area σ_{n−1}(A), spherical caps minimize the area σ_{n−1}(Aε) of the neighborhood, where Aε := {x ∈ Sⁿ⁻¹ : ∃ y ∈ A with ‖x − y‖₂ ≤ ε}.

<a id="pdf-681b6f3d947f-p115-b003"></a>
<!-- pdf-source: page=115; block=3; confidence=0.95 -->
Isoperimetric inequalities (Theorems 5.1.5 and 5.1.6) are stated without proof; bibliography notes reference known proofs.

<a id="pdf-681b6f3d947f-p115-b004"></a>
<!-- pdf-source: page=115; block=4; confidence=0.92 -->
**Section 5.1.3.** Blow-up of sets on the sphere. Heuristic: if A covers at least half the sphere by area, then Aε covers most of the sphere. For convenience the work uses the sphere of radius √n rather than the unit sphere (cf. Theorem 5.1.4).

<a id="pdf-681b6f3d947f-p115-b005"></a>
<!-- pdf-source: page=115; block=5; confidence=0.96 -->
**Lemma 5.1.7 (Blow-up).** Let A ⊂ √n Sⁿ⁻¹, and let σ be the normalized area on that sphere. If σ(A) ≥ 1/2, then for every t ≥ 0, σ(At) ≥ 1 − 2·exp(−ct²). Here At := {x ∈ √n Sⁿ⁻¹ : ∃ y ∈ A with ‖x − y‖₂ ≤ t}.

<a id="pdf-681b6f3d947f-p115-b006"></a>
<!-- pdf-source: page=115; block=6; confidence=0.94 -->
**Proof.** Define the hemisphere H := {x ∈ √n Sⁿ⁻¹ : x₁ ≤ 0}. Since σ(A) ≥ 1/2 = σ(H), the isoperimetric inequality (Theorem 5.1.6) gives σ(At) ≥ σ(Ht). (5.1) The neighborhood Ht is a spherical cap. (Continued on next page.)

<a id="pdf-681b6f3d947f-p116-b001"></a>
<!-- pdf-source: page=116; block=1; confidence=0.94 -->
**Proof (continued).** Rather than computing the cap area directly, use Theorem 3.4.6: a random vector X ∼ Unif(√n Sⁿ⁻¹) is sub-gaussian with ‖X‖_{ψ₂} ≤ C. Since σ is the uniform probability measure, σ(Ht) = P{X ∈ Ht}. The neighborhood satisfies Ht ⊃ {x ∈ √n Sⁿ⁻¹ : x₁ ≤ t/√2}. (5.2) Hence σ(Ht) ≥ P{X₁ ≤ t/√2} ≥ 1 − 2·exp(−ct²), using ‖X₁‖_{ψ₂} ≤ ‖X‖_{ψ₂} ≤ C. Combined with (5.1), the lemma follows. ∎

<a id="pdf-681b6f3d947f-p116-b002"></a>
<!-- pdf-source: page=116; block=2; confidence=0.96 -->
**Exercise 5.1.8.** Prove inclusion (5.2).

<a id="pdf-681b6f3d947f-p116-b003"></a>
<!-- pdf-source: page=116; block=3; confidence=0.94 -->
**Exercise 5.1.9 (Blow-up of exponentially small sets).** Let A ⊂ √n Sⁿ⁻¹ with σ(A) > 2·exp(−cs²) for some s > 0. (a) Prove σ(As) > 1/2. (b) Deduce that for any t ≥ s, σ(A_{2t}) ≥ 1 − 2·exp(−ct²), where c > 0 is the constant from Lemma 5.1.7. Hint: if (a) fails, B := (As)ᶜ has σ(B) ≥ 1/2; apply Lemma 5.1.7 to B.

<a id="pdf-681b6f3d947f-p116-b004"></a>
<!-- pdf-source: page=116; block=4; confidence=0.90 -->
**Remark 5.1.10 (Zero-one law).** The blow-up transition of an exponentially small A to an exponentially large A_{2t} under a small perturbation 2t (with t ≪ √n) is a typical high-dimensional phenomenon, reminiscent of zero-one laws: events determined by many random variables tend to have probability zero or one.

<a id="pdf-681b6f3d947f-p117-b001"></a>
<!-- pdf-source: page=117; block=1; confidence=0.95 -->
**Section 5.1.4.** Proof of Theorem 5.1.4.

<a id="pdf-681b6f3d947f-p117-b002"></a>
<!-- pdf-source: page=117; block=2; confidence=0.94 -->
**Proof (of Theorem 5.1.4).** Assume WLOG ‖f‖_{Lip} = 1. Let M be a median of f(X): P{f(X) ≤ M} ≥ 1/2 and P{f(X) ≥ M} ≥ 1/2. Consider the sub-level set A := {x ∈ √n Sⁿ⁻¹ : f(x) ≤ M}. Since P{X ∈ A} ≥ 1/2, Lemma 5.1.7 gives P{X ∈ At} ≥ 1 − 2·exp(−ct²). (5.3) Claim: P{X ∈ At} ≤ P{f(X) ≤ M + t}. (5.4) Indeed, if X ∈ At then ‖X − y‖₂ ≤ t for some y ∈ A with f(y) ≤ M, so f(X) ≤ f(y) + ‖X − y‖₂ ≤ M + t. Combining (5.3) and (5.4): P{f(X) ≤ M + t} ≥ 1 − 2·exp(−ct²). Applying the same to −f bounds P{f(X) ≥ M − t}; together these bound P{|f(X) − M| ≤ t}, yielding ‖f(X) − M‖_{ψ₂} ≤ C. Replace the median M by E f via the Centering Lemma 2.6.8. ∎

<a id="pdf-681b6f3d947f-p117-b003"></a>
<!-- pdf-source: page=117; block=3; confidence=0.95 -->
**Exercise 5.1.11 (Geodesic metric).** Theorem 5.1.4 was proved for f Lipschitz with respect to the Euclidean metric ‖x − y‖₂; argue that the same result holds for the geodesic metric (length of the shortest arc joining x and y).

<a id="pdf-681b6f3d947f-p117-b004"></a>
<!-- pdf-source: page=117; block=4; confidence=0.95 -->
**Exercise 5.1.12 (Concentration on the unit sphere).** Deduce from the scaled-sphere version that a Lipschitz function f on the unit sphere Sⁿ⁻¹ satisfies ‖f(X) − E f(X)‖_{ψ₂} ≤ C‖f‖_{Lip}/√n. (5.5)

<a id="pdf-681b6f3d947f-p117-b005"></a>
<!-- pdf-source: page=117; block=5; confidence=0.90 -->
Footnote: the median need not be unique, but for continuous one-to-one functions f it is unique.

<a id="pdf-681b6f3d947f-p118-b001"></a>
<!-- pdf-source: page=118; block=1; confidence=0.95 -->
Concludes a concentration statement for $X \sim \mathrm{Unif}(S^{n-1})$: for every $t \ge 0$,
$$P\{|f(X) - \mathbb{E} f(X)| \ge t\} \le 2\exp\!\left(-\frac{cnt^2}{\|f\|_{\mathrm{Lip}}^2}\right) \tag{5.6}$$

<a id="pdf-681b6f3d947f-p118-b002"></a>
<!-- pdf-source: page=118; block=2; confidence=0.95 -->
The geometric approach proceeded in three steps: (a) a blow-up inequality (Lemma 5.1.7), (b) concentration about the median, (c) replacing the median by the expectation. The following exercises show these steps can be reversed.

<a id="pdf-681b6f3d947f-p118-b003"></a>
<!-- pdf-source: page=118; block=3; confidence=0.95 -->
**Exercise 5.1.13** (Concentration about expectation and median are equivalent). For a random variable $Z$ with median $M$, show that
$$c\|Z - \mathbb{E} Z\|_{\psi_2} \le \|Z - M\|_{\psi_2} \le C\|Z - \mathbb{E} Z\|_{\psi_2},$$
for absolute constants $c, C > 0$.

<a id="pdf-681b6f3d947f-p118-b004"></a>
<!-- pdf-source: page=118; block=4; confidence=0.95 -->
**Exercise 5.1.14** (Concentration and blow-up are equivalent). For a random vector $X$ in a metric space $(T,d)$ satisfying $\|f(X) - \mathbb{E} f(X)\|_{\psi_2} \le K\|f\|_{\mathrm{Lip}}$ for every Lipschitz $f: T \to \mathbb{R}$, define $\sigma(A) := P(X \in A)$ (a probability measure on $T$). Show that $\sigma(A) \ge 1/2$ implies, for every $t \ge 0$,
$$\sigma(A_t) \ge 1 - 2\exp(-ct^2/K^2),$$
with absolute constant $c > 0$. Here $A_t := \{x \in T : \exists y \in A,\ d(x,y) \le t\}$.

<a id="pdf-681b6f3d947f-p118-b005"></a>
<!-- pdf-source: page=118; block=5; confidence=0.95 -->
**Exercise 5.1.15** (Exponential set of mutually almost orthogonal points). Fix $\varepsilon \in (0,1)$. Show there exists a set $\{x_1, \dots, x_N\}$ of unit vectors in $\mathbb{R}^n$ that are mutually almost orthogonal, $|\langle x_i, x_j \rangle| \le \varepsilon$ for all $i \ne j$, with $N \ge \exp(c(\varepsilon) n)$.

<a id="pdf-681b6f3d947f-p119-b001"></a>
<!-- pdf-source: page=119; block=1; confidence=0.98 -->
**5.2 Concentration on other metric measure spaces**

<a id="pdf-681b6f3d947f-p119-b002"></a>
<!-- pdf-source: page=119; block=2; confidence=0.90 -->
The proof of Theorem 5.1.4 rested on (a) an isoperimetric inequality and (b) a blow-up of its minimizers. Other metric measure spaces satisfy both, yielding concentration; the examples covered are Gaussian concentration in $\mathbb{R}^n$ and concentration on the Hamming cube.

<a id="pdf-681b6f3d947f-p119-b003"></a>
<!-- pdf-source: page=119; block=3; confidence=0.95 -->
**5.2.1 Gaussian concentration.** The Gaussian measure of a Borel set $A \subset \mathbb{R}^n$ is
$$\gamma_n(A) := P\{X \in A\} = \frac{1}{(2\pi)^{n/2}} \int_A e^{-\|x\|_2^2/2}\, dx,$$
where $X \sim N(0, I_n)$.

<a id="pdf-681b6f3d947f-p119-b004"></a>
<!-- pdf-source: page=119; block=4; confidence=0.95 -->
**Theorem 5.2.1** (Gaussian isoperimetric inequality). Let $\varepsilon > 0$. Among all sets $A \subset \mathbb{R}^n$ with fixed Gaussian measure $\gamma_n(A)$, the half-spaces minimize the Gaussian measure of the neighborhood $\gamma_n(A_\varepsilon)$.

<a id="pdf-681b6f3d947f-p119-b005"></a>
<!-- pdf-source: page=119; block=5; confidence=0.95 -->
**Theorem 5.2.2** (Gaussian concentration). For $X \sim N(0, I_n)$ and Lipschitz $f: \mathbb{R}^n \to \mathbb{R}$ (Euclidean metric),
$$\|f(X) - \mathbb{E} f(X)\|_{\psi_2} \le C\|f\|_{\mathrm{Lip}}. \tag{5.7}$$

<a id="pdf-681b6f3d947f-p119-b006"></a>
<!-- pdf-source: page=119; block=6; confidence=0.95 -->
**Exercise 5.2.3.** Deduce Gaussian concentration (Theorem 5.2.2) from the Gaussian isoperimetric inequality (Theorem 5.2.1).

<a id="pdf-681b6f3d947f-p119-b007"></a>
<!-- pdf-source: page=119; block=7; confidence=0.90 -->
(a) For linear $f$, Theorem 5.2.2 follows since $N(0, I_n)$ is sub-gaussian. (b) For $f(x) = \|x\|_2$, it follows from Theorem 3.1.1.

<a id="pdf-681b6f3d947f-p120-b001"></a>
<!-- pdf-source: page=120; block=1; confidence=0.95 -->
**Exercise 5.2.4** (Replacing expectation by $L^p$ norm). In the concentration results for the sphere and Gauss space (Theorems 5.1.4 and 5.2.2), $\mathbb{E} f(X)$ may be replaced by $(\mathbb{E} f(X)^p)^{1/p}$ for any $p \ge 1$ and any non-negative $f$; constants may depend on $p$.

<a id="pdf-681b6f3d947f-p120-b002"></a>
<!-- pdf-source: page=120; block=2; confidence=0.95 -->
**5.2.2 Hamming cube.** The Hamming cube $(\{0,1\}^n, d, P)$ (Definition 4.2.14) uses the normalized Hamming distance
$$d(x,y) = \frac{1}{n}\,|\{i : x_i \ne y_i\}|$$
and the uniform probability measure $P(A) = |A|/2^n$ for $A \subset \{0,1\}^n$.

<a id="pdf-681b6f3d947f-p120-b003"></a>
<!-- pdf-source: page=120; block=3; confidence=0.95 -->
**Theorem 5.2.5** (Concentration on the Hamming cube). For $X \sim \mathrm{Unif}\{0,1\}^n$ (coordinates independent $\mathrm{Ber}(1/2)$) and $f: \{0,1\}^n \to \mathbb{R}$,
$$\|f(X) - \mathbb{E} f(X)\|_{\psi_2} \le \frac{C\|f\|_{\mathrm{Lip}}}{\sqrt{n}}. \tag{5.8}$$
Deduced from the Hamming-cube isoperimetric inequality, whose minimizers are the Hamming balls (neighborhoods of single points).

<a id="pdf-681b6f3d947f-p120-b004"></a>
<!-- pdf-source: page=120; block=4; confidence=0.92 -->
**5.2.3 Symmetric group.** The symmetric group $S_n$ of all $n!$ permutations of $\{1,\dots,n\}$, viewed as a metric measure space $(S_n, d, P)$ with normalized Hamming distance
$$d(\pi, \rho) = \frac{1}{n}\,|\{i : \pi(i) \ne \rho(i)\}|.$$

<a id="pdf-681b6f3d947f-p121-b001"></a>
<!-- pdf-source: page=121; block=1; confidence=0.97 -->
**Definition (uniform measure on S_n).** $P$ is the uniform probability measure on the symmetric group $S_n$: $P(A) = |A|/n!$ for any $A \subset S_n$.

<a id="pdf-681b6f3d947f-p121-b002"></a>
<!-- pdf-source: page=121; block=2; confidence=0.97 -->
**Theorem 5.2.6.** For a random permutation $X \sim \mathrm{Unif}(S_n)$ and any $f: S_n \to \mathbb{R}$, concentration inequality (5.8) holds.

<a id="pdf-681b6f3d947f-p121-b003"></a>
<!-- pdf-source: page=121; block=3; confidence=0.92 -->
**Section 5.2.4 (optional).** A compact connected smooth Riemannian manifold $(M,g)$ is treated as a metric measure space $(M, d, P)$, where $d(x,y)$ is the geodesic arclength (w.r.t. $g$) of a minimizing geodesic and $P = dv/V$ is the normalized Riemann volume measure ($V$ = total volume). Let $c(M)$ be the infimum of the Ricci curvature tensor over all tangent vectors.

<a id="pdf-681b6f3d947f-p121-b004"></a>
<!-- pdf-source: page=121; block=4; confidence=0.93 -->
**Result (5.9).** If $c(M) > 0$, then via semigroup methods, for any Lipschitz $f: M \to \mathbb{R}$,
$$\|f(X) - \mathbb{E} f(X)\|_{\psi_2} \le \frac{C\|f\|_{\mathrm{Lip}}}{\sqrt{c(M)}}. \quad (5.9)$$
Example: $c(S^{n-1}) = n-1$, so (5.9) recovers the sphere concentration inequality (5.5).

<a id="pdf-681b6f3d947f-p121-b005"></a>
<!-- pdf-source: page=121; block=5; confidence=0.95 -->
**Section 5.2.5.** $SO(n)$ consists of the distance-preserving linear maps on $\mathbb{R}^n$, equivalently the $n\times n$ orthogonal matrices with determinant $1$. It is viewed as the metric measure space $(SO(n), \|\cdot\|_F, P)$ with Frobenius-norm distance $\|A-B\|_F$ and uniform measure $P$.

<a id="pdf-681b6f3d947f-p121-b006"></a>
<!-- pdf-source: page=121; block=6; confidence=0.96 -->
**Theorem 5.2.7.** For a random orthogonal matrix $X \sim \mathrm{Unif}(SO(n))$ and any $f: SO(n) \to \mathbb{R}$, concentration inequality (5.8) holds.

<a id="pdf-681b6f3d947f-p122-b001"></a>
<!-- pdf-source: page=122; block=1; confidence=0.90 -->
**Proof (sketch).** Theorem 5.2.7 follows from the general Riemannian-manifold concentration of Section 5.2.4.

<a id="pdf-681b6f3d947f-p122-b002"></a>
<!-- pdf-source: page=122; block=2; confidence=0.92 -->
**Remark 5.2.8.** $P$ is the Haar measure on $SO(n)$: the unique rotation-invariant probability measure ($\mu(E)=\mu(T(E))$ for all $T \in SO(n)$). Construction: take an $n\times n$ Gaussian matrix $G$ with i.i.d. $N(0,1)$ entries and SVD $G = U\Sigma V^T$; then $X := U$ is uniform on $SO(n)$, and $\mu(A) := P\{X \in A\}$ defines Haar measure.

<a id="pdf-681b6f3d947f-p122-b003"></a>
<!-- pdf-source: page=122; block=3; confidence=0.93 -->
**Section 5.2.6.** The Grassmannian $G_{n,m}$ is the set of $m$-dimensional subspaces of $\mathbb{R}^n$; for $m=1$ it identifies with $S^{n-1}$. As a metric measure space $(G_{n,m}, d, P)$, the distance is $d(E,F) = \|P_E - P_F\|$ (operator norm of the difference of orthogonal projections onto $E,F$), and $P$ is the uniform (Haar) measure, giving random subspaces $E \sim \mathrm{Unif}(G_{n,m})$. Alternatively $E$ is the column span (image) of a random $n\times m$ Gaussian matrix with i.i.d. $N(0,1)$ entries.

<a id="pdf-681b6f3d947f-p123-b001"></a>
<!-- pdf-source: page=123; block=1; confidence=0.94 -->
**Theorem 5.2.9.** For a random subspace $X \sim \mathrm{Unif}(G_{n,m})$ and any $f: G_{n,m} \to \mathbb{R}$, concentration inequality (5.8) holds. It follows from concentration on $SO(n)$ via the quotient $G_{n,m} = SO(n)/(SO_m \times SO_{n-m})$, since concentration passes to quotients.

<a id="pdf-681b6f3d947f-p123-b002"></a>
<!-- pdf-source: page=123; block=2; confidence=0.93 -->
**Section 5.2.7.** Analogous concentration holds for the unit cube $[0,1]^n$ and the ball $\sqrt{n}\,B_2^n$ with Euclidean distance and uniform measures, obtained by pushing the Gaussian measure forward onto these uniform measures.

<a id="pdf-681b6f3d947f-p123-b003"></a>
<!-- pdf-source: page=123; block=3; confidence=0.95 -->
**Theorem 5.2.10.** For $X \sim \mathrm{Unif}([0,1]^n)$ (i.i.d. uniform coordinates) and any Lipschitz $f: [0,1]^n \to \mathbb{R}$ (Lipschitz norm w.r.t. Euclidean distance), concentration inequality (5.7) holds.

<a id="pdf-681b6f3d947f-p123-b004"></a>
<!-- pdf-source: page=123; block=4; confidence=0.95 -->
**Exercise 5.2.11.** With $\Phi$ the standard normal CDF and $Z = (Z_1,\dots,Z_n) \sim N(0,I_n)$, verify $\varphi(Z) := (\Phi(Z_1),\dots,\Phi(Z_n)) \sim \mathrm{Unif}([0,1]^n)$.

<a id="pdf-681b6f3d947f-p123-b005"></a>
<!-- pdf-source: page=123; block=5; confidence=0.94 -->
**Exercise 5.2.12.** Writing $X = \varphi(Z)$, apply Gaussian concentration to $f(\varphi(Z))$ using $\|f \circ \varphi\|_{\mathrm{Lip}} \le \|f\|_{\mathrm{Lip}}\,\|\varphi\|_{\mathrm{Lip}}$; show $\|\varphi\|_{\mathrm{Lip}}$ is bounded by an absolute constant to prove Theorem 5.2.10.

<a id="pdf-681b6f3d947f-p123-b006"></a>
<!-- pdf-source: page=123; block=6; confidence=0.95 -->
**Theorem 5.2.13.** For $X \sim \mathrm{Unif}(\sqrt{n}\,B_2^n)$ and any Lipschitz $f: \sqrt{n}\,B_2^n \to \mathbb{R}$ (Euclidean Lipschitz norm), concentration inequality (5.7) holds.

<a id="pdf-681b6f3d947f-p123-b007"></a>
<!-- pdf-source: page=123; block=7; confidence=0.93 -->
**Exercise 5.2.14.** By an analogous method, define $\varphi: \mathbb{R}^n \to \sqrt{n}\,B_2^n$ pushing the Gaussian measure forward to the uniform measure on $\sqrt{n}\,B_2^n$, and check that $\varphi$ has bounded Lipschitz norm, proving Theorem 5.2.13. Footnote: $B_2^n = \{x \in \mathbb{R}^n : \|x\|_2 \le 1\}$, and $\sqrt{n}\,B_2^n$ is the ball of radius $\sqrt{n}$.

<a id="pdf-681b6f3d947f-p124-b001"></a>
<!-- pdf-source: page=124; block=1; confidence=0.98 -->
### 5.2.8 Densities $e^{-U(x)}$

<a id="pdf-681b6f3d947f-p124-b002"></a>
<!-- pdf-source: page=124; block=2; confidence=0.95 -->
The push-forward method yields concentration for a random vector $X$ in $\mathbb{R}^n$ with density $f(x)=e^{-U(x)}$, $U:\mathbb{R}^n\to\mathbb{R}$. Example: $X\sim N(0,I_n)$ gives $U(x)=\tfrac{\|x\|_2^2}{2}+c$ (with $c$ constant in $x$), and Gaussian concentration holds. Curvature of $U$ is measured by the Hessian $\operatorname{Hess}U(x)$, the $n\times n$ symmetric matrix with $(i,j)$ entry $\partial^2 U/\partial x_i\partial x_j$.

<a id="pdf-681b6f3d947f-p124-b003"></a>
<!-- pdf-source: page=124; block=3; confidence=0.97 -->
**Theorem 5.2.15.** Let $X$ in $\mathbb{R}^n$ have density $f(x)=e^{-U(x)}$, $U:\mathbb{R}^n\to\mathbb{R}$. If there is $\kappa>0$ with $\operatorname{Hess}U(x)\succeq\kappa I_n$ for all $x\in\mathbb{R}^n$, then every Lipschitz $f:\mathbb{R}^n\to\mathbb{R}$ satisfies $\|f(X)-\mathbb{E}f(X)\|_{\psi_2}\le \dfrac{C\|f\|_{\mathrm{Lip}}}{\sqrt{\kappa}}$.

<a id="pdf-681b6f3d947f-p124-b004"></a>
<!-- pdf-source: page=124; block=4; confidence=0.95 -->
Remark: this parallels the Riemannian-manifold concentration inequality (5.9); both provable via semigroup tools, not presented here. (Footnote 12: $\operatorname{Hess}U(x)\succeq\kappa I_n$ means $\operatorname{Hess}U(x)-\kappa I_n$ is symmetric positive semidefinite.)

<a id="pdf-681b6f3d947f-p124-b005"></a>
<!-- pdf-source: page=124; block=5; confidence=0.98 -->
### 5.2.9 Random vectors with independent bounded coordinates

<a id="pdf-681b6f3d947f-p124-b006"></a>
<!-- pdf-source: page=124; block=6; confidence=0.96 -->
**Theorem 5.2.16 (Talagrand's concentration inequality).** Let $X=(X_1,\dots,X_n)$ have independent coordinates with $|X_i|\le 1$ almost surely (coordinates need not be uniform; $|X_i|\le1$ is WLOG by scaling). Then concentration inequality (5.7) holds for any convex Lipschitz $f:[-1,1]^n\to\mathbb{R}$; in particular for any norm on $\mathbb{R}^n$. Stated without proof.

<a id="pdf-681b6f3d947f-p125-b001"></a>
<!-- pdf-source: page=125; block=1; confidence=0.98 -->
## 5.3 Application: Johnson-Lindenstrauss Lemma

<a id="pdf-681b6f3d947f-p125-b002"></a>
<!-- pdf-source: page=125; block=2; confidence=0.95 -->
Goal: reduce dimension of $N$ points in $\mathbb{R}^n$ (large $n$) by projecting onto a subspace $E\subset\mathbb{R}^n$ with $\dim(E)=m\ll n$, preserving geometry. The Johnson-Lindenstrauss Lemma shows geometry is well preserved for a random subspace of dimension $m\asymp\log N$. Definition: $E\sim\mathrm{Unif}(G_{n,m})$ means $E$ is a random $m$-dimensional subspace whose distribution is rotation invariant, i.e. $\mathbb{P}\{E\in\mathcal{E}\}=\mathbb{P}\{U(E)\in\mathcal{E}\}$ for every subset $\mathcal{E}\subset G_{n,m}$ and orthogonal $n\times n$ matrix $U$.

<a id="pdf-681b6f3d947f-p125-b003"></a>
<!-- pdf-source: page=125; block=3; confidence=0.94 -->
**Theorem 5.3.1 (Johnson-Lindenstrauss Lemma).** Let $\mathcal{X}$ be a set of $N$ points in $\mathbb{R}^n$ and $\varepsilon>0$, with $m\ge (C/\varepsilon^2)\log N$. [Statement continues on page 126.]

<a id="pdf-681b6f3d947f-p126-b001"></a>
<!-- pdf-source: page=126; block=1; confidence=0.96 -->
**Theorem 5.3.1 (continued).** Let $E$ be a random $m$-dimensional subspace of $\mathbb{R}^n$ uniform in $G_{n,m}$, with orthogonal projection $P$ onto $E$. Then with probability at least $1-2\exp(-c\varepsilon^2 m)$ the scaled projection $Q:=\sqrt{n/m}\,P$ is an approximate isometry on $\mathcal{X}$:
$$(1-\varepsilon)\|x-y\|_2\le\|Qx-Qy\|_2\le(1+\varepsilon)\|x-y\|_2\quad\text{for all }x,y\in\mathcal{X}.\tag{5.10}$$

<a id="pdf-681b6f3d947f-p126-b002"></a>
<!-- pdf-source: page=126; block=2; confidence=0.95 -->
Proof idea: use concentration of Lipschitz functions on the sphere (Section 5.1) to control how $P$ acts on a fixed difference $x-y$, then take a union bound over the $N^2$ differences.

<a id="pdf-681b6f3d947f-p126-b003"></a>
<!-- pdf-source: page=126; block=3; confidence=0.96 -->
**Lemma 5.3.2 (Random projection).** Let $P$ project $\mathbb{R}^n$ onto a random $m$-dimensional subspace uniform in $G_{n,m}$, let $z\in\mathbb{R}^n$ be fixed and $\varepsilon>0$. Then:
(a) $\big(\mathbb{E}\|Pz\|_2^2\big)^{1/2}=\sqrt{m/n}\,\|z\|_2$.
(b) With probability at least $1-2\exp(-c\varepsilon^2 m)$, $\;(1-\varepsilon)\sqrt{m/n}\,\|z\|_2\le\|Pz\|_2\le(1+\varepsilon)\sqrt{m/n}\,\|z\|_2$.

<a id="pdf-681b6f3d947f-p126-b004"></a>
<!-- pdf-source: page=126; block=4; confidence=0.95 -->
**Proof.** WLOG $\|z\|_2=1$. Switch to the equivalent model: fix $P$ and take $z\sim\mathrm{Unif}(S^{n-1})$ (distribution of $\|Pz\|_2$ unchanged by rotation invariance). WLOG $P$ is the coordinate projection onto the first $m$ coordinates. Then
$$\mathbb{E}\|Pz\|_2^2=\mathbb{E}\sum_{i=1}^m z_i^2=\sum_{i=1}^m\mathbb{E}z_i^2=m\,\mathbb{E}z_1^2,\tag{5.11}$$
since the $z_i$ are identically distributed. From $1=\|z\|_2^2=\sum_{i=1}^n z_i^2$, taking expectations gives $1=\sum_{i=1}^n\mathbb{E}z_i^2=n\,\mathbb{E}z_1^2$. [Proof continues beyond supplied pages.]

<a id="pdf-681b6f3d947f-p127-b001"></a>
<!-- pdf-source: page=127; block=1; confidence=0.95 -->
**Proof (first part).** Since $\mathbb{E}\, z_1^2 = 1/n$, substituting into (5.11) gives $\mathbb{E}\,\|Pz\|_2^2 = m/n$, proving the first part of the lemma.

<a id="pdf-681b6f3d947f-p127-b002"></a>
<!-- pdf-source: page=127; block=2; confidence=0.95 -->
**Proof (second part).** The function $f(x):=\|Px\|_2$ is Lipschitz on $S^{n-1}$ with $\|f\|_{\mathrm{Lip}}=1$. Concentration inequality (5.6) yields
$$\mathbb{P}\left\{\left|\,\|Px\|_2 - \sqrt{m/n}\,\right| \ge t\right\} \le 2\exp(-cnt^2),$$
using Exercise 5.2.4 to replace $\mathbb{E}\|x\|_2$ by $(\mathbb{E}\|x\|_2^2)^{1/2}$. Choosing $t:=\varepsilon\sqrt{m/n}$ completes the proof.

<a id="pdf-681b6f3d947f-p127-b003"></a>
<!-- pdf-source: page=127; block=3; confidence=0.95 -->
**Proof of Johnson-Lindenstrauss Lemma.** Let the difference set be $X-X:=\{x-y: x,y\in X\}$. The goal $(1-\varepsilon)\|z\|_2 \le \|Qz\|_2 \le (1+\varepsilon)\|z\|_2$ for all $z\in X-X$, with $Q=\sqrt{n/m}\,P$, is equivalent to (5.12):
$$(1-\varepsilon)\sqrt{m/n}\,\|z\|_2 \le \|Pz\|_2 \le (1+\varepsilon)\sqrt{m/n}\,\|z\|_2.$$
For fixed $z$, Lemma 5.3.2 gives (5.12) with probability $\ge 1-2\exp(-c\varepsilon^2 m)$. A union bound over $z\in X-X$ gives simultaneous validity with probability
$$\ge 1 - |X-X|\cdot 2\exp(-c\varepsilon^2 m) \ge 1 - N^2\cdot 2\exp(-c\varepsilon^2 m).$$
If $m \ge (C/\varepsilon^2)\log N$, this is $\ge 1-2\exp(-c\varepsilon^2 m/2)$, as claimed. $\square$

<a id="pdf-681b6f3d947f-p127-b004"></a>
<!-- pdf-source: page=127; block=4; confidence=0.90 -->
Remark: the dimension reduction map $A$ is non-adaptive (independent of the data), and the ambient dimension $n$ plays no role in the result.

<a id="pdf-681b6f3d947f-p128-b001"></a>
<!-- pdf-source: page=128; block=1; confidence=0.95 -->
**Exercise 5.3.3 (Johnson-Lindenstrauss with sub-gaussian matrices).** Let $A$ be an $m\times n$ random matrix whose rows are independent, mean zero, sub-gaussian isotropic random vectors in $\mathbb{R}^n$. Show the JL conclusion holds for $Q=(1/\sqrt{m})A$.

<a id="pdf-681b6f3d947f-p128-b002"></a>
<!-- pdf-source: page=128; block=2; confidence=0.95 -->
**Exercise 5.3.4 (Optimality of Johnson-Lindenstrauss).** Give an example of a set $X$ of $N$ points for which no scaled projection onto a subspace of dimension $m \ll \log N$ is an approximate isometry. *Hint:* take $X$ an orthogonal basis and show the projected set is a packing.

<a id="pdf-681b6f3d947f-p128-b003"></a>
<!-- pdf-source: page=128; block=3; confidence=0.90 -->
**5.4 Matrix Bernstein's inequality.** Generalizes concentration for sums of independent random variables $\sum X_i$ to sums of independent random matrices: a matrix version of Bernstein's inequality (Theorem 2.8.4) with $|\cdot|$ replaced by the operator norm $\|\cdot\|$; independence of entries/rows/columns within each $X_i$ is not required.

<a id="pdf-681b6f3d947f-p128-b004"></a>
<!-- pdf-source: page=128; block=4; confidence=0.95 -->
**Theorem 5.4.1 (Matrix Bernstein's inequality).** Let $X_1,\dots,X_N$ be independent, mean zero, $n\times n$ symmetric random matrices with $\|X_i\|\le K$ almost surely. Then for every $t\ge 0$,
$$\mathbb{P}\left\{\Big\|\sum_{i=1}^N X_i\Big\| \ge t\right\} \le 2n\exp\!\left(-\frac{t^2/2}{\sigma^2 + Kt/3}\right),$$
where $\sigma^2 = \big\|\sum_{i=1}^N \mathbb{E}\,X_i^2\big\|$ is the norm of the matrix variance of the sum. Equivalently, as a mixture of sub-gaussian and sub-exponential tails,
$$\mathbb{P}\left\{\Big\|\sum_{i=1}^N X_i\Big\| \ge t\right\} \le 2n\exp\!\left[-c\cdot\min\!\left(\frac{t^2}{\sigma^2},\ \frac{t}{K}\right)\right].$$

<a id="pdf-681b6f3d947f-p128-b005"></a>
<!-- pdf-source: page=128; block=5; confidence=0.90 -->
Proof strategy: repeat the classical moment-generating-function argument (Section 2.8), replacing scalars by matrices; every step generalizes except one non-trivial step. First develop matrix calculus to treat matrices as scalars.

<a id="pdf-681b6f3d947f-p128-b006"></a>
<!-- pdf-source: page=128; block=6; confidence=0.90 -->
**5.4.1 Matrix calculus.** Work with symmetric $n\times n$ matrices. Addition $A+B$ generalizes from scalars directly; multiplication requires care since it is non-commutative.

<a id="pdf-681b6f3d947f-p129-b001"></a>
<!-- pdf-source: page=129; block=1; confidence=0.90 -->
Since in general $AB\ne BA$, matrix Bernstein's inequality is also called the non-commutative Bernstein's inequality.

<a id="pdf-681b6f3d947f-p129-b002"></a>
<!-- pdf-source: page=129; block=2; confidence=0.97 -->
**Definition 5.4.2 (Functions of matrices).** For $f:\mathbb{R}\to\mathbb{R}$ and an $n\times n$ symmetric matrix $X$ with eigenvalues $\lambda_i$ and eigenvectors $u_i$, using the spectral decomposition $X=\sum_{i=1}^n \lambda_i u_i u_i^{\mathsf T}$, define
$$f(X):=\sum_{i=1}^n f(\lambda_i)\,u_i u_i^{\mathsf T}.$$
I.e., keep the eigenvectors and apply $f$ to the eigenvalues.

<a id="pdf-681b6f3d947f-p129-b003"></a>
<!-- pdf-source: page=129; block=3; confidence=0.95 -->
**Exercise 5.4.3 (Matrix polynomials and power series).** (a) For a polynomial $f(x)=a_0+a_1x+\cdots+a_px^p$, verify $f(X)=a_0 I + a_1 X + \cdots + a_p X^p$ (with $X^p=X\cdots X$, $p$ times). (b) For a convergent power series $f(x)=\sum_{k=1}^\infty a_k(x-x_0)^k$, verify the matrix series converges and $f(X)=\sum_{k=1}^\infty a_k(X-x_0 I)^k$. Example: $e^X = I + X + \frac{X^2}{2!} + \frac{X^3}{3!} + \cdots$.

<a id="pdf-681b6f3d947f-p129-b004"></a>
<!-- pdf-source: page=129; block=4; confidence=0.90 -->
Matrices can be compared: a partial order on $n\times n$ symmetric matrices is defined (definition begins here, continuing beyond the supplied pages).

<a id="pdf-681b6f3d947f-p130-b001"></a>
<!-- pdf-source: page=130; block=1; confidence=0.97 -->
**Definition 5.4.4 (positive semidefinite order).** Write $X \succeq 0$ if $X$ is symmetric positive semidefinite, equivalently symmetric with all eigenvalues $\lambda_i(X) \ge 0$. Write $X \succeq Y$ (and $Y \preceq X$) if $X - Y \succeq 0$. This $\succeq$ is a partial (not total) order: some pairs satisfy neither $X \succeq Y$ nor $Y \succeq X$.

<a id="pdf-681b6f3d947f-p130-b002"></a>
<!-- pdf-source: page=130; block=2; confidence=0.95 -->
**Exercise 5.4.5.** Prove: (a) $\lVert X\rVert \le t$ iff $-tI \preceq X \preceq tI$. (b) For $f,g:\mathbb{R}\to\mathbb{R}$, if $f(x)\le g(x)$ for all $|x|\le K$, then $f(X)\preceq g(X)$ whenever $\lVert X\rVert \le K$. (c) For increasing $f$ and commuting $X,Y$, $X\preceq Y$ implies $f(X)\preceq f(Y)$. (d) Give a non-commuting counterexample to (c) (hint: $2\times2$ with $0\preceq X\preceq Y$ but $X^2 \not\preceq Y^2$). (e) For arbitrary matrices, $X\preceq Y$ implies $\operatorname{tr} f(X)\le \operatorname{tr} f(Y)$ for increasing $f$ (hint: Courant–Fischer min-max (4.2) gives $\lambda_i(X)\le\lambda_i(Y)$). (f) $0\preceq X\preceq Y$ with $X$ invertible implies $X^{-1}\succeq Y^{-1}$. (g) $0\preceq X\preceq Y$ implies $\log X \preceq \log Y$ (hint: $\log x = \int_0^\infty (\tfrac{1}{1+t}-\tfrac{1}{x+t})\,dt$ and (f)).

<a id="pdf-681b6f3d947f-p130-b003"></a>
<!-- pdf-source: page=130; block=3; confidence=0.93 -->
**5.4.2 Trace inequalities.** Extending scalar notions to matrices can fail due to non-commutativity ($AB\ne BA$); in particular the scalar identity $e^{x+y}=e^x e^y$ fails for matrices.

<a id="pdf-681b6f3d947f-p130-b004"></a>
<!-- pdf-source: page=130; block=4; confidence=0.96 -->
**Exercise 5.4.6.** Let $X,Y$ be $n\times n$ symmetric. (a) Show that if $XY=YX$ then $e^{X+Y}=e^X e^Y$.

<a id="pdf-681b6f3d947f-p131-b001"></a>
<!-- pdf-source: page=131; block=1; confidence=0.90 -->
**Exercise 5.4.6 (b).** Find matrices $X,Y$ with $e^{X+Y}\ne e^X e^Y$. This is problematic because the identity $e^{x+y}=e^x e^y$ was used to factor the MGF $\mathbb{E}\exp(\lambda S)$ of a sum into a product of exponentials, cf. (2.6). Two substitute trace inequalities follow (stated without proof).

<a id="pdf-681b6f3d947f-p131-b002"></a>
<!-- pdf-source: page=131; block=2; confidence=0.97 -->
**Theorem 5.4.7 (Golden–Thompson inequality).** For any $n\times n$ symmetric $A,B$, $\operatorname{tr}(e^{A+B}) \le \operatorname{tr}(e^A e^B)$. It fails for three or more matrices: in general $\operatorname{tr}(e^{A+B+C}) \le \operatorname{tr}(e^A e^B e^C)$ need not hold.

<a id="pdf-681b6f3d947f-p131-b003"></a>
<!-- pdf-source: page=131; block=3; confidence=0.96 -->
**Theorem 5.4.8 (Lieb's inequality).** For a fixed $n\times n$ symmetric $H$, the matrix function $f(X):=\operatorname{tr}\exp(H+\log X)$ is concave on the space of positive definite $n\times n$ symmetric matrices. (Concavity: $f(\lambda X+(1-\lambda)Y)\ge \lambda f(X)+(1-\lambda)f(Y)$ for $\lambda\in[0,1]$.) In the scalar case $n=1$, $f$ is linear and the inequality is trivial.

<a id="pdf-681b6f3d947f-p131-b004"></a>
<!-- pdf-source: page=131; block=4; confidence=0.96 -->
Applying Lieb's inequality with Jensen's inequality to a random matrix $X$ gives $\mathbb{E} f(X) \le f(\mathbb{E} X)$; setting $X=e^Z$ yields:

**Lemma 5.4.9 (Lieb's inequality for random matrices).** For a fixed $n\times n$ symmetric $H$ and a random $n\times n$ symmetric $Z$, $\mathbb{E}\operatorname{tr}\exp(H+Z) \le \operatorname{tr}\exp(H+\log \mathbb{E} e^Z)$.

<a id="pdf-681b6f3d947f-p131-b005"></a>
<!-- pdf-source: page=131; block=5; confidence=0.95 -->
**5.4.3 Proof of matrix Bernstein's inequality.** The proof of Theorem 5.4.1 proceeds via Lieb's inequality.

<a id="pdf-681b6f3d947f-p132-b001"></a>
<!-- pdf-source: page=132; block=1; confidence=0.95 -->
**Step 1 (Reduction to MGF).** For $S:=\sum_{i=1}^N X_i$, bound the largest and smallest eigenvalues separately. With $\lambda_{\max}(S):=\max_i \lambda_i(S)$, one has $\lVert S\rVert = \max_i |\lambda_i(S)| = \max(\lambda_{\max}(S),\lambda_{\max}(-S))$ (5.13). For $\lambda\ge 0$, Markov's inequality gives $\mathbb{P}\{\lambda_{\max}(S)\ge t\} = \mathbb{P}\{e^{\lambda\lambda_{\max}(S)}\ge e^{\lambda t}\} \le e^{-\lambda t}\,\mathbb{E} e^{\lambda\lambda_{\max}(S)}$ (5.14). Since eigenvalues of $e^{\lambda S}$ are $e^{\lambda\lambda_i(S)}$, set $E:=\mathbb{E} e^{\lambda\lambda_{\max}(S)} = \mathbb{E}\lambda_{\max}(e^{\lambda S})$. As these eigenvalues are positive, $\lambda_{\max}(e^{\lambda S})\le \operatorname{tr}(e^{\lambda S})$, so $E \le \mathbb{E}\operatorname{tr} e^{\lambda S}$.

<a id="pdf-681b6f3d947f-p132-b002"></a>
<!-- pdf-source: page=132; block=2; confidence=0.95 -->
**Step 2 (Application of Lieb's inequality).** Separate the last term: $E \le \mathbb{E}\operatorname{tr}\exp\big(\sum_{i=1}^{N-1}\lambda X_i + \lambda X_N\big)$. Conditioning on $(X_i)_{i=1}^{N-1}$ and applying Lemma 5.4.9 with $H:=\sum_{i=1}^{N-1}\lambda X_i$ and $Z:=\lambda X_N$ (then taking total expectation) gives $E \le \mathbb{E}\operatorname{tr}\exp\big(\sum_{i=1}^{N-1}\lambda X_i + \log \mathbb{E} e^{\lambda X_N}\big)$. Repeating $N$ times (peeling off $\lambda X_{N-1}$, etc.) yields $E \le \operatorname{tr}\exp\big(\sum_{i=1}^{N}\log \mathbb{E} e^{\lambda X_i}\big)$ (5.15).

<a id="pdf-681b6f3d947f-p133-b001"></a>
<!-- pdf-source: page=133; block=1; confidence=0.95 -->
**Step 3 (MGF of individual terms).** Remaining task: bound the matrix-valued MGF $\mathbb{E}\, e^{\lambda X_i}$ for each term $X_i$, analogously to the scalar case.

<a id="pdf-681b6f3d947f-p133-b002"></a>
<!-- pdf-source: page=133; block=2; confidence=0.97 -->
**Lemma 5.4.10 (Moment generating function).** Let $X$ be an $n\times n$ symmetric mean-zero random matrix with $\lVert X\rVert \le K$ almost surely. Then
$$\mathbb{E}\exp(\lambda X) \preceq \exp\!\big(g(\lambda)\,\mathbb{E}\,X^2\big),\qquad g(\lambda)=\frac{\lambda^2/2}{1-|\lambda|K/3},$$
provided $|\lambda| < 3/K$.

<a id="pdf-681b6f3d947f-p133-b003"></a>
<!-- pdf-source: page=133; block=3; confidence=0.95 -->
**Proof.** Scalar bound from truncated Taylor expansion: for $|z|<3$,
$$e^z \le 1 + z + \frac{1}{1-|z|/3}\cdot\frac{z^2}{2},$$
obtained by writing $e^z = 1+z+z^2\sum_{p=2}^\infty z^{p-2}/p!$ and using $p!\ge 2\cdot 3^{p-2}$. Apply with $z=\lambda x$: if $|x|\le K$ and $|\lambda|<3/K$ then $e^{\lambda x}\le 1+\lambda x + g(\lambda)x^2$. Transfer to matrices via Exercise 5.4.5(b): if $\lVert X\rVert\le K$, $|\lambda|<3/K$, then $e^{\lambda X}\preceq I+\lambda X + g(\lambda)X^2$. Take expectations using $\mathbb{E}\,X=0$: $\mathbb{E}\,e^{\lambda X}\preceq I + g(\lambda)\,\mathbb{E}\,X^2$. Finally use $I+Z\preceq e^Z$ (matrix form of $1+z\le e^z$, again Exercise 5.4.5(b)) with $Z=g(\lambda)\,\mathbb{E}\,X^2$ to conclude.

<a id="pdf-681b6f3d947f-p133-b004"></a>
<!-- pdf-source: page=133; block=4; confidence=0.94 -->
**Step 4 (Completion).** Returning to bounding $E$ in (5.15), Lemma 5.4.10 gives
$$E \le \operatorname{tr}\exp\!\Big[\sum_{i=1}^N \log \mathbb{E}\,e^{\lambda X_i}\Big] \le \operatorname{tr}\exp\big[g(\lambda)Z\big],\quad Z:=\sum_{i=1}^N \mathbb{E}\,X_i^2,$$
using Exercise 5.4.5(g) (logarithms) and (e) (trace of exponential). Since $\operatorname{tr}\exp[g(\lambda)Z]$ is a sum of $n$ positive eigenvalues, it is at most $n$ times the largest:
$$E \le n\cdot\lambda_{\max}\big(\exp[g(\lambda)Z]\big) = n\exp\big[g(\lambda)\lambda_{\max}(Z)\big] = n\exp\big[g(\lambda)\lVert Z\rVert\big] = n\exp\big[g(\lambda)\sigma^2\big],$$
where $\lVert Z\rVert=\lambda_{\max}(Z)$ since $Z\succeq 0$, and $\sigma^2=\lVert Z\rVert$ by definition in the theorem.

<a id="pdf-681b6f3d947f-p134-b001"></a>
<!-- pdf-source: page=134; block=1; confidence=0.95 -->
**Step 4 (Completion, cont.).** Plugging $E=\mathbb{E}\,e^{\lambda\cdot\lambda_{\max}(S)}$ into (5.14):
$$\mathbb{P}\{\lambda_{\max}(S)\ge t\} \le n\exp\big[-\lambda t + g(\lambda)\sigma^2\big],\qquad 0<\lambda<3/K.$$
Minimizing over $\lambda$ by the choice $\lambda = t/(\sigma^2 + Kt/3)$ yields
$$\mathbb{P}\{\lambda_{\max}(S)\ge t\} \le n\exp\!\Big(-\frac{t^2/2}{\sigma^2 + Kt/3}\Big).$$
Repeating for $-S$ and combining via (5.13) completes the proof of Theorem 5.4.1.

<a id="pdf-681b6f3d947f-p134-b002"></a>
<!-- pdf-source: page=134; block=2; confidence=0.90 -->
## 5.4.4 Matrix Khintchine's inequality

Matrix Bernstein's tail bound on $\lVert\sum_{i=1}^N X_i\rVert$ also implies a nontrivial expectation bound.

<a id="pdf-681b6f3d947f-p134-b003"></a>
<!-- pdf-source: page=134; block=3; confidence=0.93 -->
**Exercise 5.4.11 (Matrix Bernstein: expectation).** Let $X_1,\dots,X_N$ be independent, mean-zero, $n\times n$ symmetric random matrices with $\lVert X_i\rVert\le K$ a.s. Deduce from Bernstein's inequality that
$$\mathbb{E}\Big\lVert\sum_{i=1}^N X_i\Big\rVert \;\lesssim\; \Big\lVert\sum_{i=1}^N \mathbb{E}\,X_i^2\Big\rVert^{1/2}\sqrt{1+\log n} + K(1+\log n).$$
*Hint:* Bernstein implies $\lVert\sum X_i\rVert \lesssim \lVert\sum \mathbb{E}\,X_i^2\rVert^{1/2}\sqrt{\log n + u} + K(\log n + u)$ with probability $\ge 1-2e^{-u}$; then use the integral identity of Lemma 1.2.1.

<a id="pdf-681b6f3d947f-p134-b004"></a>
<!-- pdf-source: page=134; block=4; confidence=0.92 -->
In the scalar case $n=1$ the expectation bound is trivial: $\mathbb{E}|\sum_{i=1}^N X_i| \le (\mathbb{E}|\sum X_i|^2)^{1/2} = (\sum_{i=1}^N \mathbb{E}\,X_i^2)^{1/2}$, since the variance of a sum of independent variables equals the sum of variances. The same techniques give matrix versions of Hoeffding's (Thm 2.2.2) and Khintchine's (Exercise 2.6.6) inequalities.

<a id="pdf-681b6f3d947f-p134-b005"></a>
<!-- pdf-source: page=134; block=5; confidence=0.93 -->
**Exercise 5.4.12 (Matrix Hoeffding's inequality).** Let $\varepsilon_1,\dots,\varepsilon_n$ be independent symmetric Bernoulli variables and $A_1,\dots,A_N$ deterministic symmetric $n\times n$ matrices. Prove that for any $t\ge 0$,
$$\mathbb{P}\Big\{\Big\lVert\sum_{i=1}^N \varepsilon_i A_i\Big\rVert \ge t\Big\} \le 2n\exp(-t^2/2\sigma^2),$$

<a id="pdf-681b6f3d947f-p135-b001"></a>
<!-- pdf-source: page=135; block=1; confidence=0.94 -->
where $\sigma^2 = \big\lVert\sum_{i=1}^N A_i^2\big\rVert$. *Hint:* Proceed as in the proof of Theorem 5.4.1, but in place of Lemma 5.4.10 check that $\mathbb{E}\exp(\lambda\varepsilon_i A_i)\preceq \exp(\lambda^2 A_i^2/2)$, as in the proof of Hoeffding's inequality (Theorem 2.2.2).

<a id="pdf-681b6f3d947f-p135-b002"></a>
<!-- pdf-source: page=135; block=2; confidence=0.95 -->
**Exercise 5.4.13 (Matrix Khintchine's inequality).** Let $\varepsilon_1,\dots,\varepsilon_N$ be independent symmetric Bernoulli variables and $A_1,\dots,A_N$ deterministic symmetric $n\times n$ matrices.

**(a)** Prove $\mathbb{E}\big\lVert\sum_{i=1}^N \varepsilon_i A_i\big\rVert \le C\sqrt{1+\log n}\,\big\lVert\sum_{i=1}^N A_i^2\big\rVert^{1/2}.$

**(b)** More generally, for every $p\in[1,\infty)$,
$$\Big(\mathbb{E}\big\lVert\textstyle\sum_{i=1}^N \varepsilon_i A_i\big\rVert^p\Big)^{1/p} \le C\sqrt{p+\log n}\,\Big\lVert\sum_{i=1}^N A_i^2\Big\rVert^{1/2}.$$

<a id="pdf-681b6f3d947f-p135-b003"></a>
<!-- pdf-source: page=135; block=3; confidence=0.90 -->
The scalar-to-matrix price is the prefactor $n$ in Theorem 5.4.1's probability bound, which becomes only logarithmic in $n$ in the expectation bounds of Exercises 5.4.11–5.4.13. The next example shows the logarithmic factor is necessary in general.

<a id="pdf-681b6f3d947f-p135-b004"></a>
<!-- pdf-source: page=135; block=4; confidence=0.94 -->
**Exercise 5.4.14 (Sharpness of matrix Bernstein).** Let $X$ be an $n\times n$ random matrix taking value $e_k e_k^{\mathsf T}$ ($e_k$ the standard basis of $\mathbb{R}^n$) with probability $1/n$ each, $k=1,\dots,n$. Let $X_1,\dots,X_N$ be independent copies and $S:=\sum_{i=1}^N X_i$, a diagonal matrix.

**(a)** Show $S_{ii}$ has the distribution of the number of balls in bin $i$ when $N$ balls are thrown independently into $n$ bins.

**(b)** Via the coupon collector's problem, show that if $N\asymp n$ then $\mathbb{E}\lVert S\rVert \asymp \dfrac{\log n}{\log\log n}$, and deduce that the bound in Exercise 5.4.11 would fail if the logarithmic factors were removed.

<a id="pdf-681b6f3d947f-p135-b005"></a>
<!-- pdf-source: page=135; block=5; confidence=0.95 -->
**Notation.** Write $a_n \asymp b_n$ if there exist constants $c,C>0$ with $c\,a_n < b_n \le C\,a_n$ for all $n$.

<a id="pdf-681b6f3d947f-p136-b001"></a>
<!-- pdf-source: page=136; block=1; confidence=0.95 -->
**Exercise 5.4.15 (Matrix Bernstein's inequality for rectangular matrices).** Let $X_1,\dots,X_N$ be independent, mean-zero $m\times n$ random matrices with $\|X_i\|\le K$ almost surely for all $i$. Prove that for $t\ge 0$,
$$P\Big\{\Big\|\sum_{i=1}^N X_i\Big\|\ge t\Big\}\le 2(m+n)\exp\!\Big(-\frac{t^2/2}{\sigma^2+Kt/3}\Big),$$
where $\sigma^2=\max\big(\big\|\sum_{i=1}^N \mathbb{E}\,X_i^{\mathsf T}X_i\big\|,\ \big\|\sum_{i=1}^N \mathbb{E}\,X_iX_i^{\mathsf T}\big\|\big)$. Hint: apply matrix Bernstein (Theorem 5.4.1) to the $(m+n)\times(m+n)$ symmetric matrices $\begin{bmatrix}0 & X_i^{\mathsf T}\\ X_i & 0\end{bmatrix}$.

<a id="pdf-681b6f3d947f-p136-b002"></a>
<!-- pdf-source: page=136; block=2; confidence=0.98 -->
**5.5 Application: community detection in sparse networks**

<a id="pdf-681b6f3d947f-p136-b003"></a>
<!-- pdf-source: page=136; block=3; confidence=0.92 -->
Re-examines spectral clustering (from Section 4.5) for the stochastic block model $G(n,p,q)$ with two communities using matrix Bernstein's inequality, showing it works for sparser networks than Theorem 4.5.6 gave. Let $A$ be the adjacency matrix of a random graph from $G(n,p,q)$, written $A=D+R$ where $D=\mathbb{E}\,A$ is the deterministic signal and $R$ is random noise; success hinges on $\|R\|$ being small (cf. (4.18)).

<a id="pdf-681b6f3d947f-p136-b004"></a>
<!-- pdf-source: page=136; block=4; confidence=0.93 -->
**Exercise 5.5.1 (Controlling the noise).** (a) Represent the adjacency matrix as a sum of independent random matrices $A=\sum_{1\le i\le j\le n} Z_{ij}$, where each $Z_{ij}$ encodes the edge between vertices $i$ and $j$: its only nonzero entries are $(ij)$ and $(ji)$, equal to those of $A$. (b) Apply matrix Bernstein's inequality to obtain $\mathbb{E}\|R\|\lesssim \sqrt{d\log n}+\log n$.

<a id="pdf-681b6f3d947f-p137-b001"></a>
<!-- pdf-source: page=137; block=1; confidence=0.90 -->
Completing Exercise 5.5.1(b): here $d=\tfrac12(p+q)n$ is the expected average degree of the graph.

<a id="pdf-681b6f3d947f-p137-b002"></a>
<!-- pdf-source: page=137; block=2; confidence=0.94 -->
**Exercise 5.5.2 (Spectral clustering for sparse networks).** Use the bound from Exercise 5.5.1 to give better performance guarantees for spectral clustering than Section 4.5; in particular argue it works for sparse networks provided the average expected degree satisfies $d\gg\log n$.

<a id="pdf-681b6f3d947f-p137-b003"></a>
<!-- pdf-source: page=137; block=3; confidence=0.98 -->
**5.6 Application: covariance estimation for general distributions**

<a id="pdf-681b6f3d947f-p137-b004"></a>
<!-- pdf-source: page=137; block=4; confidence=0.92 -->
Removes the sub-gaussian requirement of Section 4.7, enabling covariance estimation for general (including discrete) distributions at the cost of a logarithmic oversampling factor. The second moment matrix $\Sigma=\mathbb{E}\,XX^{\mathsf T}$ is estimated by its sample version $\Sigma_m=\tfrac1m\sum_{i=1}^m X_iX_i^{\mathsf T}$; if $X$ has zero mean these are the covariance and sample covariance matrices.

<a id="pdf-681b6f3d947f-p137-b005"></a>
<!-- pdf-source: page=137; block=5; confidence=0.95 -->
**Theorem 5.6.1 (General covariance estimation).** Let $X$ be a random vector in $\mathbb{R}^n$, $n\ge 2$. Assume for some $K\ge 1$ that $\|X\|_2\le K(\mathbb{E}\|X\|_2^2)^{1/2}$ almost surely (5.16). Then for every positive integer $m$,
$$\mathbb{E}\|\Sigma_m-\Sigma\|\le C\Big(\sqrt{\tfrac{K^2 n\log n}{m}}+\tfrac{K^2 n\log n}{m}\Big)\|\Sigma\|.$$

<a id="pdf-681b6f3d947f-p137-b006"></a>
<!-- pdf-source: page=137; block=6; confidence=0.93 -->
**Proof.** Since $\mathbb{E}\|X\|_2^2=\operatorname{tr}(\Sigma)$ (as in the proof of Lemma 3.2.4), assumption (5.16) becomes $\|X\|_2^2\le K^2\operatorname{tr}(\Sigma)$ almost surely (5.17). Apply the expectation version of matrix Bernstein (Exercise 5.4.11) to the i.i.d. mean-zero matrices $X_iX_i^{\mathsf T}-\Sigma$:
$$\mathbb{E}\|\Sigma_m-\Sigma\|=\tfrac1m\,\mathbb{E}\Big\|\sum_{i=1}^m (X_iX_i^{\mathsf T}-\Sigma)\Big\|\lesssim \tfrac1m\big(\sigma\sqrt{\log n}+M\log n\big).\quad(5.18)$$

<a id="pdf-681b6f3d947f-p138-b001"></a>
<!-- pdf-source: page=138; block=1; confidence=0.93 -->
Here $\sigma^2=\big\|\sum_{i=1}^m \mathbb{E}(X_iX_i^{\mathsf T}-\Sigma)^2\big\|=m\big\|\mathbb{E}(XX^{\mathsf T}-\Sigma)^2\big\|$ and $M$ satisfies $\|XX^{\mathsf T}-\Sigma\|\le M$ a.s. Bounding $\sigma^2$: expanding, $\mathbb{E}(XX^{\mathsf T}-\Sigma)^2=\mathbb{E}(XX^{\mathsf T})^2-\Sigma^2\preceq \mathbb{E}(XX^{\mathsf T})^2$ (5.19). By (5.17), $(XX^{\mathsf T})^2=\|X\|_2^2\,XX^{\mathsf T}\preceq K^2\operatorname{tr}(\Sigma)XX^{\mathsf T}$; taking expectation ($\mathbb{E}\,XX^{\mathsf T}=\Sigma$) gives $\mathbb{E}(XX^{\mathsf T})^2\preceq K^2\operatorname{tr}(\Sigma)\Sigma$, hence $\sigma^2\le K^2 m\operatorname{tr}(\Sigma)\|\Sigma\|$. Bounding $M$: $\|XX^{\mathsf T}-\Sigma\|\le \|X\|_2^2+\|\Sigma\|\le K^2\operatorname{tr}(\Sigma)+\|\Sigma\|\le 2K^2\operatorname{tr}(\Sigma)=:M$ (using $\|\Sigma\|\le\operatorname{tr}(\Sigma)$, $K\ge1$). Substituting into (5.18): $\mathbb{E}\|\Sigma_m-\Sigma\|\le \tfrac1m\big(\sqrt{K^2 m\operatorname{tr}(\Sigma)\|\Sigma\|}\,\sqrt{\log n}+2K^2\operatorname{tr}(\Sigma)\log n\big)$. Finish with $\operatorname{tr}(\Sigma)\le n\|\Sigma\|$ and simplify. $\blacksquare$

<a id="pdf-681b6f3d947f-p138-b002"></a>
<!-- pdf-source: page=138; block=2; confidence=0.94 -->
**Remark 5.6.2 (Sample complexity).** For any $\varepsilon\in(0,1)$, the relative-error guarantee $\mathbb{E}\|\Sigma_m-\Sigma\|\le\varepsilon\|\Sigma\|$ (5.20) holds with sample size $m\asymp \varepsilon^{-2}n\log n$. Compared with $m\asymp\varepsilon^{-2}n$ for sub-gaussian distributions (Remark 4.7.2), dropping the sub-gaussian requirement costs only a logarithmic oversampling factor.

<a id="pdf-681b6f3d947f-p139-b001"></a>
<!-- pdf-source: page=139; block=1; confidence=0.90 -->
**Section 5.6.** Covariance estimation for general distributions (running section header).

<a id="pdf-681b6f3d947f-p139-b002"></a>
<!-- pdf-source: page=139; block=2; confidence=0.90 -->
**Remark 5.6.3 (Lower-dimensional distributions).** Instead of the crude bound $\operatorname{tr}(\Sigma)\le n\|\Sigma\|$ used at the end of the proof of Theorem 5.6.1, one can bound in terms of the intrinsic dimension $r=\dfrac{\operatorname{tr}(\Sigma)}{\|\Sigma\|}$, giving
$$\mathbb{E}\|\Sigma_m-\Sigma\|\le C\left(\sqrt{\tfrac{K^2 r\log n}{m}}+\tfrac{K^2 r\log n}{m}\right)\|\Sigma\|.$$
Hence a sample of size $m\asymp \varepsilon^{-2} r\log n$ suffices to estimate $\Sigma$ as in (5.20). Since always $r\le n$, this bound is at least as good as Theorem 5.6.1; for approximately low-dimensional distributions $r\ll n$. (Stable dimension/rank revisited in Section 7.6.)

<a id="pdf-681b6f3d947f-p139-b003"></a>
<!-- pdf-source: page=139; block=3; confidence=0.92 -->
**Exercise 5.6.4 (Tail bound).** Show that for any $u\ge 0$,
$$\|\Sigma_m-\Sigma\|\le C\left(\sqrt{\tfrac{K^2 r(\log n+u)}{m}}+\tfrac{K^2 r(\log n+u)}{m}\right)\|\Sigma\|$$
with probability at least $1-2e^{-u}$, where $r=\operatorname{tr}(\Sigma)/\|\Sigma\|\le n$.

<a id="pdf-681b6f3d947f-p139-b004"></a>
<!-- pdf-source: page=139; block=4; confidence=0.95 -->
**Exercise 5.6.5 (Necessity of boundedness assumption).** Show that if the boundedness assumption (5.16) is dropped from Theorem 5.6.1, the conclusion may fail in general.

<a id="pdf-681b6f3d947f-p139-b005"></a>
<!-- pdf-source: page=139; block=5; confidence=0.92 -->
**Exercise 5.6.6 (Sampling from frames).** For an equal-norm tight frame $(u_i)_{i=1}^N$ in $\mathbb{R}^n$, state and prove that a random sample of $m\gtrsim n\log n$ of the $u_i$ forms a frame with good (arbitrarily close to tight) frame bounds, with quality independent of the frame size $N$.

<a id="pdf-681b6f3d947f-p139-b006"></a>
<!-- pdf-source: page=139; block=6; confidence=0.92 -->
**Exercise 5.6.7 (Necessity of logarithmic oversampling).** Show logarithmic oversampling is necessary in general: give a distribution in $\mathbb{R}^n$ for which bound (5.20) must fail for every $\varepsilon<1$ unless $m\gtrsim n\log n$. (Hint: coordinate distribution from Section 3.3.4; argue as in Exercise 5.4.14.)

<a id="pdf-681b6f3d947f-p139-b007"></a>
<!-- pdf-source: page=139; block=7; confidence=0.95 -->
Footnote: frames introduced in Section 3.3.4; an equal-norm frame means $\|u_i\|_2=\|u_j\|_2$ for all $i,j$.

<a id="pdf-681b6f3d947f-p140-b001"></a>
<!-- pdf-source: page=140; block=1; confidence=0.92 -->
**Exercise 5.6.8 (Random matrices with general independent rows).** Prove a version of Theorem 4.6.1 for arbitrary (not necessarily sub-gaussian) row distributions. Let $A$ be an $m\times n$ matrix with independent isotropic rows $A_i\in\mathbb{R}^n$ satisfying, for some $K\ge 0$,
$$\|A_i\|_2\le K\sqrt{n}\ \text{a.s. for every } i.\tag{5.21}$$
Prove that for every $t\ge 1$,
$$\sqrt{m}-Kt\sqrt{n\log n}\le s_n(A)\le s_1(A)\le \sqrt{m}+Kt\sqrt{n\log n}\tag{5.22}$$
with probability at least $1-2n^{-ct^2}$. (Hint: as in Theorem 4.6.1, derive from a bound on $\tfrac1m A^{\mathsf T}A-I_n=\tfrac1m\sum_{i=1}^m A_iA_i^{\mathsf T}-I_n$; use Exercise 5.6.4.)

<a id="pdf-681b6f3d947f-p140-b002"></a>
<!-- pdf-source: page=140; block=2; confidence=0.95 -->
**Section 5.7. Notes.** Bibliographic notes for Chapter 5.

<a id="pdf-681b6f3d947f-p140-b003"></a>
<!-- pdf-source: page=140; block=3; confidence=0.88 -->
Introductory texts on concentration: [11, Ch. 3], [150, 130, 129, 30], tutorial [13]. The isoperimetric approach (Section 5.1) originates with P. Lévy, to whom Theorems 5.1.5 and 5.1.4 are due [91]. V. Milman's 1970s work extended the concentration-of-measure principle (surveyed in Section 5.2); omitted approaches include bounded differences, martingale, semigroup and transportation methods, Poincaré and log-Sobolev inequalities, hypercontractivity, Stein's method, and Talagrand's inequalities [212, 129, 30]. Sections 5.1–5.2 material found in [11, Ch. 3], [150, 129].

<a id="pdf-681b6f3d947f-p140-b004"></a>
<!-- pdf-source: page=140; block=4; confidence=0.88 -->
Gaussian isoperimetric inequality (Theorem 5.2.1): first proved by Sudakov and Cirelson (Tsirelson) and independently by Borell [28]; other proofs [24, 12, 16]; elementary derivation of Gaussian concentration (Theorem 5.2.2) from Gaussian interpolation [167]. Concentration on the Hamming cube (Theorem 5.2.5) follows from Harper's isoperimetric theorem [98], see [25]; on the symmetric group (Theorem 5.2.6) due to Maurey [139]; both also provable via martingale methods [150, Ch. 7]. Concentration on positively curved Riemannian manifolds [129, Sec. 2.3, Prop. 2.17] yields special cases: Theorem 5.2.7 (special orthogonal group [150, Sec. 6.5.1]) and Theorem 5.2.9 (Grassmannian [150, Sec. 6.7.2]); Haar measure construction (Remark 5.2.8) in [150, Ch. 1].

<a id="pdf-681b6f3d947f-p141-b001"></a>
<!-- pdf-source: page=141; block=1; confidence=0.88 -->
(Continuing 5.7 Notes.) References [76, Ch. 2]; survey [147] on numerically stable generation of random unitary matrices. Concentration on the continuous cube (Theorem 5.2.10) in [129, Prop. 2.8]; Euclidean ball (Theorem 5.2.13) in [129, Prop. 2.9]; exponential densities (Theorem 5.2.15) from [129, Prop. 2.18]; Talagrand's concentration inequality (Theorem 5.2.16) in [198, Thm 6.6], [129, Cor. 4.10]. Johnson–Lindenstrauss Lemma original formulation [110]; versions and applications [138, Sec. 15.2]; the condition $m\gtrsim\varepsilon^{-2}\log N$ is optimal [124].

<a id="pdf-681b6f3d947f-p141-b002"></a>
<!-- pdf-source: page=141; block=2; confidence=0.86 -->
Matrix concentration approach of Section 5.4 originates in Ahlswede–Winter [4]; short proof of Golden–Thompson (Theorem 5.4.7) in [21, Thm 9.3.7], [221]; early applications [227, 220, 92, 159]. The original Ahlswede–Winter argument gives a weaker matrix Bernstein than Theorem 5.4.1, with $\sum_{i=1}^N\|\mathbb{E}X_i^2\|$ in place of $\sigma$; tightened by Oliveira [160] and independently by Tropp [206] using Lieb's inequality (Theorem 5.4.8) instead of Golden–Thompson. The book follows Tropp's proof of Theorem 5.4.1. Self-contained proofs of Lieb's inequality, matrix Hoeffding (Exercise 5.4.12), matrix Chernoff in [207]; also [165], [78, Sec. 8.5, App. B.6]. Exercise 5.4.11 alternatively via Gaussian integration by parts and a trace inequality [209]. Matrix Khintchine (Exercise 5.4.13) deducible from non-commutative Khintchine (Lust-Piquard [134]; [135, 40, 41, 172]), first used by Rudelson [175].

<a id="pdf-681b6f3d947f-p141-b003"></a>
<!-- pdf-source: page=141; block=3; confidence=0.86 -->
Community detection (Section 5.5): see Chapter 4 notes. The random-graph concentration via matrix Bernstein outlined in Section 5.5 was first proposed by Oliveira [160]. Covariance estimation for general high-dimensional distributions (Section 5.6) follows [222]; an alternative and earlier approach [continues on next page].

<a id="pdf-681b6f3d947f-p142-b001"></a>
<!-- pdf-source: page=142; block=1; confidence=0.90 -->
Closing notes: an alternative covariance-estimation approach with similar results relies on matrix (non-commutative) Khintchine inequalities, developed earlier by Rudelson [175]. Further references in the Chapter 4 notes. Exercise 5.6.8 is from [222, Section 5.4.2].

<a id="pdf-681b6f3d947f-p143-b001"></a>
<!-- pdf-source: page=143; block=1; confidence=0.95 -->
**Chapter 6. Quadratic forms, symmetrization and contraction.** Introduces decoupling (§6.1), the Hanson–Wright inequality for concentration of quadratic forms (§6.2), symmetrization (§6.4), and contraction (§6.7), with applications to anisotropic random vectors, distances to subspaces (§6.3), operator norm of random matrices (§6.5), and matrix completion (§6.6).

<a id="pdf-681b6f3d947f-p143-b002"></a>
<!-- pdf-source: page=143; block=2; confidence=0.95 -->
**Section 6.1 (Decoupling).** Extends the study of linear sums $\sum_{i=1}^n a_i X_i$ (6.1) to quadratic forms
$$\sum_{i,j=1}^n a_{ij} X_i X_j = X^{\mathsf T} A X = \langle X, AX\rangle \tag{6.2}$$
where $A=(a_{ij})$ is an $n\times n$ coefficient matrix and $X=(X_1,\dots,X_n)$ has independent coordinates; such a form is called a **chaos**. For $X_i$ with zero mean and unit variance,
$$\mathbb{E}\,X^{\mathsf T}AX = \sum_{i,j=1}^n a_{ij}\,\mathbb{E} X_i X_j = \sum_{i=1}^n a_{ii} = \operatorname{tr} A.$$

<a id="pdf-681b6f3d947f-p144-b001"></a>
<!-- pdf-source: page=144; block=1; confidence=0.94 -->
Concentration of a chaos is hard because the terms of (6.2) are dependent. Decoupling replaces the quadratic form by the **bilinear form** $\sum_{i,j} a_{ij} X_i X_j' = X^{\mathsf T} A X' = \langle X, AX'\rangle$, where $X'$ is an **independent copy** of $X$ (independent of $X$, same distribution). Conditioning on $X'$ makes it a sum of independent terms $\sum_i c_i X_i$ with $c_i = \sum_j a_{ij} X_j'$, reducing to the linear case (6.1).

<a id="pdf-681b6f3d947f-p144-b002"></a>
<!-- pdf-source: page=144; block=2; confidence=0.96 -->
**Theorem 6.1.1 (Decoupling).** Let $A$ be an $n\times n$ diagonal-free matrix (zero diagonal), and $X=(X_1,\dots,X_n)$ a random vector with independent mean-zero coordinates. Then for every convex $F:\mathbb{R}\to\mathbb{R}$,
$$\mathbb{E}\,F(X^{\mathsf T}AX) \le \mathbb{E}\,F(4\,X^{\mathsf T}AX') \tag{6.3}$$
where $X'$ is an independent copy of $X$.

<a id="pdf-681b6f3d947f-p144-b003"></a>
<!-- pdf-source: page=144; block=3; confidence=0.96 -->
**Lemma 6.1.2.** Let $Y,Z$ be independent random variables with $\mathbb{E} Z = 0$. Then for every convex $F$, $\mathbb{E}\,F(Y) \le \mathbb{E}\,F(Y+Z)$.

<a id="pdf-681b6f3d947f-p144-b004"></a>
<!-- pdf-source: page=144; block=4; confidence=0.93 -->
**Proof.** By Jensen's inequality: for fixed $y$, using $\mathbb{E} Z=0$, $F(y)=F(y+\mathbb{E} Z)=F(\mathbb{E}[y+Z])\le \mathbb{E}\,F(y+Z)$. Set $y=Y$ and take expectations (independence of $Y,Z$ is used here). $\square$

<a id="pdf-681b6f3d947f-p144-b005"></a>
<!-- pdf-source: page=144; block=5; confidence=0.90 -->
**Proof of Decoupling Theorem 6.1.1.** Outline: replace the chaos $X^{\mathsf T}AX=\sum_{i,j} a_{ij}X_iX_j$ by the **partial chaos** $\sum_{(i,j)\in I\times I^c} a_{ij}X_iX_j$, where the index subset $I\subset\{1,\dots,n\}$ is chosen by random sampling. (Proof continues beyond supplied pages.)

<a id="pdf-681b6f3d947f-p145-b001"></a>
<!-- pdf-source: page=145; block=1; confidence=0.95 -->
**Proof (continued).** Partial chaos sums over disjoint index sets for $i$ and $j$, so $X_j$ can be replaced by $X'_j$ without changing the distribution; the partial chaos is then completed to $X^T A X' = \sum_{i,j} a_{ij} X_i X'_j$ via Lemma 6.1.2.

Introduce selectors $\delta_1,\dots,\delta_n \in \{0,1\}$, independent Bernoulli with $P\{\delta_i=0\}=P\{\delta_i=1\}=1/2$, and set $I := \{i : \delta_i = 1\}$. Condition on $X$. Since $a_{ii}=0$ and $\mathbb{E}\,\delta_i(1-\delta_j) = \tfrac12\cdot\tfrac12 = \tfrac14$ for all $i\neq j$,
$$X^T A X = \sum_{i\neq j} a_{ij}X_iX_j = 4\,\mathbb{E}_\delta \sum_{i\neq j}\delta_i(1-\delta_j)a_{ij}X_iX_j = 4\,\mathbb{E}_I \sum_{(i,j)\in I\times I^c} a_{ij}X_iX_j.$$

<a id="pdf-681b6f3d947f-p145-b002"></a>
<!-- pdf-source: page=145; block=2; confidence=0.95 -->
**Proof (continued).** Applying $F$ and taking expectation over $X$, Jensen's inequality and Fubini give
$$\mathbb{E}_X F(X^T A X) \le \mathbb{E}_I \mathbb{E}_X F\!\Big(4\sum_{(i,j)\in I\times I^c} a_{ij}X_iX_j\Big).$$
Hence there exists a realization of $I$ with $\mathbb{E}_X F(X^T A X) \le \mathbb{E}_X F\big(4\sum_{(i,j)\in I\times I^c} a_{ij}X_iX_j\big)$; fix it and drop the $X$ subscript. Since $(X_i)_{i\in I}$ are independent of $(X_j)_{j\in I^c}$, replacing $X_j$ by $X'_j$ leaves the distribution unchanged:
$$\mathbb{E} F(X^T A X) \le \mathbb{E} F\!\Big(4\sum_{(i,j)\in I\times I^c} a_{ij}X_iX'_j\Big).$$
It remains to complete the sum to all index pairs, i.e. to show (with $[n]=\{1,\dots,n\}$)
$$\mathbb{E} F\!\Big(4\sum_{(i,j)\in I\times I^c} a_{ij}X_iX'_j\Big) \le \mathbb{E} F\!\Big(4\sum_{(i,j)\in [n]\times[n]} a_{ij}X_iX'_j\Big). \tag{6.4}$$

<a id="pdf-681b6f3d947f-p146-b001"></a>
<!-- pdf-source: page=146; block=1; confidence=0.95 -->
**Proof (continued).** Decompose $\sum_{(i,j)\in[n]\times[n]} a_{ij}X_iX'_j = Y + Z_1 + Z_2$ where
$$Y=\!\!\sum_{(i,j)\in I\times I^c}\!\! a_{ij}X_iX'_j,\quad Z_1=\!\!\sum_{(i,j)\in I\times I}\!\! a_{ij}X_iX'_j,\quad Z_2=\!\!\sum_{(i,j)\in I^c\times[n]}\!\! a_{ij}X_iX'_j.$$
Condition on all variables except $(X'_j)_{j\in I}$ and $(X_i)_{i\in I^c}$: this fixes $Y$, while $Z_1,Z_2$ have zero conditional expectation. By Lemma 6.1.2, the conditional expectation $\mathbb{E}'$ satisfies $F(4Y) \le \mathbb{E}' F(4Y+4Z_1+4Z_2)$. Taking expectation over the remaining variables gives $\mathbb{E} F(4Y) \le \mathbb{E} F(4Y+4Z_1+4Z_2)$, proving (6.4). $\blacksquare$

<a id="pdf-681b6f3d947f-p146-b002"></a>
<!-- pdf-source: page=146; block=2; confidence=0.95 -->
**Remark 6.1.3.** A slightly stronger decoupling was proved: $A$ need not be diagonal-free. For any square matrix $A=(a_{ij})$,
$$\mathbb{E} F\!\Big(\sum_{i,j:\,i\neq j} a_{ij}X_iX_j\Big) \le \mathbb{E} F\!\Big(4\sum_{i,j} a_{ij}X_iX'_j\Big).$$

<a id="pdf-681b6f3d947f-p146-b003"></a>
<!-- pdf-source: page=146; block=3; confidence=0.95 -->
**Exercise 6.1.4 (Decoupling in Hilbert spaces).** Let $A=(a_{ij})$ be $n\times n$ and $X_1,\dots,X_n$ independent, mean zero random vectors in a Hilbert space. Show that for every convex $F:\mathbb{R}\to\mathbb{R}$,
$$\mathbb{E} F\!\Big(\sum_{i,j:\,i\neq j} a_{ij}\langle X_i, X_j\rangle\Big) \le \mathbb{E} F\!\Big(4\sum_{i,j} a_{ij}\langle X_i, X'_j\rangle\Big),$$
where $(X'_i)$ is an independent copy of $(X_i)$.

<a id="pdf-681b6f3d947f-p146-b004"></a>
<!-- pdf-source: page=146; block=4; confidence=0.95 -->
**Exercise 6.1.5 (Decoupling in normed spaces).** Let $(u_{ij})_{i,j=1}^n$ be fixed vectors in a normed space and $X_1,\dots,X_n$ independent, mean zero random variables. Show that for every convex increasing $F$,
$$\mathbb{E} F\!\Big(\Big\|\sum_{i,j:\,i\neq j} X_iX_j u_{ij}\Big\|\Big) \le \mathbb{E} F\!\Big(4\Big\|\sum_{i,j} X_iX'_j u_{ij}\Big\|\Big),$$
where $(X'_i)$ is an independent copy of $(X_i)$.

<a id="pdf-681b6f3d947f-p147-b001"></a>
<!-- pdf-source: page=147; block=1; confidence=0.97 -->
**6.2 Hanson-Wright Inequality.** A general concentration inequality for a chaos, viewable as a chaos version of Bernstein's inequality.

<a id="pdf-681b6f3d947f-p147-b002"></a>
<!-- pdf-source: page=147; block=2; confidence=0.97 -->
**Theorem 6.2.1 (Hanson-Wright inequality).** Let $X=(X_1,\dots,X_n)\in\mathbb{R}^n$ have independent, mean zero, sub-gaussian coordinates, and let $A$ be an $n\times n$ matrix. Then for every $t\ge 0$,
$$P\big\{ |X^T A X - \mathbb{E}\,X^T A X| \ge t \big\} \le 2\exp\!\Big[-c\,\min\Big(\tfrac{t^2}{K^4\|A\|_F^2},\ \tfrac{t}{K^2\|A\|}\Big)\Big],$$
where $K=\max_i \|X_i\|_{\psi_2}$.

<a id="pdf-681b6f3d947f-p147-b003"></a>
<!-- pdf-source: page=147; block=3; confidence=0.90 -->
Proof outline: bound the MGF of $X^T A X$; use decoupling to replace it by $X^T A X'$; bound the decoupled MGF in the Gaussian case $X\sim N(0,I_n)$; then extend to general sub-gaussian distributions by a replacement trick.

<a id="pdf-681b6f3d947f-p147-b004"></a>
<!-- pdf-source: page=147; block=4; confidence=0.97 -->
**Lemma 6.2.2 (MGF of Gaussian chaos).** Let $X,X'\sim N(0,I_n)$ be independent and $A=(a_{ij})$ an $n\times n$ matrix. Then
$$\mathbb{E}\exp(\lambda X^T A X') \le \exp(C\lambda^2\|A\|_F^2)$$
for all $\lambda$ with $|\lambda|\le c/\|A\|$.

<a id="pdf-681b6f3d947f-p147-b005"></a>
<!-- pdf-source: page=147; block=5; confidence=0.93 -->
**Proof.** By rotation invariance reduce to diagonal $A$. Using the SVD $A=\sum_i s_i u_i v_i^T$,
$$X^T A X' = \sum_i s_i \langle u_i, X\rangle\langle v_i, X'\rangle.$$
By rotation invariance of the normal distribution, $g:=(\langle u_i,X\rangle)_{i=1}^n$ and $g':=(\langle v_i,X'\rangle)_{i=1}^n$ are independent standard normal vectors in $\mathbb{R}^n$ (Exercise 3.3.3), so $X^T A X' = \sum_i s_i g_i g'_i$ with $g,g'\sim N(0,I_n)$ independent and $s_i$ the singular values of $A$. By independence,
$$\mathbb{E}\exp(\lambda X^T A X') = \prod_i \mathbb{E}\exp(\lambda s_i g_i g'_i). \tag{6.5}$$
For each $i$, $\mathbb{E}\exp(\lambda s_i g_i g'_i) = \mathbb{E}\exp(\lambda^2 s_i^2 g_i^2/2) \le \exp(C\lambda^2 s_i^2)$ provided $\lambda^2 s_i^2 \le c$.

<a id="pdf-681b6f3d947f-p148-b001"></a>
<!-- pdf-source: page=148; block=1; confidence=0.90 -->
**Proof (concl.).** The first identity follows by conditioning on $g_i$ and applying the normal MGF formula (2.12) to $g_i'$; the second step uses Proposition 2.7.1(c) for the sub-exponential $g_i^2$. Substituting into (6.5) gives
$$\mathbb{E}\exp(\lambda X^\top A X') \le \exp\Big(C\lambda^2 \sum_i s_i^2\Big)$$
provided $\lambda^2 \le c/\max_i s_i^2$. Since the $s_i$ are the singular values of $A$, $\sum_i s_i^2 = \|A\|_F^2$ and $\max_i s_i = \|A\|$, proving the lemma.

<a id="pdf-681b6f3d947f-p148-b002"></a>
<!-- pdf-source: page=148; block=2; confidence=0.95 -->
A replacement trick is used to compare the MGFs of general and Gaussian chaoses, extending Lemma 6.2.2 to general distributions.

<a id="pdf-681b6f3d947f-p148-b003"></a>
<!-- pdf-source: page=148; block=3; confidence=0.97 -->
**Lemma 6.2.3 (Comparison).** Let $X, X'$ be independent, mean-zero, sub-gaussian random vectors in $\mathbb{R}^n$ with $\|X\|_{\psi_2} \le K$ and $\|X'\|_{\psi_2} \le K$, and let $g, g' \sim N(0, I_n)$ be independent. For any $n\times n$ matrix $A$ and any $\lambda \in \mathbb{R}$,
$$\mathbb{E}\exp(\lambda X^\top A X') \le \mathbb{E}\exp(CK^2\lambda\, g^\top A g').$$

<a id="pdf-681b6f3d947f-p148-b004"></a>
<!-- pdf-source: page=148; block=4; confidence=0.92 -->
**Proof.** Condition on $X'$ and take $\mathbb{E}_X$. Then $X^\top A X' = \langle X, AX'\rangle$ is conditionally sub-gaussian with norm $\le K\|AX'\|_2$, so the sub-gaussian MGF bound (2.16) gives
$$\mathbb{E}_X \exp(\lambda X^\top A X') \le \exp(C\lambda^2 K^2 \|AX'\|_2^2),\quad \lambda\in\mathbb{R}. \tag{6.6}$$
The normal MGF formula (2.12) applied to $g^\top A X' = \langle g, AX'\rangle$ (conditional on $X'$) gives
$$\mathbb{E}_g \exp(\mu g^\top A X') = \exp(\mu^2 \|AX'\|_2^2/2),\quad \mu\in\mathbb{R}. \tag{6.7}$$
Choosing $\mu = \sqrt{2}\,CK\lambda$ matches the right sides of (6.6) and (6.7), yielding $\mathbb{E}_X \exp(\lambda X^\top A X') \le \mathbb{E}_g \exp(\sqrt{2}\,CK\lambda\, g^\top A X')$. Taking $\mathbb{E}_{X'}$ replaces $X$ by $g$ at a cost of a factor $\sqrt{2}\,CK$; repeating the argument for $X'$ replaces it by $g'$ at another factor $\sqrt{2}\,CK$ (details in Exercise 6.2.4). $\square$

<a id="pdf-681b6f3d947f-p148-b005"></a>
<!-- pdf-source: page=148; block=5; confidence=0.95 -->
**Exercise 6.2.4.** Complete the proof of Lemma 6.2.3 by carefully replacing $X'$ with $g'$.

<a id="pdf-681b6f3d947f-p149-b001"></a>
<!-- pdf-source: page=149; block=1; confidence=0.95 -->
**Proof of Theorem 6.2.1.** WLOG $K=1$. It suffices to bound the upper tail $p := \mathbb{P}\{X^\top A X - \mathbb{E}\,X^\top A X \ge t\}$; the lower tail follows by replacing $A$ with $-A$, and combining completes the proof. With $A=(a_{ij})_{i,j=1}^n$, using mean-zero and independence,
$$X^\top A X = \sum_{i,j} a_{ij}X_iX_j,\qquad \mathbb{E}\,X^\top A X = \sum_i a_{ii}\,\mathbb{E}\,X_i^2,$$
so the deviation is $\sum_i a_{ii}(X_i^2 - \mathbb{E}\,X_i^2) + \sum_{i\ne j} a_{ij}X_iX_j$. Hence $p \le p_1 + p_2$ where $p_1 = \mathbb{P}\{\sum_i a_{ii}(X_i^2-\mathbb{E}\,X_i^2) \ge t/2\}$ (diagonal) and $p_2 = \mathbb{P}\{\sum_{i\ne j} a_{ij}X_iX_j \ge t/2\}$ (off-diagonal).

<a id="pdf-681b6f3d947f-p149-b002"></a>
<!-- pdf-source: page=149; block=2; confidence=0.93 -->
**Step 1 (diagonal sum).** The $X_i^2 - \mathbb{E}\,X_i^2$ are independent, mean-zero, sub-exponential with $\|X_i^2 - \mathbb{E}\,X_i^2\|_{\psi_1} \lesssim \|X_i^2\|_{\psi_1} \lesssim \|X_i\|_{\psi_2}^2 \lesssim 1$ (Centering Exercise 2.7.10, Lemma 2.7.6). Bernstein's inequality (Theorem 2.8.2) gives
$$p_1 \le \exp\Big[-c\min\Big(\tfrac{t^2}{\sum_i a_{ii}^2}, \tfrac{t}{\max_i|a_{ii}|}\Big)\Big] \le \exp\Big[-c\min\Big(\tfrac{t^2}{\|A\|_F^2}, \tfrac{t}{\|A\|}\Big)\Big].$$

<a id="pdf-681b6f3d947f-p149-b003"></a>
<!-- pdf-source: page=149; block=3; confidence=0.92 -->
**Step 2 (off-diagonal sum).** Let $S := \sum_{i\ne j} a_{ij}X_iX_j$ and $\lambda > 0$. By Markov,
$$p_2 = \mathbb{P}\{S \ge t/2\} = \mathbb{P}\{\lambda S \ge \lambda t/2\} \le \exp(-\lambda t/2)\,\mathbb{E}\exp(\lambda S). \tag{6.8}$$
Then
$$\mathbb{E}\exp(\lambda S) \le \mathbb{E}\exp(4\lambda X^\top A X') \ (\text{decoupling, Remark 6.1.3}) \le \mathbb{E}\exp(C_1\lambda\, g^\top A g') \ (\text{Comparison Lemma 6.2.3}) \le \exp(C\lambda^2\|A\|_F^2) \ (\text{Lemma 6.2.2}).$$

<a id="pdf-681b6f3d947f-p150-b001"></a>
<!-- pdf-source: page=150; block=1; confidence=0.92 -->
**Proof (concl.).** The last bound holds for $|\lambda| \le c/\|A\|$. Substituting into (6.8), $p_2 \le \exp(-\lambda t/2 + C\lambda^2\|A\|_F^2)$. Optimizing over $0 \le \lambda \le c/\|A\|$ yields
$$p_2 \le \exp\Big[-c\min\Big(\tfrac{t^2}{\|A\|_F^2}, \tfrac{t}{\|A\|}\Big)\Big].$$
Combining $p_1$ and $p_2$ completes the proof of Theorem 6.2.1. (Footnote: adding upper and lower tail bounds gives a factor 4 rather than 2 in front; the 4 can be reduced to 2 by lowering the exponent constant $c$.) $\square$

<a id="pdf-681b6f3d947f-p150-b002"></a>
<!-- pdf-source: page=150; block=2; confidence=0.95 -->
**Exercise 6.2.5.** Give an alternative proof of Hanson–Wright for normal distributions without separating the diagonal part or decoupling. Hint: use the SVD of $A$ and rotation invariance of $X\sim N(0,I_n)$ to simplify $X^\top A X$.

<a id="pdf-681b6f3d947f-p150-b003"></a>
<!-- pdf-source: page=150; block=3; confidence=0.95 -->
**Exercise 6.2.6.** For a mean-zero sub-gaussian vector $X\in\mathbb{R}^n$ with $\|X\|_{\psi_2}\le K$ and an $m\times n$ matrix $B$, show
$$\mathbb{E}\exp(\lambda^2\|BX\|_2^2) \le \exp(CK^2\lambda^2\|B\|_F^2)\quad\text{for }|\lambda|\le c/(K\|B\|),$$
via replacing $X$ by $g\sim N(0,I_m)$: (a) prove $\mathbb{E}\exp(\lambda^2\|BX\|_2^2) \le \mathbb{E}\exp(CK^2\lambda^2\|B^\top g\|_2^2)$ for all $\lambda$ (like Lemma 6.2.3); (b) check $\mathbb{E}\exp(\lambda^2\|B^\top g\|_2^2) \le \exp(C\lambda^2\|B\|_F^2)$ for $|\lambda|\le c/\|B\|$ (like Lemma 6.2.2).

<a id="pdf-681b6f3d947f-p150-b004"></a>
<!-- pdf-source: page=150; block=4; confidence=0.93 -->
**Exercise 6.2.7.** For independent, mean-zero, sub-gaussian vectors $X_1,\dots,X_n\in\mathbb{R}^d$ and an $n\times n$ matrix $A=(a_{ij})$, prove that for every $t\ge 0$,
$$\mathbb{P}\Big\{\Big|\sum_{i\ne j} a_{ij}\langle X_i, X_j\rangle\Big| \ge t\Big\} \le 2\exp\Big[-c\min\Big(\tfrac{t^2}{K^4 d\|A\|_F^2}, \tfrac{t}{K^2\|A\|}\Big)\Big],\quad K=\max_i\|X_i\|_{\psi_2}.$$
Hint: represent the form as $X^\top A X$ with $X$ a $d\times n$ random matrix.

<a id="pdf-681b6f3d947f-p151-b001"></a>
<!-- pdf-source: page=151; block=1; confidence=0.90 -->
Continuation of an exercise from the previous page: for the matrix with columns $X_i$, redo the MGF computation for the Gaussian case (Lemma 6.2.2) and the Comparison Lemma 6.2.3.

<a id="pdf-681b6f3d947f-p151-b002"></a>
<!-- pdf-source: page=151; block=2; confidence=0.98 -->
## 6.3 Concentration of anisotropic random vectors

<a id="pdf-681b6f3d947f-p151-b003"></a>
<!-- pdf-source: page=151; block=3; confidence=0.95 -->
Using the Hanson–Wright inequality, concentration is derived for anisotropic random vectors of the form $BX$, where $B$ is a fixed matrix and $X$ is isotropic.

<a id="pdf-681b6f3d947f-p151-b004"></a>
<!-- pdf-source: page=151; block=4; confidence=0.95 -->
**Exercise 6.3.1.** For $B$ an $m\times n$ matrix and $X$ isotropic in $\mathbb{R}^n$, verify $\mathbb{E}\,\|BX\|_2^2 = \|B\|_F^2$.

<a id="pdf-681b6f3d947f-p151-b005"></a>
<!-- pdf-source: page=151; block=5; confidence=0.97 -->
**Theorem 6.3.2 (Concentration of random vectors).** Let $B$ be an $m\times n$ matrix and $X=(X_1,\dots,X_n)\in\mathbb{R}^n$ have independent, mean zero, unit variance, sub-gaussian coordinates. Then
$$\big\|\,\|BX\|_2 - \|B\|_F\,\big\|_{\psi_2} \le CK^2\|B\|,$$
where $K=\max_i\|X_i\|_{\psi_2}$.

<a id="pdf-681b6f3d947f-p151-b006"></a>
<!-- pdf-source: page=151; block=6; confidence=0.95 -->
For $B=I_n$ the result reduces to $\big\|\,\|X\|_2 - \sqrt{n}\,\big\|_{\psi_2} \le CK^2$, previously proved as Theorem 3.1.1.

<a id="pdf-681b6f3d947f-p151-b007"></a>
<!-- pdf-source: page=151; block=7; confidence=0.95 -->
**Proof of Theorem 6.3.2.** Assume WLOG $K\ge 1$. Apply Hanson–Wright (Theorem 6.2.1) to $A:=B^{\mathsf T}B$, using $X^{\mathsf T}AX=\|BX\|_2^2$, $\mathbb{E}\,X^{\mathsf T}AX=\|B\|_F^2$, $\|A\|=\|B\|^2$, and $\|A\|_F=\|B^{\mathsf T}B\|_F\le\|B^{\mathsf T}\|\|B\|_F=\|B\|\|B\|_F$ (Exercise 6.3.3). Then for every $u\ge 0$,
$$\mathbb{P}\big\{|\|BX\|_2^2-\|B\|_F^2|\ge u\big\}\le 2\exp\!\left[-\frac{c}{K^4}\min\!\left(\frac{u^2}{\|B\|^2\|B\|_F^2},\frac{u}{\|B\|^2}\right)\right]$$
(using $K^4\ge K^2$ since $K\ge 1$). Substituting $u=\varepsilon\|B\|_F^2$, $\varepsilon\ge 0$, gives
$$\mathbb{P}\big\{|\|BX\|_2^2-\|B\|_F^2|\ge\varepsilon\|B\|_F^2\big\}\le 2\exp\!\left[-c\,\min(\varepsilon^2,\varepsilon)\,\frac{\|B\|_F^2}{K^4\|B\|^2}\right].$$

<a id="pdf-681b6f3d947f-p152-b001"></a>
<!-- pdf-source: page=152; block=1; confidence=0.95 -->
**Proof (continued).** From the bound on $\|BX\|_2^2$, deduce one for $\|BX\|_2$. Set $\delta^2=\min(\varepsilon^2,\varepsilon)$, equivalently $\varepsilon=\max(\delta,\delta^2)$. The implication holds: if $|\|BX\|_2-\|B\|_F|\ge\delta\|B\|_F$ then $|\|BX\|_2^2-\|B\|_F^2|\ge\varepsilon\|B\|_F^2$ (as in inequality (3.2), dividing by $\|B\|_F^2$). Hence
$$\mathbb{P}\big\{|\|BX\|_2-\|B\|_F|\ge\delta\|B\|_F\big\}\le 2\exp\!\left(-c\delta^2\frac{\|B\|_F^2}{K^4\|B\|^2}\right).$$
Changing variables $t=\delta\|B\|_F$ yields, for all $t\ge 0$,
$$\mathbb{P}\big\{|\|BX\|_2-\|B\|_F|>t\big\}\le 2\exp\!\left(-\frac{ct^2}{K^4\|B\|^2}\right),$$
and the theorem follows from the definition of sub-gaussian distributions. $\square$

<a id="pdf-681b6f3d947f-p152-b002"></a>
<!-- pdf-source: page=152; block=2; confidence=0.96 -->
**Exercise 6.3.3.** For $D$ a $k\times m$ matrix and $B$ an $m\times n$ matrix, prove $\|DB\|_F\le\|D\|\|B\|_F$.

<a id="pdf-681b6f3d947f-p152-b003"></a>
<!-- pdf-source: page=152; block=3; confidence=0.95 -->
**Exercise 6.3.4 (Distance to a subspace).** Let $E\subseteq\mathbb{R}^n$ be a subspace of dimension $d$, and $X=(X_1,\dots,X_n)$ have independent, mean zero, unit variance, sub-gaussian coordinates. (a) Show $(\mathbb{E}\,\mathrm{dist}(X,E)^2)^{1/2}=\sqrt{n-d}$. (b) Prove for $t\ge 0$: $\mathbb{P}\{|d(X,E)-\sqrt{n-d}|>t\}\le 2\exp(-ct^2/K^4)$, with $K=\max_i\|X_i\|_{\psi_2}$.

<a id="pdf-681b6f3d947f-p152-b004"></a>
<!-- pdf-source: page=152; block=4; confidence=0.90 -->
A weaker form of Theorem 6.3.2 is stated next, dropping the independence assumption on the coordinates of $X$.

<a id="pdf-681b6f3d947f-p152-b005"></a>
<!-- pdf-source: page=152; block=5; confidence=0.95 -->
**Exercise 6.3.5 (Tails of sub-gaussian random vectors).** Let $B$ be an $m\times n$ matrix and $X$ a mean zero, sub-gaussian random vector in $\mathbb{R}^n$ with $\|X\|_{\psi_2}\le K$. Prove for $t\ge 0$:
$$\mathbb{P}\{\|BX\|_2\ge CK\|B\|_F+t\}\le\exp\!\left(-\frac{ct^2}{K^2\|B\|^2}\right).$$
Hint: use the MGF bound from Exercise 6.2.6.

<a id="pdf-681b6f3d947f-p152-b006"></a>
<!-- pdf-source: page=152; block=6; confidence=0.90 -->
The next exercise shows why concentration must be weaker than Theorem 3.1.1 when independence of coordinates is not assumed.

<a id="pdf-681b6f3d947f-p153-b001"></a>
<!-- pdf-source: page=153; block=1; confidence=0.95 -->
**Exercise 6.3.6.** Show there exists a mean zero, isotropic, sub-gaussian random vector $X$ in $\mathbb{R}^n$ with $\mathbb{P}\{\|X\|_2=0\}=\mathbb{P}\{\|X\|_2\ge 1.4\sqrt{n}\}=\tfrac12$; i.e. $\|X\|_2$ does not concentrate near $\sqrt{n}$.

<a id="pdf-681b6f3d947f-p153-b002"></a>
<!-- pdf-source: page=153; block=2; confidence=0.98 -->
## 6.4 Symmetrization

<a id="pdf-681b6f3d947f-p153-b003"></a>
<!-- pdf-source: page=153; block=3; confidence=0.95 -->
**Definition.** $X$ is *symmetric* if $X$ and $-X$ have the same distribution. The symmetric Bernoulli variable $\xi$ satisfies $\mathbb{P}\{\xi=1\}=\mathbb{P}\{\xi=-1\}=\tfrac12$. A mean zero normal $X\sim N(0,\sigma^2)$ is symmetric; Poisson and exponential variables are not.

<a id="pdf-681b6f3d947f-p153-b004"></a>
<!-- pdf-source: page=153; block=4; confidence=0.93 -->
Symmetrization reduces problems about arbitrary distributions to symmetric ones, sometimes to the symmetric Bernoulli distribution.

<a id="pdf-681b6f3d947f-p153-b005"></a>
<!-- pdf-source: page=153; block=5; confidence=0.95 -->
**Exercise 6.4.1 (Constructing symmetric distributions).** Let $X$ be a random variable and $\xi$ an independent symmetric Bernoulli. (a) Show $\xi X$ and $\xi|X|$ are symmetric with the same distribution. (b) If $X$ is symmetric, show $\xi X$ and $\xi|X|$ have the same distribution as $X$. (c) For $X'$ an independent copy of $X$, show $X-X'$ is symmetric.

<a id="pdf-681b6f3d947f-p153-b006"></a>
<!-- pdf-source: page=153; block=6; confidence=0.95 -->
Notation: $\varepsilon_1,\varepsilon_2,\varepsilon_3,\dots$ denotes a sequence of independent symmetric Bernoulli variables, jointly independent of each other and of all other random variables considered.

<a id="pdf-681b6f3d947f-p153-b007"></a>
<!-- pdf-source: page=153; block=7; confidence=0.97 -->
**Lemma 6.4.2 (Symmetrization).** Let $X_1,\dots,X_N$ be independent, mean zero random vectors in a normed space. Then
$$\tfrac12\,\mathbb{E}\Big\|\sum_{i=1}^N \varepsilon_i X_i\Big\| \le \mathbb{E}\Big\|\sum_{i=1}^N X_i\Big\| \le 2\,\mathbb{E}\Big\|\sum_{i=1}^N \varepsilon_i X_i\Big\|.$$
The lemma lets one replace general $X_i$ by the symmetric $\varepsilon_i X_i$.

<a id="pdf-681b6f3d947f-p154-b001"></a>
<!-- pdf-source: page=154; block=1; confidence=0.95 -->
**Proof (upper bound).** Let $(X_i')$ be an independent copy of $(X_i)$. Since $\sum_i X_i'$ has zero mean, $p := \mathbb{E}\lVert\sum_i X_i\rVert \le \mathbb{E}\lVert\sum_i (X_i - X_i')\rVert$, using the version of Lemma 6.1.2: for independent $Y,Z$ with $\mathbb{E}Z=0$,
$$\mathbb{E}\lVert Y\rVert \le \mathbb{E}\lVert Y+Z\rVert. \tag{6.9}$$
Since $X_i - X_i'$ is symmetric, it has the same distribution as $\varepsilon_i(X_i - X_i')$ (Exercise 6.4.1). Hence $p \le \mathbb{E}\lVert\sum_i \varepsilon_i(X_i - X_i')\rVert \le \mathbb{E}\lVert\sum_i \varepsilon_i X_i\rVert + \mathbb{E}\lVert\sum_i \varepsilon_i X_i'\rVert = 2\,\mathbb{E}\lVert\sum_i \varepsilon_i X_i\rVert$ (triangle inequality; the two terms are identically distributed).

<a id="pdf-681b6f3d947f-p154-b002"></a>
<!-- pdf-source: page=154; block=2; confidence=0.96 -->
**Proof (lower bound).** By a similar argument, conditioning on $(\varepsilon_i)$ and applying (6.9),
$$\mathbb{E}\Big\lVert\sum_i \varepsilon_i X_i\Big\rVert \le \mathbb{E}\Big\lVert\sum_i \varepsilon_i(X_i - X_i')\Big\rVert = \mathbb{E}\Big\lVert\sum_i (X_i - X_i')\Big\rVert \le \mathbb{E}\Big\lVert\sum_i X_i\Big\rVert + \mathbb{E}\Big\lVert\sum_i X_i'\Big\rVert = 2\,\mathbb{E}\Big\lVert\sum_i X_i\Big\rVert,$$
using identical distribution of $X_i - X_i'$ and $\varepsilon_i(X_i-X_i')$, the triangle inequality, and identical distribution of $(X_i)$ and $(X_i')$. This completes the proof of the symmetrization lemma.

<a id="pdf-681b6f3d947f-p154-b003"></a>
<!-- pdf-source: page=154; block=3; confidence=0.95 -->
**Exercise 6.4.3.** Identify where the independence of the $X_i$ was used in the argument, and whether the mean-zero assumption is needed for both the upper and lower bounds.

<a id="pdf-681b6f3d947f-p154-b004"></a>
<!-- pdf-source: page=154; block=4; confidence=0.95 -->
**Exercise 6.4.4.** (a) Prove the generalization of Symmetrization Lemma 6.4.2 for random vectors $X_i$ without zero mean:
$$\mathbb{E}\Big\lVert \sum_{i=1}^N X_i - \sum_{i=1}^N \mathbb{E}X_i \Big\rVert \le 2\,\mathbb{E}\Big\lVert \sum_{i=1}^N \varepsilon_i X_i \Big\rVert.$$
(b) Argue that no non-trivial reverse inequality can hold.

<a id="pdf-681b6f3d947f-p155-b001"></a>
<!-- pdf-source: page=155; block=1; confidence=0.96 -->
**Exercise 6.4.5.** Let $F:\mathbb{R}_+ \to \mathbb{R}$ be increasing and convex. Show the inequalities of Lemma 6.4.2 hold with $\lVert\cdot\rVert$ replaced by $F(\lVert\cdot\rVert)$:
$$\mathbb{E}F\Big(\tfrac12\Big\lVert\sum_{i=1}^N \varepsilon_i X_i\Big\rVert\Big) \le \mathbb{E}F\Big(\Big\lVert\sum_{i=1}^N X_i\Big\rVert\Big) \le \mathbb{E}F\Big(2\Big\lVert\sum_{i=1}^N \varepsilon_i X_i\Big\rVert\Big).$$

<a id="pdf-681b6f3d947f-p155-b002"></a>
<!-- pdf-source: page=155; block=2; confidence=0.95 -->
**Exercise 6.4.6.** Let $X_1,\dots,X_N$ be independent, mean zero random variables. Show $\sum_i X_i$ is sub-gaussian iff $\sum_i \varepsilon_i X_i$ is sub-gaussian, and
$$c\Big\lVert\sum_{i=1}^N \varepsilon_i X_i\Big\rVert_{\psi_2} \le \Big\lVert\sum_{i=1}^N X_i\Big\rVert_{\psi_2} \le C\Big\lVert\sum_{i=1}^N \varepsilon_i X_i\Big\rVert_{\psi_2}.$$
Hint: apply Exercise 6.4.5 with $F(x)=\exp(\lambda x)$ or $F(x)=\exp(cx^2)$.

<a id="pdf-681b6f3d947f-p155-b003"></a>
<!-- pdf-source: page=155; block=3; confidence=0.94 -->
**Section 6.5 — Random matrices with non-i.i.d. entries.** Overview of the symmetrization technique: replace general $X_i$ by symmetric $\varepsilon_i X_i$, then condition on $X_i$ so all randomness lies with $\varepsilon_i$, reducing problems to symmetric Bernoulli variables. Applied here to bound norms of random matrices with independent but not identically distributed entries.

<a id="pdf-681b6f3d947f-p155-b004"></a>
<!-- pdf-source: page=155; block=4; confidence=0.97 -->
**Theorem 6.5.1.** Let $A$ be an $n\times n$ symmetric random matrix whose entries on and above the diagonal are independent, mean zero random variables. Then
$$\mathbb{E}\lVert A\rVert \le C\sqrt{\log n}\;\mathbb{E}\max_i \lVert A_i\rVert_2,$$
where $A_i$ denote the rows of $A$.

<a id="pdf-681b6f3d947f-p155-b005"></a>
<!-- pdf-source: page=155; block=5; confidence=0.94 -->
The bound is sharp up to the logarithmic factor: since the operator norm dominates the Euclidean norms of the rows, $\mathbb{E}\lVert A\rVert \ge \mathbb{E}\max_i \lVert A_i\rVert_2$. Unlike earlier results, Theorem 6.5.1 requires no moment assumptions on the entries.

<a id="pdf-681b6f3d947f-p155-b006"></a>
<!-- pdf-source: page=155; block=6; confidence=0.93 -->
**Proof of Theorem 6.5.1.** The argument combines symmetrization with the matrix Khintchine inequality (Exercise 5.4.13). First decompose $A$ into a sum of independent, mean zero, symmetric random matrices $Z_{ij}$, each containing a pair of symmetric entries of $A$ (or one diagonal entry). (Continued on next page.)

<a id="pdf-681b6f3d947f-p156-b001"></a>
<!-- pdf-source: page=156; block=1; confidence=0.95 -->
**Proof (continued).** Write $A = \sum_{i\le j} Z_{ij}$, where $Z_{ij} = A_{ij}(e_i e_j^T + e_j e_i^T)$ for $i<j$ and $Z_{ii} = A_{ii} e_i e_i^T$, with $(e_i)$ the canonical basis of $\mathbb{R}^n$. Symmetrization Lemma 6.4.2 gives
$$\mathbb{E}\lVert A\rVert = \mathbb{E}\Big\lVert\sum_{i\le j} Z_{ij}\Big\rVert \le 2\,\mathbb{E}\Big\lVert\sum_{i\le j}\varepsilon_{ij} Z_{ij}\Big\rVert, \tag{6.10}$$
with independent symmetric Bernoulli $(\varepsilon_{ij})$. Conditioning on $(Z_{ij})$ and applying matrix Khintchine (Exercise 5.4.13), then taking expectation,
$$\mathbb{E}\Big\lVert\sum_{i\le j}\varepsilon_{ij} Z_{ij}\Big\rVert \le C\sqrt{\log n}\;\mathbb{E}\Big\lVert\sum_{i\le j} Z_{ij}^2\Big\rVert^{1/2}. \tag{6.11}$$
Each $Z_{ij}^2$ is diagonal: $Z_{ij}^2 = A_{ij}^2(e_i e_i^T + e_j e_j^T)$ for $i<j$, and $A_{ii}^2 e_i e_i^T$ for $i=j$. Summing,
$$\sum_{i\le j} Z_{ij}^2 = \sum_{i=1}^n\Big(\sum_{j=1}^n A_{ij}^2\Big) e_i e_i^T = \sum_{i=1}^n \lVert A_i\rVert_2^2\, e_i e_i^T,$$
a diagonal matrix with entries $\lVert A_i\rVert_2^2$. Since the operator norm of a diagonal matrix equals its maximal absolute entry, $\lVert\sum_{i\le j} Z_{ij}^2\rVert = \max_i \lVert A_i\rVert_2^2$. Substituting into (6.11) then (6.10) completes the proof. $\blacksquare$

<a id="pdf-681b6f3d947f-p156-b002"></a>
<!-- pdf-source: page=156; block=2; confidence=0.95 -->
**Exercise 6.5.2.** Let $A$ be an $m\times n$ random matrix with independent, mean zero entries. Show
$$\mathbb{E}\lVert A\rVert \le C\sqrt{\log(m+n)}\Big(\mathbb{E}\max_i \lVert A_i\rVert_2 + \mathbb{E}\max_j \lVert A^j\rVert_2\Big),$$
where $A_i$ and $A^j$ denote the rows and columns of $A$. Hint: apply Theorem 6.5.1 to the $(m+n)\times(m+n)$ symmetric matrix $\begin{bmatrix}0 & A\\ A^T & 0\end{bmatrix}$ (Hermitization trick).

<a id="pdf-681b6f3d947f-p157-b001"></a>
<!-- pdf-source: page=157; block=1; confidence=0.95 -->
**Exercise 6.5.3 (Sharpness).** Show the result of Exercise 6.5.2 is sharp up to the logarithmic factor: one always has $E\|A\| \ge c\big(E\max_i \|A_i\|_2 + E\max_j \|A^j\|_2\big)$.

<a id="pdf-681b6f3d947f-p157-b002"></a>
<!-- pdf-source: page=157; block=2; confidence=0.93 -->
**Exercise 6.5.4 (Sharpness).** Show the logarithmic factor in Theorem 6.5.1 cannot be completely removed in general: construct a random matrix $A$ satisfying the theorem's assumptions with $E\|A\| \ge c\log^{1/4}(n)\cdot E\max_i \|A_i\|_2$. Hint: block-diagonal with $n/k$ independent $k\times k$ symmetric Bernoulli blocks; condition on a block being all ones; choose $k$ at the end.

<a id="pdf-681b6f3d947f-p157-b003"></a>
<!-- pdf-source: page=157; block=3; confidence=0.97 -->
# 6.6 Application: matrix completion

Motivation (compressed): given a few observed entries of a matrix, recovery is possible when the matrix has low rank.

<a id="pdf-681b6f3d947f-p157-b004"></a>
<!-- pdf-source: page=157; block=4; confidence=0.95 -->
**Setup.** Fix an $n\times n$ matrix $X$ with $\operatorname{rank}(X)=r$, $r\ll n$. Each entry $X_{ij}$ is revealed independently with probability $p\in(0,1)$ and hidden otherwise. We observe $Y$ with entries $Y_{ij}:=\delta_{ij}X_{ij}$, where $\delta_{ij}\sim\mathrm{Ber}(p)$ independent (selectors; hidden entries become $0$). Taking $p=\dfrac{m}{n^2}$ (6.12) means $m$ entries are shown on average. Recovery strategy: use a best rank-$r$ approximation to $Y$, suitably scaled.

<a id="pdf-681b6f3d947f-p157-b005"></a>
<!-- pdf-source: page=157; block=5; confidence=0.96 -->
**Theorem 6.6.1 (Matrix completion).** Let $\hat X$ be a best rank-$r$ approximation to $p^{-1}Y$. Then $E\,\dfrac{1}{n}\|\hat X - X\|_F \le C\sqrt{\dfrac{rn\log n}{m}}\,\|X\|_\infty$.

<a id="pdf-681b6f3d947f-p158-b001"></a>
<!-- pdf-source: page=158; block=1; confidence=0.95 -->
**Theorem 6.6.1 (continued).** The bound holds as long as $m\ge n\log n$, where $\|X\|_\infty = \max_{i,j}|X_{ij}|$ is the maximum entry magnitude.

<a id="pdf-681b6f3d947f-p158-b002"></a>
<!-- pdf-source: page=158; block=2; confidence=0.94 -->
The recovery error $\dfrac{1}{n}\|\hat X - X\|_F = \Big(\dfrac{1}{n^2}\sum_{i,j=1}^n |\hat X_{ij}-X_{ij}|^2\Big)^{1/2}$ is the average per-entry $L^2$ error. If $m\ge C'rn\log n$ with large $C'$, the average error is $\ll \|X\|_\infty$. Summary: completion succeeds once observed entries exceed $rn$ by a logarithmic margin.

<a id="pdf-681b6f3d947f-p158-b003"></a>
<!-- pdf-source: page=158; block=3; confidence=0.94 -->
**Proof, Step 1 (operator norm).** By triangle inequality $\|\hat X - X\| \le \|\hat X - p^{-1}Y\| + \|p^{-1}Y - X\|$. Since $\hat X$ is a best rank-$r$ approximation to $p^{-1}Y$, $\|\hat X - p^{-1}Y\|\le\|p^{-1}Y - X\|$, hence
$$\|\hat X - X\| \le 2\|p^{-1}Y - X\| = \tfrac{2}{p}\|Y - pX\|.\quad(6.13)$$
The entries $(Y-pX)_{ij}=(\delta_{ij}-p)X_{ij}$ are independent, mean-zero. Applying Exercise 6.5.2:
$$E\|Y-pX\| \le C\sqrt{\log n}\Big(E\max_{i\in[n]}\|(Y-pX)_i\|_2 + E\max_{j\in[n]}\|(Y-pX)^j\|_2\Big).\quad(6.14)$$
Row/column norms satisfy $\|(Y-pX)_i\|_2^2 = \sum_{j=1}^n (\delta_{ij}-p)^2 X_{ij}^2 \le \sum_{j=1}^n (\delta_{ij}-p)^2\cdot\|X\|_\infty^2$.

<a id="pdf-681b6f3d947f-p159-b001"></a>
<!-- pdf-source: page=159; block=1; confidence=0.95 -->
**Proof, Step 1 (concluded).** By Bernstein's/Chernoff's inequality, $E\max_{i\in[n]}\sum_{j=1}^n (\delta_{ij}-p)^2 \le Cpn$ (Exercise 6.6.2), similarly for columns. Substituting into (6.14) gives $E\|Y-pX\| \lesssim \sqrt{pn\log n}\,\|X\|_\infty$. Then by (6.13),
$$E\|\hat X - X\| \lesssim \sqrt{\tfrac{n\log n}{p}}\,\|X\|_\infty.\quad(6.15)$$

<a id="pdf-681b6f3d947f-p159-b002"></a>
<!-- pdf-source: page=159; block=2; confidence=0.95 -->
**Proof, Step 2 (Frobenius norm).** Since $\operatorname{rank}(X)\le r$ and $\operatorname{rank}(\hat X)\le r$, $\operatorname{rank}(\hat X - X)\le 2r$. Relation (4.4) gives $\|\hat X - X\|_F \le \sqrt{2r}\,\|\hat X - X\|$. Taking expectations with (6.15): $E\|\hat X - X\|_F \le \sqrt{2r}\,E\|\hat X - X\| \lesssim \sqrt{\tfrac{rn\log n}{p}}\,\|X\|_\infty$. Dividing by $n$: $E\,\tfrac{1}{n}\|\hat X - X\|_F \lesssim \sqrt{\tfrac{rn\log n}{pn^2}}\,\|X\|_\infty$. Since $pn^2=m$ by (6.12), the claim follows. $\square$

<a id="pdf-681b6f3d947f-p159-b003"></a>
<!-- pdf-source: page=159; block=3; confidence=0.93 -->
**Exercise 6.6.2 (Bounding rows of random matrices).** For i.i.d. $\delta_{ij}\sim\mathrm{Ber}(p)$, $i,j=1,\dots,n$, assuming $pn\ge\log n$, show $E\max_{i\in[n]}\sum_{j=1}^n (\delta_{ij}-p)^2 \le Cpn$. Hint: Bernstein tail bound for fixed $i$, then union bound over $i\in[n]$.

<a id="pdf-681b6f3d947f-p159-b004"></a>
<!-- pdf-source: page=159; block=4; confidence=0.94 -->
**Exercise 6.6.3 (Rectangular matrices).** State and prove a version of Theorem 6.6.1 for general rectangular $n_1\times n_2$ matrices $X$.

<a id="pdf-681b6f3d947f-p159-b005"></a>
<!-- pdf-source: page=159; block=5; confidence=0.90 -->
**Exercise 6.6.4 (Noisy observations).** Extend Theorem 6.6.1 to noisy observations, where noisy versions $X_{ij}+\nu_{ij}$ of the entries are shown. [Statement truncated in source.]

<a id="pdf-681b6f3d947f-p160-b001"></a>
<!-- pdf-source: page=160; block=1; confidence=0.90 -->
Continuation of the matrix-completion setup: observed entries of $X$ are corrupted by independent, mean-zero sub-gaussian noise variables $\nu_{ij}$.

<a id="pdf-681b6f3d947f-p160-b002"></a>
<!-- pdf-source: page=160; block=2; confidence=0.95 -->
**Remark 6.6.5 (Improvements).** The logarithmic factor in the bound of Theorem 6.6.1 can be removed, and in some cases matrix completion can be exact (zero error); see the chapter notes.

<a id="pdf-681b6f3d947f-p160-b003"></a>
<!-- pdf-source: page=160; block=3; confidence=0.95 -->
## 6.7 Contraction Principle

Notation: $\varepsilon_1,\varepsilon_2,\dots$ denote independent symmetric Bernoulli random variables, independent of all other random variables in question.

<a id="pdf-681b6f3d947f-p160-b004"></a>
<!-- pdf-source: page=160; block=4; confidence=0.98 -->
**Theorem 6.7.1 (Contraction principle).** Let $x_1,\dots,x_N$ be deterministic vectors in a normed space and $a=(a_1,\dots,a_N)\in\mathbb{R}^N$. Then
$$\mathbb{E}\Big\|\sum_{i=1}^N a_i\varepsilon_i x_i\Big\| \le \|a\|_\infty\cdot \mathbb{E}\Big\|\sum_{i=1}^N \varepsilon_i x_i\Big\|.$$

<a id="pdf-681b6f3d947f-p160-b005"></a>
<!-- pdf-source: page=160; block=5; confidence=0.97 -->
**Proof.** WLOG assume $\|a\|_\infty\le 1$. Define $f(a):=\mathbb{E}\big\|\sum_{i=1}^N a_i\varepsilon_i x_i\big\|$ (6.16); $f:\mathbb{R}^N\to\mathbb{R}$ is convex (Exercise 6.7.2). Bound $f$ over the cube $[-1,1]^N$: by the maximum principle, a convex function on a compact convex set attains its maximum at an extreme point, i.e. a vertex $a$ with all $a_i=\pm1$. At such $a$, $(\varepsilon_i a_i)$ has the same distribution as $(\varepsilon_i)$ by symmetry, so $\mathbb{E}\big\|\sum a_i\varepsilon_i x_i\big\|=\mathbb{E}\big\|\sum \varepsilon_i x_i\big\|$. Hence $f(a)\le \mathbb{E}\big\|\sum_{i=1}^N \varepsilon_i x_i\big\|$ whenever $\|a\|_\infty\le1$. $\blacksquare$

<a id="pdf-681b6f3d947f-p160-b006"></a>
<!-- pdf-source: page=160; block=6; confidence=0.95 -->
**Exercise 6.7.2.** Verify that the function $f$ defined in (6.16) is convex.

<a id="pdf-681b6f3d947f-p160-b007"></a>
<!-- pdf-source: page=160; block=7; confidence=0.96 -->
**Exercise 6.7.3 (Contraction principle for general distributions).** Let $X_1,\dots,X_N$ be independent, mean-zero random vectors in a normed space and $a=(a_1,\dots,a_n)\in\mathbb{R}^n$. Prove
$$\mathbb{E}\Big\|\sum_{i=1}^N a_i X_i\Big\| \le 4\|a\|_\infty\cdot \mathbb{E}\Big\|\sum_{i=1}^N X_i\Big\|.$$

<a id="pdf-681b6f3d947f-p161-b001"></a>
<!-- pdf-source: page=161; block=1; confidence=0.90 -->
Hint for Exercise 6.7.3: apply symmetrization, then Theorem 6.7.1 conditioned on $(X_i)$, then symmetrization again. As an application, symmetrization can instead be carried out with Gaussian $g_i\sim N(0,1)$ in place of the Bernoulli $\varepsilon_i$.

<a id="pdf-681b6f3d947f-p161-b002"></a>
<!-- pdf-source: page=161; block=2; confidence=0.97 -->
**Lemma 6.7.4 (Symmetrization with Gaussians).** Let $X_1,\dots,X_N$ be independent, mean-zero random vectors in a normed space, and $g_1,\dots,g_N\sim N(0,1)$ independent (and independent of the $X_i$). Then
$$\frac{c}{\sqrt{\log N}}\,\mathbb{E}\Big\|\sum_{i=1}^N g_i X_i\Big\| \le \mathbb{E}\Big\|\sum_{i=1}^N X_i\Big\| \le 3\,\mathbb{E}\Big\|\sum_{i=1}^N g_i X_i\Big\|.$$

<a id="pdf-681b6f3d947f-p161-b003"></a>
<!-- pdf-source: page=161; block=3; confidence=0.95 -->
**Proof (upper bound).** By symmetrization (Lemma 6.4.2), $E:=\mathbb{E}\big\|\sum X_i\big\|\le 2\,\mathbb{E}\big\|\sum \varepsilon_i X_i\big\|$. Since $\mathbb{E}|g_i|=\sqrt{2/\pi}$, insert Gaussians: by Jensen's inequality
$$E\le 2\sqrt{\tfrac{\pi}{2}}\,\mathbb{E}_X\Big\|\sum_{i=1}^N \varepsilon_i\,\mathbb{E}_g|g_i|\,X_i\Big\| \le 2\sqrt{\tfrac{\pi}{2}}\,\mathbb{E}\Big\|\sum_{i=1}^N \varepsilon_i|g_i|X_i\Big\| = 2\sqrt{\tfrac{\pi}{2}}\,\mathbb{E}\Big\|\sum_{i=1}^N g_i X_i\Big\|,$$
the last equality because $\varepsilon_i|g_i|$ has the same distribution as $g_i$ (Exercise 6.4.1). (Footnote: $\mathbb{E}_g$ is expectation over $(g_i)$ conditional on $(X_i)$, and $\mathbb{E}_X$ over $(X_i)$.)

<a id="pdf-681b6f3d947f-p162-b001"></a>
<!-- pdf-source: page=162; block=1; confidence=0.95 -->
**Proof (lower bound, continued).** Using contraction (Theorem 6.7.1) and symmetrization (Lemma 6.4.2):
$$\mathbb{E}\Big\|\sum g_i X_i\Big\| = \mathbb{E}\Big\|\sum \varepsilon_i g_i X_i\Big\| \text{ (symmetry of }g_i\text{)} \le \mathbb{E}_g\,\mathbb{E}_X\Big[\|g\|_\infty\,\mathbb{E}_\varepsilon\Big\|\sum \varepsilon_i X_i\Big\|\Big] \text{ (Thm 6.7.1)}$$
$$= \mathbb{E}_g\Big[\|g\|_\infty\,\mathbb{E}_\varepsilon\mathbb{E}_X\Big\|\sum \varepsilon_i X_i\Big\|\Big] \text{ (independence)} \le 2\,\mathbb{E}_g\Big[\|g\|_\infty\,\mathbb{E}_X\Big\|\sum X_i\Big\|\Big] \text{ (Lemma 6.4.2)} = 2(\mathbb{E}\|g\|_\infty)\Big(\mathbb{E}\Big\|\sum X_i\Big\|\Big).$$
By Exercise 2.5.10, $\mathbb{E}\|g\|_\infty\le C\sqrt{\log N}$, completing the proof. $\blacksquare$

<a id="pdf-681b6f3d947f-p162-b002"></a>
<!-- pdf-source: page=162; block=2; confidence=0.95 -->
**Exercise 6.7.5.** Show the factor $\sqrt{\log N}$ in Lemma 6.7.4 is needed in general and is optimal; hence Gaussian symmetrization is generally weaker than symmetrization with symmetric Bernoullis.

<a id="pdf-681b6f3d947f-p162-b003"></a>
<!-- pdf-source: page=162; block=3; confidence=0.95 -->
**Exercise 6.7.6 (Symmetrization and contraction for functions of norms).** For a convex increasing $F:\mathbb{R}_+\to\mathbb{R}$, generalize the symmetrization and contraction results by replacing the norm $\|\cdot\|$ with $F(\|\cdot\|)$ throughout.

<a id="pdf-681b6f3d947f-p162-b004"></a>
<!-- pdf-source: page=162; block=4; confidence=0.95 -->
**Exercise 6.7.7 (Talagrand's contraction principle).** For a bounded $T\subset\mathbb{R}^n$, independent symmetric Bernoulli $\varepsilon_1,\dots,\varepsilon_n$, and contractions $\phi_i:\mathbb{R}\to\mathbb{R}$ ($\|\phi_i\|_{\mathrm{Lip}}\le1$):
$$\mathbb{E}\sup_{t\in T}\sum_{i=1}^n \varepsilon_i\phi_i(t_i) \le \mathbb{E}\sup_{t\in T}\sum_{i=1}^n \varepsilon_i t_i. \quad (6.17)$$
Step (a): for $n=2$, $T\subset\mathbb{R}^2$ and contraction $\phi:\mathbb{R}\to\mathbb{R}$, check that
$$\sup_{t\in T}(t_1+\phi(t_2))+\sup_{t\in T}(t_1-\phi(t_2)) \le \sup_{t\in T}(t_1+t_2)+\sup_{t\in T}(t_1-t_2).$$

<a id="pdf-681b6f3d947f-p163-b001"></a>
<!-- pdf-source: page=163; block=1; confidence=0.90 -->
**Exercise (part b, continued).** Complete the proof by induction on $n$; to establish (6.17), condition on $\varepsilon_1,\dots,\varepsilon_{n-1}$ and apply part 1.

<a id="pdf-681b6f3d947f-p163-b002"></a>
<!-- pdf-source: page=163; block=2; confidence=0.95 -->
**Exercise 6.7.8.** Generalize Talagrand's contraction principle to arbitrary Lipschitz functions $\varphi_i:\mathbb{R}\to\mathbb{R}$ with no restriction on their Lipschitz norms. Hint: use Theorem 6.7.1.

<a id="pdf-681b6f3d947f-p163-b003"></a>
<!-- pdf-source: page=163; block=3; confidence=0.98 -->
## 6.8 Notes

<a id="pdf-681b6f3d947f-p163-b004"></a>
<!-- pdf-source: page=163; block=4; confidence=0.90 -->
Bibliographic notes: The decoupling inequality (Theorem 6.1.1, Exercise 6.1.5) originates with Bourgain–Tzafriri; related extensions cited. The Hanson–Wright inequality's original (weaker) form dates to earlier work; Theorem 6.2.1 and its proof follow [179], with special cases for Bernoulli, Gaussian, and diagonal-free matrices cited. Concentration for anisotropic vectors (Theorem 6.3.2) and the random-vector-to-subspace distance bound (Exercise 6.3.4) are from [179]. Symmetrization Lemma 6.4.2 appears in [130], [78]. Theorem 6.5.1 is essentially known; its $\sqrt{\log n}$ factor can be improved to $\log^{1/4} n$ via Seginer's theorem plus symmetrization, which is optimal (Exercise 6.5.4), and can be removed entirely for i.i.d.- and Gaussian-entry matrices. The matrix completion result Theorem 6.6.1 and its proof are from [170]; a trimming argument removes the log factor, and exact completion is possible with $m\asymp rn\log^2(n)$ sampled entries under incoherence assumptions.

<a id="pdf-681b6f3d947f-p164-b001"></a>
<!-- pdf-source: page=164; block=1; confidence=0.92 -->
Bibliographic notes (contraction): The contraction principle (Theorem 6.7.1) and Lemma 6.7.4 (inequality (4.9)) are from [130]; the logarithmic factor in the lemma can be removed when the normed space has nontrivial cotype. Talagrand's contraction principle (Exercise 6.7.7) appears in [130] in a more general form (with a convex increasing function of the supremum) and is adapted from [212]; a Gaussian version is deferred to Exercise 7.2.13.

<a id="pdf-681b6f3d947f-p165-b001"></a>
<!-- pdf-source: page=165; block=1; confidence=0.98 -->
# 7 Random processes

<a id="pdf-681b6f3d947f-p165-b002"></a>
<!-- pdf-source: page=165; block=2; confidence=0.93 -->
A random process is a collection $(X_t)_{t\in T}$ of not-necessarily-independent random variables; in high-dimensional probability $T$ is a general abstract set. Key example: the canonical Gaussian process $X_t=\langle g,t\rangle$, $t\in T$, with $T\subset\mathbb{R}^n$ and $g$ a standard normal vector in $\mathbb{R}^n$ (Section 7.1). Chapter outline: Gaussian comparison inequalities (Slepian, Sudakov–Fernique, Gordon) via Gaussian interpolation (Section 7.2); a sharp operator-norm bound $\mathbb{E}\|A\|\le\sqrt{m}+\sqrt{n}$ for an $m\times n$ Gaussian matrix (Section 7.3); Sudakov's minoration lower-bounding the Gaussian width $w(T)=\mathbb{E}\sup_{t\in T}\langle g,t\rangle$ via covering numbers (Section 7.4); the Gaussian width and related notions—stable dimension, stable rank, Gaussian complexity (Section 7.5); and random projections of a set $T\subset\mathbb{R}^n$ (Section 7.7).

<a id="pdf-681b6f3d947f-p165-b003"></a>
<!-- pdf-source: page=165; block=3; confidence=0.97 -->
## 7.1 Basic concepts and examples

<a id="pdf-681b6f3d947f-p165-b004"></a>
<!-- pdf-source: page=165; block=4; confidence=0.97 -->
**Definition 7.1.1 (Random process).** A random process is a collection of random variables $(X_t)_{t\in T}$ on a common probability space, indexed by elements $t$ of a set $T$.

<a id="pdf-681b6f3d947f-p166-b001"></a>
<!-- pdf-source: page=166; block=1; confidence=0.95 -->
Sometimes $t$ denotes time so $T\subseteq\mathbb{R}$; the focus here is high-dimensional settings with $T\subseteq\mathbb{R}^n$, where the time analogy is lost.

<a id="pdf-681b6f3d947f-p166-b002"></a>
<!-- pdf-source: page=166; block=2; confidence=0.97 -->
**Example 7.1.2 (Discrete time).** If $T=\{1,\dots,n\}$, the random process is identified with a random vector $(X_1,\dots,X_n)\in\mathbb{R}^n$.

<a id="pdf-681b6f3d947f-p166-b003"></a>
<!-- pdf-source: page=166; block=3; confidence=0.97 -->
**Example 7.1.3 (Random walks).** For $T=\mathbb{N}$, a discrete-time process $(X_n)_{n\in\mathbb{N}}$ is a sequence of random variables. A random walk is $X_n:=\sum_{i=1}^n Z_i$, where the increments $Z_i$ are independent, mean-zero random variables.

<a id="pdf-681b6f3d947f-p166-b004"></a>
<!-- pdf-source: page=166; block=4; confidence=0.90 -->
Figure 7.1: trials of a random walk with symmetric Bernoulli steps $Z_i$ (left) and of standard Brownian motion in $\mathbb{R}$ (right).

<a id="pdf-681b6f3d947f-p166-b005"></a>
<!-- pdf-source: page=166; block=5; confidence=0.96 -->
**Example 7.1.4 (Brownian motion).** The standard Brownian motion (Wiener process) $(X_t)_{t\ge 0}$ is characterized by: (i) continuous sample paths, i.e. $f(t):=X_t$ is continuous almost surely; (ii) independent increments with $X_t-X_s\sim N(0,\,t-s)$ for all $t\ge s$.

<a id="pdf-681b6f3d947f-p167-b001"></a>
<!-- pdf-source: page=167; block=1; confidence=0.95 -->
**Example 7.1.5 (Random fields).** When $T\subseteq\mathbb{R}^n$, a process $(X_t)_{t\in T}$ is called a spatial random process or random field (e.g. water temperature $X_t$ at Earth location $t$).

<a id="pdf-681b6f3d947f-p167-b002"></a>
<!-- pdf-source: page=167; block=2; confidence=0.95 -->
**Section 7.1.1 — Covariance and increments.** Analogue of the covariance matrix for random processes; this section assumes zero mean, $\mathbb{E}X_t=0$ for all $t\in T$.

<a id="pdf-681b6f3d947f-p167-b003"></a>
<!-- pdf-source: page=167; block=3; confidence=0.96 -->
**Definition.** For a zero-mean process $(X_t)_{t\in T}$, the covariance function is $\Sigma(t,s):=\operatorname{cov}(X_t,X_s)=\mathbb{E}X_tX_s$, $t,s\in T$. The increments are $d(t,s):=\lVert X_t-X_s\rVert_{L^2}=\big(\mathbb{E}(X_t-X_s)^2\big)^{1/2}$, $t,s\in T$.

<a id="pdf-681b6f3d947f-p167-b004"></a>
<!-- pdf-source: page=167; block=4; confidence=0.95 -->
**Example 7.1.6.** Standard Brownian motion has increments $d(t,s)=\sqrt{t-s}$ for $t\ge s$. A random walk (Example 7.1.3) with $\mathbb{E}Z_i^2=1$ behaves similarly: $d(n,m)=\sqrt{n-m}$ for $n\ge m$.

<a id="pdf-681b6f3d947f-p167-b005"></a>
<!-- pdf-source: page=167; block=5; confidence=0.93 -->
**Remark 7.1.7 (Canonical metric).** The increments $d(t,s)$ always define a (pseudo)metric on $T$, making $T$ a metric space even without geometric structure; this metric need not agree with $|t-s|$ on $\mathbb{R}$ (per Example 7.1.6). Footnote: $d$ is a pseudometric since $d(t,s)=0$ need not imply $t=s$.

<a id="pdf-681b6f3d947f-p167-b006"></a>
<!-- pdf-source: page=167; block=6; confidence=0.95 -->
**Exercise 7.1.8 (Covariance vs. increments).** For a process $(X_t)_{t\in T}$: (a) express the increments $\lVert X_t-X_s\rVert_{L^2}$ via the covariance function $\Sigma(t,s)$; (b) assuming the zero random variable $0$ belongs to the process, express $\Sigma(t,s)$ via the increments.

<a id="pdf-681b6f3d947f-p168-b001"></a>
<!-- pdf-source: page=168; block=1; confidence=0.95 -->
**Exercise 7.1.9 (Symmetrization for random processes).** Let $X_1(t),\dots,X_N(t)$ be independent, mean-zero processes indexed by $t\in T$, and $\varepsilon_1,\dots,\varepsilon_N$ independent symmetric Bernoulli variables. Prove $\tfrac12\,\mathbb{E}\sup_{t\in T}\big|\sum_{i=1}^N\varepsilon_iX_i(t)\big| \le \mathbb{E}\sup_{t\in T}\big|\sum_{i=1}^N X_i(t)\big| \le 2\,\mathbb{E}\sup_{t\in T}\big|\sum_{i=1}^N\varepsilon_iX_i(t)\big|$. Hint: argue as in the proof of Lemma 6.4.2.

<a id="pdf-681b6f3d947f-p168-b002"></a>
<!-- pdf-source: page=168; block=2; confidence=0.97 -->
**Section 7.1.2 — Gaussian processes.**

<a id="pdf-681b6f3d947f-p168-b003"></a>
<!-- pdf-source: page=168; block=3; confidence=0.95 -->
**Definition 7.1.10 (Gaussian process).** $(X_t)_{t\in T}$ is a Gaussian process if for every finite $T_0\subset T$ the vector $(X_t)_{t\in T_0}$ is normal; equivalently, every finite linear combination $\sum_{t\in T_0} a_t X_t$ is a normal random variable (by the characterization in Exercise 3.3.4). This generalizes Gaussian random vectors in $\mathbb{R}^n$; standard Brownian motion is an example.

<a id="pdf-681b6f3d947f-p168-b004"></a>
<!-- pdf-source: page=168; block=4; confidence=0.93 -->
**Remark 7.1.11.** By formula (3.5) for the multivariate normal density, a mean-zero Gaussian vector's distribution is determined by its covariance matrix; hence the distribution of a mean-zero Gaussian process $(X_t)_{t\in T}$ is determined by its covariance function $\Sigma(t,s)$, equivalently (via Exercise 7.1.8) by its increments $d(t,s)$. (Footnote: understood as determining all finite marginals $(X_t)_{t\in T_0}$.)

<a id="pdf-681b6f3d947f-p168-b005"></a>
<!-- pdf-source: page=168; block=5; confidence=0.95 -->
**Definition (Canonical Gaussian process).** For $g\sim N(0,I_n)$ and $T\subseteq\mathbb{R}^n$, define $X_t:=\langle g,t\rangle$, $t\in T$ (Eq. 7.1). This is a Gaussian process with increments equal to the Euclidean distance, $\lVert X_t-X_s\rVert_{L^2}=\lVert t-s\rVert_2$. Any Gaussian process can be realized as the canonical process (7.1).

<a id="pdf-681b6f3d947f-p169-b001"></a>
<!-- pdf-source: page=169; block=1; confidence=0.97 -->
**Lemma 7.1.12 (Gaussian random vectors).** If Y is a mean-zero Gaussian random vector in R^n, then there exist points t_1,...,t_n ∈ R^n such that Y ≡ (⟨g, t_i⟩)_{i=1}^n where g ~ N(0, I_n). Here ≡ denotes equality of distributions.

<a id="pdf-681b6f3d947f-p169-b002"></a>
<!-- pdf-source: page=169; block=2; confidence=0.97 -->
**Proof.** Let Σ be the covariance matrix of Y. Realize Y ≡ Σ^{1/2} g with g ~ N(0, I_n). The coordinates of Σ^{1/2} g are ⟨t_i, g⟩, where the t_i are the rows of Σ^{1/2}. ∎

<a id="pdf-681b6f3d947f-p169-b003"></a>
<!-- pdf-source: page=169; block=3; confidence=0.95 -->
For any Gaussian process (Y_s)_{s∈S}, every finite-dimensional marginal (Y_s)_{s∈S_0} with |S_0| = n can be represented as the canonical Gaussian process (7.1) indexed by some subset T_0 ⊂ R^n.

<a id="pdf-681b6f3d947f-p169-b004"></a>
<!-- pdf-source: page=169; block=4; confidence=0.94 -->
**Exercise 7.1.13.** Realize the N-step random walk of Example 7.1.3 (with Z_i ~ N(0,1)) as a canonical Gaussian process (7.1) with T ⊂ R^N. Hint: work with increments ‖X_t − X_s‖_2 rather than the covariance matrix.

<a id="pdf-681b6f3d947f-p169-b005"></a>
<!-- pdf-source: page=169; block=5; confidence=0.97 -->
## 7.2 Slepian's inequality

<a id="pdf-681b6f3d947f-p169-b006"></a>
<!-- pdf-source: page=169; block=6; confidence=0.90 -->
It is useful to bound E sup_{t∈T} X_t. For a standard Brownian motion the reflection principle gives E sup_{t≤t_0} X_t = √(2 t_0 / π) for every t_0 ≥ 0. For general (even Gaussian) processes the problem is nontrivial. Slepian's comparison inequality: the faster a Gaussian process grows in increment magnitude, the farther it reaches.

<a id="pdf-681b6f3d947f-p169-b007"></a>
<!-- pdf-source: page=169; block=7; confidence=0.97 -->
**Theorem 7.2.1 (Slepian's inequality).** Let (X_t)_{t∈T} and (Y_t)_{t∈T} be mean-zero Gaussian processes such that for all t, s ∈ T,

E X_t^2 = E Y_t^2  and  E(X_t − X_s)^2 ≤ E(Y_t − Y_s)^2.  (7.2)

Then for every τ ∈ R,

P{ sup_{t∈T} X_t ≥ τ } ≤ P{ sup_{t∈T} Y_t ≥ τ }.  (7.3)

<a id="pdf-681b6f3d947f-p169-b008"></a>
<!-- pdf-source: page=169; block=8; confidence=0.93 -->
To avoid measurability issues, E sup_{t∈T} X_t is interpreted via finite-dimensional marginals as sup_{T_0 ⊂ T} E max_{t∈T_0} X_t, the supremum being over all finite subsets T_0 ⊂ T.

<a id="pdf-681b6f3d947f-p170-b001"></a>
<!-- pdf-source: page=170; block=1; confidence=0.95 -->
Consequently, E sup_{t∈T} X_t ≤ E sup_{t∈T} Y_t. (7.4) When the tail comparison (7.3) holds, X is said to be stochastically dominated by Y.

<a id="pdf-681b6f3d947f-p170-b002"></a>
<!-- pdf-source: page=170; block=2; confidence=0.93 -->
### 7.2.1 Gaussian interpolation

Assume T is finite, so X = (X_t)_{t∈T} and Y = (Y_t)_{t∈T} are Gaussian random vectors in R^n, n = |T|, taken independent. Define the interpolating Gaussian vector Z(u) := √u X + √(1−u) Y, u ∈ [0,1], with Z(0) = Y and Z(1) = X.

<a id="pdf-681b6f3d947f-p170-b003"></a>
<!-- pdf-source: page=170; block=3; confidence=0.96 -->
**Exercise 7.2.2.** Check that the covariance matrix of Z(u) interpolates linearly: Σ(Z(u)) = u Σ(X) + (1−u) Σ(Y).

<a id="pdf-681b6f3d947f-p170-b004"></a>
<!-- pdf-source: page=170; block=4; confidence=0.94 -->
Study how E f(Z(u)) changes as u goes 0→1 for f(x) = 1{ max_i x_i < τ }. Showing E f(Z(u)) increases in u yields Slepian's inequality: E f(Z(1)) ≥ E f(Z(0)) gives P{ max_i X_i < τ } ≥ P{ max_i Y_i < τ }.

<a id="pdf-681b6f3d947f-p170-b005"></a>
<!-- pdf-source: page=170; block=5; confidence=0.97 -->
**Lemma 7.2.3 (Gaussian integration by parts).** Let X ~ N(0,1). For any differentiable f : R → R, E f'(X) = E X f(X), assuming both expectations exist and are finite.

<a id="pdf-681b6f3d947f-p170-b006"></a>
<!-- pdf-source: page=170; block=6; confidence=0.95 -->
**Proof.** Assume first that f has bounded support. Denote the Gaussian density of X by p(x) = (1/√(2π)) e^{−x^2/2}. (continues)

<a id="pdf-681b6f3d947f-p171-b001"></a>
<!-- pdf-source: page=171; block=1; confidence=0.97 -->
**Proof (cont.).** Writing the expectation as an integral and integrating by parts,

E f'(X) = ∫_R f'(x) p(x) dx = − ∫_R f(x) p'(x) dx.  (7.5)

Since p'(x) = −x p(x), the integral in (7.5) equals ∫_R f(x) p(x) x dx = E X f(X). Extend to general functions by approximation. ∎

<a id="pdf-681b6f3d947f-p171-b002"></a>
<!-- pdf-source: page=171; block=2; confidence=0.96 -->
**Exercise 7.2.4.** If X ~ N(0, σ^2), show E X f(X) = σ^2 E f'(X). Hint: write X = σ Z with Z ~ N(0,1) and apply Gaussian integration by parts.

<a id="pdf-681b6f3d947f-p171-b003"></a>
<!-- pdf-source: page=171; block=3; confidence=0.97 -->
**Lemma 7.2.5 (Multivariate Gaussian integration by parts).** Let X ~ N(0, Σ). For any differentiable f : R^n → R, E X f(X) = Σ · E ∇f(X), assuming both expectations exist and are finite.

<a id="pdf-681b6f3d947f-p171-b004"></a>
<!-- pdf-source: page=171; block=4; confidence=0.94 -->
**Exercise 7.2.6.** Prove Lemma 7.2.5. Equivalently, E X_i f(X) = Σ_{j=1}^n Σ_{ij} E (∂f/∂x_j)(X), i = 1,...,n.  (7.6) Hint: write X = Σ^{1/2} Z with Z ~ N(0, I_n), so X_i = Σ_k (Σ^{1/2})_{ik} Z_k and E X_i f(X) = Σ_k (Σ^{1/2})_{ik} E Z_k f(Σ^{1/2} Z); apply univariate integration by parts conditionally on all variables except Z_k.

<a id="pdf-681b6f3d947f-p171-b005"></a>
<!-- pdf-source: page=171; block=5; confidence=0.97 -->
**Lemma 7.2.7 (Gaussian interpolation).** Let X ~ N(0, Σ^X) and Y ~ N(0, Σ^Y) be independent, and set Z(u) := √u X + √(1−u) Y, u ∈ [0,1]. Then for any twice-differentiable f : R^n → R,

(d/du) E f(Z(u)) = (1/2) Σ_{i,j=1}^n (Σ^X_{ij} − Σ^Y_{ij}) E[ (∂^2 f / ∂x_i ∂x_j)(Z(u)) ],  (7.8)

assuming all expectations exist and are finite.

<a id="pdf-681b6f3d947f-p172-b001"></a>
<!-- pdf-source: page=172; block=1; confidence=0.90 -->
**Proof (continued).** By the multivariate chain rule, d/du E f(Z(u)) = Σᵢ E[∂f/∂xᵢ(Z(u)) · dZᵢ/du] = ½ Σᵢ E[∂f/∂xᵢ(Z(u)) · (Xᵢ/√u − Yᵢ/√(1−u))] by (7.7) — eq (7.9). Split the sum into Xᵢ- and Yᵢ-terms. For the Xᵢ contribution, condition on Y: Σᵢ (1/√u) E[Xᵢ ∂f/∂xᵢ(Z(u))] = Σᵢ (1/√u) E[Xᵢ gᵢ(X)] — eq (7.10), where gᵢ(X) = ∂f/∂xᵢ(√u X + √(1−u) Y). Apply multivariate Gaussian integration by parts (Lemma 7.2.5) using (7.6): E[Xᵢ gᵢ(X)] = Σⱼ Σˣᵢⱼ E[∂gᵢ/∂xⱼ(X)] = Σⱼ Σˣᵢⱼ E[∂²f/∂xᵢ∂xⱼ(√u X + √(1−u) Y)] · √u. Substituting into (7.10): Σᵢ (1/√u) E[Xᵢ ∂f/∂xᵢ(Z(u))] = Σᵢ,ⱼ Σˣᵢⱼ E[∂²f/∂xᵢ∂xⱼ(Z(u))]. Taking expectation over Y lifts the conditioning. The Yᵢ-sum is evaluated similarly; combining the two sums completes the proof. (Footnote 4: multivariate chain rule df/du = Σᵢ (∂f/∂xᵢ)(dgᵢ/du) for f(g₁(u),…,gₙ(u)), gᵢ: ℝ→ℝ, f: ℝⁿ→ℝ.)

<a id="pdf-681b6f3d947f-p172-b002"></a>
<!-- pdf-source: page=172; block=2; confidence=0.98 -->
**7.2.2 Proof of Slepian's inequality.** Establishes a preliminary functional form of Slepian's inequality.

<a id="pdf-681b6f3d947f-p172-b003"></a>
<!-- pdf-source: page=172; block=3; confidence=0.95 -->
**Lemma 7.2.8 (Slepian's inequality, functional form).** Let X, Y be mean-zero Gaussian random vectors in ℝⁿ with, for all i, j = 1,…,n, E Xᵢ² = E Yᵢ² and E(Xᵢ − Xⱼ)² ≤ E(Yᵢ − Yⱼ)². Let f: ℝⁿ → ℝ be twice differentiable with ∂²f/∂xᵢ∂xⱼ ≥ 0 for all i ≠ j. Then E f(X) ≥ E f(Y), provided both expectations exist and are finite. (Statement begins on p.172, concludes on p.173.)

<a id="pdf-681b6f3d947f-p173-b001"></a>
<!-- pdf-source: page=173; block=1; confidence=0.95 -->
**Proof.** The assumptions translate to covariance-matrix entries Σˣᵢᵢ = Σʸᵢᵢ and Σˣᵢⱼ ≥ Σʸᵢⱼ for all i, j. Assume X and Y independent. By Lemma 7.2.7 and these assumptions, d/du E f(Z(u)) ≥ 0, so E f(Z(u)) is nondecreasing in u. Hence E f(X) = E f(Z(1)) ≥ E f(Z(0)) = E f(Y).

<a id="pdf-681b6f3d947f-p173-b002"></a>
<!-- pdf-source: page=173; block=2; confidence=0.96 -->
**Theorem 7.2.9 (Slepian's inequality).** Let X, Y be Gaussian random vectors as in Lemma 7.2.8. Then for every τ ≥ 0, P{maxᵢ≤n Xᵢ ≥ τ} ≤ P{maxᵢ≤n Yᵢ ≥ τ}. Consequently, E maxᵢ≤n Xᵢ ≤ E maxᵢ≤n Yᵢ. (Stated in equivalent form for Gaussian random vectors.)

<a id="pdf-681b6f3d947f-p173-b003"></a>
<!-- pdf-source: page=173; block=3; confidence=0.92 -->
**Proof.** Let h: ℝ → [0,1] be a twice-differentiable, non-increasing smooth approximation to the indicator 1_(−∞,τ), i.e. h(x) ≈ 1_(−∞,τ) (Figure 7.2). Define f: ℝⁿ → ℝ by (proof continues on p.174). Figure 7.2: h(x) is a smooth, non-increasing approximation to the indicator 1_(−∞,τ).

<a id="pdf-681b6f3d947f-p174-b001"></a>
<!-- pdf-source: page=174; block=1; confidence=0.93 -->
**Proof (continued).** Set f(x) = h(x₁)···h(xₙ), an approximation to 1_{maxᵢ xᵢ < τ}. To verify the hypotheses of Lemma 7.2.8, for i ≠ j: ∂²f/∂xᵢ∂xⱼ = h′(xᵢ) h′(xⱼ) · ∏_{k∉{i,j}} h(xₖ). The first two factors are non-positive and the rest non-negative, so the second derivative is ≥ 0. Hence E f(X) ≥ E f(Y). By approximation, P{maxᵢ≤n Xᵢ < τ} ≥ P{maxᵢ≤n Yᵢ < τ}, proving the first part. The second part follows from the integral identity of Lemma 1.2.1 (see Exercise 7.2.10).

<a id="pdf-681b6f3d947f-p174-b002"></a>
<!-- pdf-source: page=174; block=2; confidence=0.95 -->
**Exercise 7.2.10.** Using the integral identity of Exercise 1.2.2, deduce the second part of Slepian's inequality (the comparison of expectations).

<a id="pdf-681b6f3d947f-p174-b003"></a>
<!-- pdf-source: page=174; block=3; confidence=0.95 -->
**7.2.3 Sudakov-Fernique's and Gordon's inequalities.** Slepian's inequality assumes both equal variances and dominance of increments for (Xₜ), (Yₜ) in (7.2); this section removes the equal-variance assumption while still obtaining (7.4), a result due to Sudakov and Fernique.

<a id="pdf-681b6f3d947f-p174-b004"></a>
<!-- pdf-source: page=174; block=4; confidence=0.96 -->
**Theorem 7.2.11 (Sudakov-Fernique's inequality).** Let (Xₜ)_{t∈T} and (Yₜ)_{t∈T} be two mean-zero Gaussian processes with E(Xₜ − Xₛ)² ≤ E(Yₜ − Yₛ)² for all t, s ∈ T. Then E sup_{t∈T} Xₜ ≤ E sup_{t∈T} Yₜ.

<a id="pdf-681b6f3d947f-p174-b005"></a>
<!-- pdf-source: page=174; block=5; confidence=0.92 -->
**Proof.** It suffices to prove the theorem for Gaussian random vectors X, Y in ℝⁿ (as done for Slepian's inequality, Theorem 7.2.9), again deducing it from the Gaussian Interpolation Lemma 7.2.7. But now, instead of choosing f(x) approximating the indicator of {maxᵢ xᵢ < τ}, take f(x) to approximate maxᵢ xᵢ. (Proof continues beyond supplied pages.)

<a id="pdf-681b6f3d947f-p175-b001"></a>
<!-- pdf-source: page=175; block=1; confidence=0.95 -->
Define the soft-max function $f(x) := \tfrac{1}{\beta}\log\sum_{i=1}^n e^{\beta x_i}$ (7.11), with parameter $\beta>0$. It satisfies $f(x)\to\max_{i\le n} x_i$ as $\beta\to\infty$. Substituting $f$ into the Gaussian interpolation formula (7.8) and simplifying gives $\frac{d}{du}\,\mathbb{E} f(Z(u))\le 0$ for all $u$; the proof of Sudakov-Fernique then finishes as in Slepian's inequality.

<a id="pdf-681b6f3d947f-p175-b002"></a>
<!-- pdf-source: page=175; block=2; confidence=0.95 -->
**Exercise 7.2.12.** Show $\frac{d}{du}\mathbb{E} f(Z(u))\le 0$ in Sudakov-Fernique's Theorem 7.2.11. Compute $\frac{\partial f}{\partial x_i}=\frac{e^{\beta x_i}}{\sum_k e^{\beta x_k}}=:p_i(x)$ and $\frac{\partial^2 f}{\partial x_i\partial x_j}=\beta\big(\delta_{ij}p_i(x)-p_i(x)p_j(x)\big)$, $\delta_{ij}$ the Kronecker delta. Numeric identity: if $\sum_{i=1}^n p_i=1$ then $\sum_{i,j=1}^n \sigma_{ij}(\delta_{ij}p_i-p_ip_j)=\tfrac12\sum_{i\ne j}(\sigma_{ii}+\sigma_{jj}-2\sigma_{ij})p_ip_j$. Using formula 7.2.7 with $\sigma_{ij}=\Sigma^X_{ij}-\Sigma^Y_{ij}$ and $p_i=p_i(Z(u))$, deduce $\frac{d}{du}\mathbb{E} f(Z(u))=\tfrac{\beta}{4}\sum_{i\ne j}\big[\mathbb{E}(X_i-X_j)^2-\mathbb{E}(Y_i-Y_j)^2\big]\,\mathbb{E}\,p_i(Z(u))p_j(Z(u))$, which is non-positive by the assumptions.

<a id="pdf-681b6f3d947f-p175-b003"></a>
<!-- pdf-source: page=175; block=3; confidence=0.97 -->
**Exercise 7.2.13 (Gaussian contraction inequality).** A Gaussian analogue of Talagrand's contraction principle (Exercise 6.7.7). For a bounded $T\subset\mathbb{R}^n$, independent $g_1,\dots,g_n\sim N(0,1)$, and contractions $\phi_i:\mathbb{R}\to\mathbb{R}$ with $\|\phi_i\|_{\mathrm{Lip}}\le 1$, prove $\mathbb{E}\sup_{t\in T}\sum_{i=1}^n g_i\phi_i(t_i)\le \mathbb{E}\sup_{t\in T}\sum_{i=1}^n g_i t_i$. Hint: Sudakov-Fernique.

<a id="pdf-681b6f3d947f-p175-b004"></a>
<!-- pdf-source: page=175; block=4; confidence=0.90 -->
**Exercise 7.2.14 (Gordon's inequality).** Prove Y. Gordon's extension of Slepian's inequality. Let $(X_{ut})_{u\in U,t\in T}$ and $(Y_{ut})_{u\in U,t\in T}$ be two mean-zero Gaussian processes indexed by pairs in $U\times T$ (statement continues on p.176).

<a id="pdf-681b6f3d947f-p175-b005"></a>
<!-- pdf-source: page=175; block=5; confidence=0.95 -->
Footnote: the form of $f(x)$ is motivated by statistical mechanics, where the right side of (7.11) is a log-partition function and $\beta$ the inverse temperature.

<a id="pdf-681b6f3d947f-p176-b001"></a>
<!-- pdf-source: page=176; block=1; confidence=0.95 -->
**Exercise 7.2.14 (Gordon's inequality, cont.).** Assume $\mathbb{E} X_{ut}^2=\mathbb{E} Y_{ut}^2$ and: $\mathbb{E}(X_{ut}-X_{us})^2\le \mathbb{E}(Y_{ut}-Y_{us})^2$ for all $u,t,s$; and $\mathbb{E}(X_{ut}-X_{vs})^2\ge \mathbb{E}(Y_{ut}-Y_{vs})^2$ for all $u\ne v$ and all $t,s$. Then for every $\tau\ge 0$, $\mathbb{P}\{\inf_{u\in U}\sup_{t\in T}X_{ut}\ge\tau\}\le \mathbb{P}\{\inf_{u\in U}\sup_{t\in T}Y_{ut}\ge\tau\}$. Consequently $\mathbb{E}\inf_{u}\sup_{t}X_{ut}\le \mathbb{E}\inf_{u}\sup_{t}Y_{ut}$ (7.12). Hint: use Gaussian Interpolation Lemma 7.2.7 with $f(x)=\prod_i[1-\prod_j h(x_{ij})]$, $h$ approximating $\mathbf{1}_{\{x\le\tau\}}$. Remark: the equal-variance assumption can be removed (not proved here).

<a id="pdf-681b6f3d947f-p176-b002"></a>
<!-- pdf-source: page=176; block=2; confidence=0.95 -->
**Section 7.3 — Sharp bounds on Gaussian matrices.** Application of the Gaussian comparison inequalities to random matrices. Section 4.6's $\varepsilon$-net argument gave $\mathbb{E}\|A\|\le \sqrt{m}+C\sqrt{n}$ for $m\times n$ matrices with independent sub-gaussian rows (Exercise 4.6.3). Sudakov-Fernique sharpens this to $C=1$ for Gaussian matrices.

<a id="pdf-681b6f3d947f-p176-b003"></a>
<!-- pdf-source: page=176; block=3; confidence=0.98 -->
**Theorem 7.3.1 (Norms of Gaussian random matrices).** Let $A$ be an $m\times n$ matrix with independent $N(0,1)$ entries. Then $\mathbb{E}\|A\|\le \sqrt{m}+\sqrt{n}$.

<a id="pdf-681b6f3d947f-p176-b004"></a>
<!-- pdf-source: page=176; block=4; confidence=0.95 -->
**Proof.** Realize $\|A\|$ as a supremum of a Gaussian process: $\|A\|=\max_{u\in S^{n-1},\,v\in S^{m-1}}\langle Au,v\rangle=\max_{(u,v)\in T}X_{uv}$, where $T=S^{n-1}\times S^{m-1}$ and $X_{uv}:=\langle Au,v\rangle\sim N(0,1)$. (Continues on p.177.)

<a id="pdf-681b6f3d947f-p177-b001"></a>
<!-- pdf-source: page=177; block=1; confidence=0.95 -->
**Proof (cont.).** For $(u,v),(w,z)\in T$: $\mathbb{E}(X_{uv}-X_{wz})^2=\mathbb{E}\big(\sum_{i,j}A_{ij}(u_jv_i-w_jz_i)\big)^2=\sum_{i,j}(u_jv_i-w_jz_i)^2=\|uv^T-wz^T\|_F^2\le \|u-w\|_2^2+\|v-z\|_2^2$ (Exercise 7.3.2). Define $Y_{uv}:=\langle g,u\rangle+\langle h,v\rangle$ with independent $g\sim N(0,I_n)$, $h\sim N(0,I_m)$; then $\mathbb{E}(Y_{uv}-Y_{wz})^2=\|u-w\|_2^2+\|v-z\|_2^2$. Hence $\mathbb{E}(X_{uv}-X_{wz})^2\le \mathbb{E}(Y_{uv}-Y_{wz})^2$. By Sudakov-Fernique (Theorem 7.2.11), $\mathbb{E}\|A\|=\mathbb{E}\sup_{(u,v)\in T}X_{uv}\le \mathbb{E}\sup Y_{uv}=\mathbb{E}\sup_{u\in S^{n-1}}\langle g,u\rangle+\mathbb{E}\sup_{v\in S^{m-1}}\langle h,v\rangle=\mathbb{E}\|g\|_2+\mathbb{E}\|h\|_2\le (\mathbb{E}\|g\|_2^2)^{1/2}+(\mathbb{E}\|h\|_2^2)^{1/2}=\sqrt{n}+\sqrt{m}$ (by (1.3) for $L^p$ norms and Lemma 3.2.4). $\qquad\blacksquare$

<a id="pdf-681b6f3d947f-p177-b002"></a>
<!-- pdf-source: page=177; block=2; confidence=0.97 -->
**Exercise 7.3.2.** Prove the bound used above: for any $u,w\in S^{n-1}$ and $v,z\in S^{m-1}$, $\|uv^T-wz^T\|_F^2\le \|u-w\|_2^2+\|v-z\|_2^2$.

<a id="pdf-681b6f3d947f-p177-b003"></a>
<!-- pdf-source: page=177; block=3; confidence=0.95 -->
Theorem 7.3.1 gives no tail bound for $\|A\|$, but one follows automatically via the concentration inequalities of Section 5.2.

<a id="pdf-681b6f3d947f-p178-b001"></a>
<!-- pdf-source: page=178; block=1; confidence=0.90 -->
**Corollary 7.3.3 (Norms of Gaussian random matrices: tails).** Let $A$ be an $m\times n$ matrix with independent $N(0,1)$ entries. Then for every $t\ge 0$,
$$\mathbb{P}\{\|A\| \ge \sqrt{m}+\sqrt{n}+t\} \le 2\exp(-ct^2).$$

<a id="pdf-681b6f3d947f-p178-b002"></a>
<!-- pdf-source: page=178; block=2; confidence=0.93 -->
**Proof.** Combine Theorem 7.3.1 with Gaussian-space concentration (Theorem 5.2.2). Viewing $A$ as a vector in $\mathbb{R}^{m\times n}$ (rows concatenated) gives $A\sim N(0,I_{nm})$. For $f(A):=\|A\|$ one has $f(A)\le \|A\|_2$ (the Frobenius/Euclidean norm dominates the operator norm), so $A\mapsto\|A\|$ is Lipschitz with Lipschitz norm $\le 1$. Theorem 5.2.2 then yields $\mathbb{P}\{\|A\|\ge \mathbb{E}\|A\|+t\}\le 2\exp(-ct^2)$, and the bound on $\mathbb{E}\|A\|$ from Theorem 7.3.1 finishes. $\square$

<a id="pdf-681b6f3d947f-p178-b003"></a>
<!-- pdf-source: page=178; block=3; confidence=0.85 -->
**Exercise 7.3.4 (Smallest singular values).** Using Gordon's inequality (Exercise 7.2.14), prove for an $m\times n$ matrix $A$ with independent $N(0,1)$ entries the sharp bound $\mathbb{E}\,s_n(A) \ge \sqrt{m}-\sqrt{n}$, and combine with concentration to get the tail bound $\mathbb{P}\{\|A\| \le \sqrt{m}-\sqrt{n}-t\} \le 2\exp(-ct^2)$. Hint: use $s_n(A)=\min_{u\in S^{n-1}}\max_{v\in S^{m-1}}\langle Au,v\rangle$; apply Gordon's inequality (without equal-variance requirement) to get $\mathbb{E}\,s_n(A) \ge \mathbb{E}\|h\|_2 - \mathbb{E}\|g\|_2$ with $g\sim N(0,I_n)$, $h\sim N(0,I_m)$; and use that $f(n):=\mathbb{E}\|g\|_2-\sqrt{n}$ is increasing in $n$.

<a id="pdf-681b6f3d947f-p178-b004"></a>
<!-- pdf-source: page=178; block=4; confidence=0.92 -->
**Exercise 7.3.5 (Symmetric random matrices).** Adapt the arguments to bound the norm of a symmetric $n\times n$ Gaussian random matrix $A$ with above-diagonal entries independent $N(0,1)$ and diagonal entries independent $N(0,2)$ — the Gaussian orthogonal ensemble (GOE). Show $\mathbb{E}\|A\| \le 2\sqrt{n}$.

<a id="pdf-681b6f3d947f-p179-b001"></a>
<!-- pdf-source: page=179; block=1; confidence=0.92 -->
Then deduce the tail bound $\mathbb{P}\{\|A\| \ge 2\sqrt{n}+t\} \le 2\exp(-ct^2)$.

<a id="pdf-681b6f3d947f-p179-b002"></a>
<!-- pdf-source: page=179; block=2; confidence=0.90 -->
# 7.4 Sudakov's minoration inequality

Returning to mean zero Gaussian processes $(X_t)_{t\in T}$, the increments define the canonical metric on $T$:
$$d(t,s) := \|X_t-X_s\|_{L^2} = \big(\mathbb{E}(X_t-X_s)^2\big)^{1/2}. \tag{7.13}$$
The canonical metric determines the covariance and hence the distribution of the process, so the geometry of $(T,d)$ governs its probabilistic behavior.

<a id="pdf-681b6f3d947f-p179-b003"></a>
<!-- pdf-source: page=179; block=3; confidence=0.90 -->
Goal: estimate the overall magnitude $\mathbb{E}\sup_{t\in T} X_t$ (7.14) via the geometry of $(T,d)$; this section gives a lower bound in terms of metric entropy. For $\varepsilon>0$, the covering number $N(T,d,\varepsilon)$ is the smallest cardinality of an $\varepsilon$-net of $T$ (equivalently, the smallest number of closed radius-$\varepsilon$ balls covering $T$; set to $\infty$ if no finite $\varepsilon$-net exists). Its logarithm $\log_2 N(T,d,\varepsilon)$ is the metric entropy of $T$.

<a id="pdf-681b6f3d947f-p179-b004"></a>
<!-- pdf-source: page=179; block=4; confidence=0.95 -->
**Theorem 7.4.1 (Sudakov's minoration inequality).** Let $(X_t)_{t\in T}$ be a mean zero Gaussian process. Then for any $\varepsilon\ge 0$,
$$\mathbb{E}\sup_{t\in T} X_t \ge c\,\varepsilon\sqrt{\log N(T,d,\varepsilon)},$$
where $d$ is the canonical metric (7.13).

<a id="pdf-681b6f3d947f-p180-b001"></a>
<!-- pdf-source: page=180; block=1; confidence=0.94 -->
**Proof.** Deduce from Sudakov–Fernique's comparison inequality (Theorem 7.2.11). Assume $N(T,d,\varepsilon)=:N$ is finite (infinite case: Exercise 7.4.2). Let $\mathcal{N}$ be a maximal $\varepsilon$-separated subset of $T$; then $\mathcal{N}$ is an $\varepsilon$-net (Lemma 4.2.6), so $|\mathcal{N}|\ge N$. It suffices to show $\mathbb{E}\sup_{t\in\mathcal{N}} X_t \ge c\varepsilon\sqrt{\log N}$. Compare $(X_t)$ to $Y_t := \tfrac{\varepsilon}{\sqrt{2}} g_t$ with $g_t$ independent $N(0,1)$. For distinct $t,s\in\mathcal{N}$: $\mathbb{E}(X_t-X_s)^2 = d(t,s)^2 \ge \varepsilon^2$, while $\mathbb{E}(Y_t-Y_s)^2 = \tfrac{\varepsilon^2}{2}\mathbb{E}(g_t-g_s)^2 = \varepsilon^2$ (since $g_t-g_s\sim N(0,2)$). Hence $\mathbb{E}(X_t-X_s)^2 \ge \mathbb{E}(Y_t-Y_s)^2$. By Theorem 7.2.11, $\mathbb{E}\sup_{t\in\mathcal{N}} X_t \ge \mathbb{E}\sup_{t\in\mathcal{N}} Y_t = \tfrac{\varepsilon}{\sqrt{2}}\,\mathbb{E}\max_{t\in\mathcal{N}} g_t \ge c\varepsilon\sqrt{\log N}$, using $\mathbb{E}\max$ of $N$ standard normals $\ge c\sqrt{\log N}$ (Exercise 2.5.11). $\square$

<a id="pdf-681b6f3d947f-p180-b002"></a>
<!-- pdf-source: page=180; block=2; confidence=0.94 -->
**Exercise 7.4.2 (Sudakov's minoration for non-compact sets).** Show that if $(T,d)$ is not relatively compact, i.e. $N(T,d,\varepsilon)=\infty$ for some $\varepsilon>0$, then $\mathbb{E}\sup_{t\in T} X_t = \infty$.

<a id="pdf-681b6f3d947f-p181-b001"></a>
<!-- pdf-source: page=181; block=1; confidence=0.98 -->
### 7.4.1 Application for covering numbers in R^n

<a id="pdf-681b6f3d947f-p181-b002"></a>
<!-- pdf-source: page=181; block=2; confidence=0.95 -->
For T ⊂ R^n, take the canonical Gaussian process X_t := ⟨g, t⟩, t ∈ T, with g ∼ N(0, I_n). Its canonical distance is Euclidean: d(t,s) = ‖X_t − X_s‖_{L2} = ‖t − s‖_2.

<a id="pdf-681b6f3d947f-p181-b003"></a>
<!-- pdf-source: page=181; block=3; confidence=0.95 -->
**Corollary 7.4.3 (Sudakov's minoration inequality in R^n).** For T ⊂ R^n and any ε > 0, E sup_{t∈T} ⟨g, t⟩ ≥ cε √(log N(T, ε)), where N(T, ε) is the covering number of T by Euclidean balls of radius ε with centers in T (cf. Section 4.2.1).

<a id="pdf-681b6f3d947f-p181-b004"></a>
<!-- pdf-source: page=181; block=4; confidence=0.96 -->
**Corollary 7.4.4 (Covering numbers of polytopes).** Let P be a polytope in R^n with N vertices and diameter bounded by 1. Then for every ε > 0, N(P, ε) ≤ N^{C/ε^2}.

<a id="pdf-681b6f3d947f-p181-b005"></a>
<!-- pdf-source: page=181; block=5; confidence=0.94 -->
**Proof.** WLOG (by translation) the radius of P is ≤ 1. Let x_1, …, x_N be the vertices. Since a linear function attains its maximum on the convex set P at a vertex, E sup_{t∈P} ⟨g, t⟩ = E sup_{i≤N} ⟨g, x_i⟩ ≤ C√(log N); the bound uses Exercise 2.5.10 with ⟨g, x⟩ ∼ N(0, ‖x‖_2^2) and ‖x‖_2 ≤ 1. Substituting into Corollary 7.4.3 and simplifying gives the claim. ∎

<a id="pdf-681b6f3d947f-p181-b006"></a>
<!-- pdf-source: page=181; block=6; confidence=0.94 -->
**Exercise 7.4.5 (Volume of polytopes).** For a polytope P ⊂ R^n with N vertices contained in the unit ball B_2^n, show Vol(P)/Vol(B_2^n) ≤ (C log N / n)^{Cn}. Hint: use Proposition 4.2.12, Corollary 7.4.4, and optimize in ε.

<a id="pdf-681b6f3d947f-p182-b001"></a>
<!-- pdf-source: page=182; block=1; confidence=0.98 -->
## 7.5 Gaussian width

<a id="pdf-681b6f3d947f-p182-b002"></a>
<!-- pdf-source: page=182; block=2; confidence=0.93 -->
The quantity E sup_{t∈T} ⟨g, t⟩ (g ∼ N(0, I_n)), the magnitude of the canonical Gaussian process on T, is central in high-dimensional probability; it is named and studied next.

<a id="pdf-681b6f3d947f-p182-b003"></a>
<!-- pdf-source: page=182; block=3; confidence=0.97 -->
**Definition 7.5.1.** The Gaussian width of T ⊂ R^n is w(T) := E sup_{x∈T} ⟨g, x⟩, where g ∼ N(0, I_n).

<a id="pdf-681b6f3d947f-p182-b004"></a>
<!-- pdf-source: page=182; block=4; confidence=0.93 -->
Equivalent or nearly-equivalent variants (see Section 7.6): E sup_{x∈T} |⟨g, x⟩|, (E sup_{x∈T} ⟨g, x⟩^2)^{1/2}, and E sup_{x,y∈T} ⟨g, x − y⟩.

<a id="pdf-681b6f3d947f-p182-b005"></a>
<!-- pdf-source: page=182; block=5; confidence=0.95 -->
**Proposition 7.5.2 (Gaussian width; §7.5.1 Basic properties).**
(a) w(T) is finite iff T is bounded.
(b) Invariant under affine unitary transformations: for orthogonal U and any y, w(UT + y) = w(T).
(c) Invariant under convex hull: w(conv(T)) = w(T).
(d) Respects Minkowski addition and scaling: w(T + S) = w(T) + w(S); w(aT) = |a| w(T) for a ∈ R.
(e) w(T) = ½ w(T − T) = ½ E sup_{x,y∈T} ⟨g, x − y⟩.

<a id="pdf-681b6f3d947f-p183-b001"></a>
<!-- pdf-source: page=183; block=1; confidence=0.95 -->
**Proposition 7.5.2 (f) (Gaussian width and diameter).** (1/√(2π))·diam(T) ≤ w(T) ≤ (√n / 2)·diam(T).

<a id="pdf-681b6f3d947f-p183-b002"></a>
<!-- pdf-source: page=183; block=2; confidence=0.93 -->
**Proof.** Properties (a)–(d) are left to Exercise 7.5.3.
(e): Using (d) twice, w(T) = ½[w(T) + w(T)] = ½[w(T) + w(−T)] = ½ w(T − T).
Lower bound in (f): fix x, y ∈ T; both x − y and y − x lie in T − T, so by (e), w(T) ≥ ½ E max(⟨x−y, g⟩, ⟨y−x, g⟩) = ½ E|⟨x−y, g⟩| = ½ √(2/π) ‖x−y‖_2, since ⟨x−y, g⟩ ∼ N(0, ‖x−y‖_2^2) and E|X| = √(2/π) for X ∼ N(0,1); take sup over x, y.
Upper bound in (f): w(T) = ½ E sup_{x,y∈T} ⟨g, x−y⟩ ≤ ½ E sup_{x,y∈T} ‖g‖_2 ‖x−y‖_2 ≤ ½ E‖g‖_2 · diam(T), and E‖g‖_2 ≤ (E‖g‖_2^2)^{1/2} = √n. ∎

<a id="pdf-681b6f3d947f-p183-b003"></a>
<!-- pdf-source: page=183; block=3; confidence=0.95 -->
**Exercise 7.5.3.** Prove properties (a)–(d) of Proposition 7.5.2. Hint: use rotation invariance of the Gaussian distribution.

<a id="pdf-681b6f3d947f-p183-b004"></a>
<!-- pdf-source: page=183; block=4; confidence=0.95 -->
**Exercise 7.5.4 (Gaussian width under linear transformations).** For any m × n matrix A, show w(AT) ≤ ‖A‖ w(T). Hint: use the Sudakov–Fernique comparison inequality.

<a id="pdf-681b6f3d947f-p183-b005"></a>
<!-- pdf-source: page=183; block=5; confidence=0.90 -->
### 7.5.2 Geometric meaning of width
The width of T in direction θ ∈ S^{n−1} is the smallest width of the slab (between parallel hyperplanes orthogonal to θ) containing T (Figure 7.3).

<a id="pdf-681b6f3d947f-p183-b006"></a>
<!-- pdf-source: page=183; block=6; confidence=0.96 -->
Footnote: diam(T) := sup{‖x − y‖_2 : x, y ∈ T}.

<a id="pdf-681b6f3d947f-p184-b001"></a>
<!-- pdf-source: page=184; block=1; confidence=0.90 -->
The width of $T\subset\mathbb{R}^n$ in unit direction $\theta$ is $\sup_{x,y\in T}\langle\theta,x-y\rangle$. Averaging over unit directions $\theta$ gives the quantity
$$\mathbb{E}\,\sup_{x,y\in T}\langle\theta,x-y\rangle.\tag{7.15}$$

<a id="pdf-681b6f3d947f-p184-b002"></a>
<!-- pdf-source: page=184; block=2; confidence=0.95 -->
**Definition 7.5.5 (Spherical width).** The spherical width of $T\subset\mathbb{R}^n$ is $w_s(T):=\mathbb{E}\,\sup_{x\in T}\langle\theta,x\rangle$ where $\theta\sim\mathrm{Unif}(S^{n-1})$. The quantity (7.15) equals $w_s(T-T)$. (Also called the mean width.)

<a id="pdf-681b6f3d947f-p184-b003"></a>
<!-- pdf-source: page=184; block=3; confidence=0.85 -->
Gaussian and spherical widths differ only in the averaging vector: $g\sim N(0,I_n)$ vs. $\theta\sim\mathrm{Unif}(S^{n-1})$; both are rotation invariant, and $g$ is about $\sqrt{n}$ times longer than $\theta$, so Gaussian width is roughly a $\sqrt{n}$ scaling of spherical width.

<a id="pdf-681b6f3d947f-p184-b004"></a>
<!-- pdf-source: page=184; block=4; confidence=0.95 -->
**Lemma 7.5.6 (Gaussian vs. spherical widths).** $(\sqrt{n}-C)\,w_s(T)\le w(T)\le(\sqrt{n}+C)\,w_s(T).$

<a id="pdf-681b6f3d947f-p184-b005"></a>
<!-- pdf-source: page=184; block=5; confidence=0.95 -->
**Proof.** Write $g=\|g\|_2\cdot g/\|g\|_2=:r\theta$. By Section 3.3.3, $r$ and $\theta$ are independent and $\theta\sim\mathrm{Unif}(S^{n-1})$. Hence
$$w(T)=\mathbb{E}\,\sup_{x\in T}\langle r\theta,x\rangle=(\mathbb{E}\,r)\cdot\mathbb{E}\,\sup_{x\in T}\langle\theta,x\rangle=\mathbb{E}\|g\|_2\cdot w_s(T).$$
Concentration of the norm gives $\big|\mathbb{E}\|g\|_2-\sqrt{n}\big|\le C$ (Exercise 3.1.4). $\square$

<a id="pdf-681b6f3d947f-p185-b001"></a>
<!-- pdf-source: page=185; block=1; confidence=0.95 -->
**7.5.3 Examples**

<a id="pdf-681b6f3d947f-p185-b002"></a>
<!-- pdf-source: page=185; block=2; confidence=0.95 -->
**Example 7.5.7 (Euclidean ball and sphere).** $w(S^{n-1})=w(B_2^n)=\mathbb{E}\|g\|_2=\sqrt{n}\pm C$ (7.16), by Exercise 3.1.4. Their spherical widths equal $1$.

<a id="pdf-681b6f3d947f-p185-b003"></a>
<!-- pdf-source: page=185; block=3; confidence=0.95 -->
**Example 7.5.8 (Cube).** For the $\ell_\infty$ unit ball $B_\infty^n=[-1,1]^n$,
$$w(B_\infty^n)=\mathbb{E}\|g\|_1=\mathbb{E}|g_1|\cdot n=\sqrt{\tfrac{2}{\pi}}\,n.\tag{7.17}$$
By (7.16), the cube $B_\infty^n$ and its circumscribed ball $\sqrt{n}\,B_2^n$ have the same order $n$.

<a id="pdf-681b6f3d947f-p185-b004"></a>
<!-- pdf-source: page=185; block=4; confidence=0.95 -->
**Example 7.5.9 ($\ell_1$ ball).** The $\ell_1$ unit ball $B_1^n=\{x\in\mathbb{R}^n:\|x\|_1\le1\}$ (cross-polytope) satisfies
$$c\sqrt{\log n}\le w(B_1^n)\le C\sqrt{\log n}\tag{7.18}$$
since $w(B_1^n)=\mathbb{E}\|g\|_\infty=\mathbb{E}\max_{i\le n}|g_i|$; bounds from Exercises 2.5.10 and 2.5.11. Thus $B_1^n$ and its inscribed ball $\tfrac{1}{\sqrt{n}}B_2^n$ have almost the same order (up to a log factor).

<a id="pdf-681b6f3d947f-p186-b001"></a>
<!-- pdf-source: page=186; block=1; confidence=0.95 -->
**Exercise 7.5.10 (Finite point sets).** For a finite set $T\subset\mathbb{R}^n$, show $w(T)\le C\sqrt{\log|T|}\cdot\mathrm{diam}(T)$. Hint: argue as in the proof of Corollary 7.4.4.

<a id="pdf-681b6f3d947f-p186-b002"></a>
<!-- pdf-source: page=186; block=2; confidence=0.95 -->
**Exercise 7.5.11 ($\ell_p$ balls).** For $1\le p<\infty$ and $B_p^n=\{x\in\mathbb{R}^n:\|x\|_p\le1\}$, show $w(B_p^n)\le C\sqrt{p'}\,n^{1/p'}$, where $p'$ is the conjugate exponent with $\tfrac{1}{p}+\tfrac{1}{p'}=1$.

<a id="pdf-681b6f3d947f-p186-b003"></a>
<!-- pdf-source: page=186; block=3; confidence=0.95 -->
**7.5.4 Surprising behavior of width in high dimensions**

<a id="pdf-681b6f3d947f-p186-b004"></a>
<!-- pdf-source: page=186; block=4; confidence=0.85 -->
From Example 7.5.9, the spherical width of $B_1^n$ is $w_s(B_1^n)\asymp\sqrt{\tfrac{\log n}{n}}$, far smaller than its diameter $2$. The Gaussian width of $B_1^n$ nearly matches that of its inscribed ball $\tfrac{1}{\sqrt{n}}B_2^n$ (diameter $\tfrac{2}{\sqrt{n}}$), up to a log factor, despite $B_1^n$ appearing much larger. Intuitive explanation: in high dimensions the cube $B_\infty^n$ has $2^n$ vertices and extends to radius near $\sqrt{n}$ in most directions, nearly filling its enclosing ball; the volumes of the cube and its circumscribed ball are both of order $C^n$.

<a id="pdf-681b6f3d947f-p187-b001"></a>
<!-- pdf-source: page=187; block=1; confidence=0.90 -->
Motivational discussion: the octahedron $B^n_1$ has only $2n$ vertices, so a random direction $\theta$ is nearly orthogonal to all of them and the vertices barely affect the width. The width is governed by the "bulk" — the inscribed Euclidean ball. Volumetrically, $B^n_1$ and its inscribed ball both have volume of order $(C/n)^n$, so Gaussian width and volume give the same conclusion. Milman's hyperbolic picture (Figure 7.6) illustrates bulk and outliers but may distort convexity.

<a id="pdf-681b6f3d947f-p187-b002"></a>
<!-- pdf-source: page=187; block=2; confidence=0.97 -->
**Section 7.6 — Stable dimension, stable rank, and Gaussian complexity.** Gaussian width gives a more robust replacement for the linear-algebraic dimension $\dim T$ of $T\subset\mathbb{R}^n$ (the smallest dimension of an affine subspace containing $T$), which is unstable under small perturbations. The section works with the squared Gaussian width
$$h(T)^2 := \mathbb{E}\sup_{t\in T}\langle g,t\rangle^2,\qquad g\sim N(0,I_n).\tag{7.19}$$

<a id="pdf-681b6f3d947f-p188-b001"></a>
<!-- pdf-source: page=188; block=1; confidence=0.96 -->
**Exercise 7.6.1 (Equivalence).** Show the squared and usual Gaussian widths are equivalent up to constants:
$$w(T-T)\le h(T-T)\le w(T-T)+C_1\operatorname{diam}(T)\le C\,w(T-T).$$
In particular
$$2w(T)\le h(T-T)\le 2C\,w(T).\tag{7.20}$$
Hint: use Gaussian concentration for the upper bound.

<a id="pdf-681b6f3d947f-p188-b002"></a>
<!-- pdf-source: page=188; block=2; confidence=0.97 -->
**Definition 7.6.2 (Stable dimension).** For a bounded $T\subset\mathbb{R}^n$, the stable dimension is
$$d(T):=\frac{h(T-T)^2}{\operatorname{diam}(T)^2}\;\asymp\;\frac{w(T)^2}{\operatorname{diam}(T)^2}.$$

<a id="pdf-681b6f3d947f-p188-b003"></a>
<!-- pdf-source: page=188; block=3; confidence=0.97 -->
**Lemma 7.6.3.** For any $T\subset\mathbb{R}^n$, $\;d(T)\le \dim(T)$.

<a id="pdf-681b6f3d947f-p188-b004"></a>
<!-- pdf-source: page=188; block=4; confidence=0.96 -->
**Proof.** Let $\dim T=k$, so $T$ lies in a $k$-dimensional subspace $E$; by rotation invariance take $E=\mathbb{R}^k$. Then
$$h(T-T)^2=\mathbb{E}\sup_{x,y\in T}\langle g,x-y\rangle^2.$$
Since $x-y\in\mathbb{R}^k$ with $\|x-y\|_2\le\operatorname{diam}(T)$, write $x-y=\operatorname{diam}(T)\cdot z$ with $z\in B_2^k$. The quantity is bounded by
$$\operatorname{diam}(T)^2\,\mathbb{E}\sup_{z\in B_2^k}\langle g,z\rangle^2=\operatorname{diam}(T)^2\,\mathbb{E}\|g'\|_2^2=\operatorname{diam}(T)^2\cdot k,$$
where $g'\sim N(0,I_k)$. Hence $d(T)\le k$. $\square$

<a id="pdf-681b6f3d947f-p188-b005"></a>
<!-- pdf-source: page=188; block=5; confidence=0.96 -->
**Exercise 7.6.4.** The bound $d(T)\le\dim(T)$ is sharp: if $T$ is a Euclidean ball in any subspace of $\mathbb{R}^n$, then $d(T)=\dim(T)$.

<a id="pdf-681b6f3d947f-p188-b006"></a>
<!-- pdf-source: page=188; block=6; confidence=0.96 -->
**Example 7.6.5.** For a finite set $T\subset\mathbb{R}^n$, $\;d(T)\le C\log|T|$, which follows from the Gaussian width bound in Exercise 7.5.10.

<a id="pdf-681b6f3d947f-p189-b001"></a>
<!-- pdf-source: page=189; block=1; confidence=0.92 -->
**Subsection 7.6.1 — Stable rank.** Stable dimension is robust: small perturbations of $T$ change $w(T)$, $\operatorname{diam}(T)$, and hence $d(T)$ only slightly. Example: shrinking one axis of $B_2^n$ from 1 to 0 keeps the algebraic dimension at $n$ then makes it jump to $n-1$, whereas the stable dimension decreases gradually from $n$ to $n-1$.

<a id="pdf-681b6f3d947f-p189-b002"></a>
<!-- pdf-source: page=189; block=2; confidence=0.95 -->
**Exercise 7.6.6 (Ellipsoids).** For an $m\times n$ matrix $A$ and unit ball $B_2^n$, the squared mean width of the ellipsoid $AB_2^n$ equals the Frobenius norm: $h(AB_2^n)=\|A\|_F$. Deduce
$$d(AB_2^n)=\frac{\|A\|_F^2}{\|A\|^2}.\tag{7.21}$$

<a id="pdf-681b6f3d947f-p189-b003"></a>
<!-- pdf-source: page=189; block=3; confidence=0.96 -->
**Definition 7.6.7 (Stable rank).** The stable rank of an $m\times n$ matrix $A$ is
$$r(A):=\frac{\|A\|_F^2}{\|A\|^2}.$$
Since $\operatorname{rank}(A)=\dim(AB_2^n)$ and, by (7.21), $r(A)=d(AB_2^n)$, the stable rank is the stable dimension of the image. Always $r(A)\le\operatorname{rank}(A)$.

<a id="pdf-681b6f3d947f-p189-b004"></a>
<!-- pdf-source: page=189; block=4; confidence=0.90 -->
**Subsection 7.6.2 — Gaussian complexity.** Introduces a further variant of Gaussian width in which, instead of squaring $\langle g,x\rangle$ as in (7.19), one takes the absolute value.

<a id="pdf-681b6f3d947f-p190-b001"></a>
<!-- pdf-source: page=190; block=1; confidence=0.98 -->
**Definition 7.6.8 (Gaussian complexity).** For $T \subset \mathbb{R}^n$, $\gamma(T) := \mathbb{E}\sup_{x\in T}|\langle g, x\rangle|$ with $g \sim N(0, I_n)$.

<a id="pdf-681b6f3d947f-p190-b002"></a>
<!-- pdf-source: page=190; block=2; confidence=0.96 -->
Always $w(T) \le \gamma(T)$, with equality when $T$ is origin-symmetric ($T = -T$). Since $T - T$ is origin-symmetric, property (e) of Proposition 7.5.2 gives $w(T) = \tfrac12 w(T-T) = \tfrac12 \gamma(T-T)$ (7.22). Width and complexity can differ in general (e.g. a single nonzero point has $w(T)=0$, $\gamma(T)>0$).

<a id="pdf-681b6f3d947f-p190-b003"></a>
<!-- pdf-source: page=190; block=3; confidence=0.95 -->
**Exercise 7.6.9.** For $T \subset \mathbb{R}^n$ and $y \in T$, show $\tfrac13\big(w(T)+\|y\|_2\big) \le \gamma(T) \le 2\big(w(T)+\|y\|_2\big)$ (constants may vary). In particular, if $T$ contains the origin then $w(T) \le \gamma(T) \le 2w(T)$.

<a id="pdf-681b6f3d947f-p190-b004"></a>
<!-- pdf-source: page=190; block=4; confidence=0.99 -->
**7.7 Random projections of sets**

<a id="pdf-681b6f3d947f-p190-b005"></a>
<!-- pdf-source: page=190; block=5; confidence=0.95 -->
Motivates Gaussian/spherical width in dimension reduction: project $T \subset \mathbb{R}^n$ onto a random $m$-dimensional subspace $P$ (uniform on Grassmannian $G_{n,m}$) and ask about $\mathrm{diam}(PT)$. For finite $T$, the Johnson–Lindenstrauss Lemma (Theorem 5.3.1) says that if $m \gtrsim \log|T|$ (7.23), then $P$ shrinks distances by $\approx \sqrt{m/n}$, so $\mathrm{diam}(PT) \approx \sqrt{m/n}\,\mathrm{diam}(T)$ (7.24). For large or infinite $T$, (7.24) may fail.

<a id="pdf-681b6f3d947f-p191-b001"></a>
<!-- pdf-source: page=191; block=1; confidence=0.95 -->
If $T = B_2^n$ (Euclidean ball), no projection shrinks it: $\mathrm{diam}(PT) = \mathrm{diam}(T)$ (7.25). For general $T$, a random projection shrinks $T$ as in (7.24) but cannot shrink below the spherical width of $T$.

<a id="pdf-681b6f3d947f-p191-b002"></a>
<!-- pdf-source: page=191; block=2; confidence=0.97 -->
**Theorem 7.7.1 (Sizes of random projections of sets).** For bounded $T \subset \mathbb{R}^n$ and $P$ a projection onto a random $m$-dimensional subspace $E \sim \mathrm{Unif}(G_{n,m})$, with probability at least $1 - 2e^{-m}$, $\mathrm{diam}(PT) \le C\big[w_s(T) + \sqrt{m/n}\,\mathrm{diam}(T)\big].$

<a id="pdf-681b6f3d947f-p191-b003"></a>
<!-- pdf-source: page=191; block=3; confidence=0.94 -->
As in the Johnson–Lindenstrauss proof (Proposition 5.3.2), pass to an equivalent model: realize a random subspace $E$ by a random rotation of a fixed subspace $\mathbb{R}^m$, and equivalently fix the subspace while randomly rotating $T$.

<a id="pdf-681b6f3d947f-p191-b004"></a>
<!-- pdf-source: page=191; block=4; confidence=0.96 -->
**Exercise 7.7.2.** Let $P$ project onto random $E \sim \mathrm{Unif}(G_{n,m})$, and let $Q$ be the $m\times n$ matrix of the first $m$ rows of $U \sim \mathrm{Unif}(O(n))$. (a) For fixed $x \in \mathbb{R}^n$, $\|Px\|_2$ and $\|Qx\|_2$ have the same distribution (hint: SVD of $P$). (b) For fixed $z \in S^{m-1}$, $Q^{\mathsf T}z \sim \mathrm{Unif}(S^{n-1})$, so $Q^{\mathsf T}$ is a random isometric embedding of $\mathbb{R}^m$ into $\mathbb{R}^n$ (hint: rotation invariance).

<a id="pdf-681b6f3d947f-p191-b005"></a>
<!-- pdf-source: page=191; block=5; confidence=0.95 -->
**Proof.** An $\varepsilon$-net argument; WLOG $\mathrm{diam}(T) \le 1$. **Step 1 (Approximation).** By Exercise 7.7.2 it suffices to prove the theorem for $Q$, bounding $\mathrm{diam}(QT) = \sup_{x\in T-T}\|Qx\|_2 = \sup_{x\in T-T}\max_{z\in S^{m-1}}\langle Qx, z\rangle$. Discretize $S^{m-1}$ with a $(1/2)$-net $N$ satisfying $|N| \le 5^m$.

<a id="pdf-681b6f3d947f-p192-b001"></a>
<!-- pdf-source: page=192; block=1; confidence=0.95 -->
By Corollary 4.2.13 such a net exists. Replacing the supremum over $S^{m-1}$ by the maximum over $N$ costs a factor 2: $\mathrm{diam}(QT) \le 2\sup_{x\in T-T}\max_{z\in N}\langle Qx, z\rangle = 2\max_{z\in N}\sup_{x\in T-T}\langle Q^{\mathsf T}z, x\rangle$ (7.26) (Exercise 4.4.2). Plan: control $\sup_{x\in T-T}\langle Q^{\mathsf T}z, x\rangle$ (7.27) for fixed $z$ with high probability, then union bound over $z$.

<a id="pdf-681b6f3d947f-p192-b002"></a>
<!-- pdf-source: page=192; block=2; confidence=0.96 -->
**Step 2 (Concentration).** Fix $z \in N$; by Exercise 7.7.2, $Q^{\mathsf T}z \sim \mathrm{Unif}(S^{n-1})$, so $\mathbb{E}\sup_{x\in T-T}\langle Q^{\mathsf T}z, x\rangle = w_s(T-T) = 2w_s(T)$ (spherical analogue of Proposition 7.5.2(e)). The map $\theta \mapsto \sup_{x\in T-T}\langle \theta, x\rangle$ is Lipschitz on $S^{n-1}$ with norm $\le 1$ (since $\mathrm{diam}(T)\le 1$), so concentration inequality (5.6) gives $\mathbb{P}\{\sup_{x\in T-T}\langle Q^{\mathsf T}z, x\rangle \ge 2w_s(T) + t\} \le 2\exp(-cnt^2)$.

<a id="pdf-681b6f3d947f-p192-b003"></a>
<!-- pdf-source: page=192; block=3; confidence=0.95 -->
**Step 3 (Union bound).** Over $N$: $\mathbb{P}\{\max_{z\in N}\sup_{x\in T-T}\langle Q^{\mathsf T}z, x\rangle \ge 2w_s(T) + t\} \le |N|\cdot 2\exp(-cnt^2)$ (7.28). With $|N| \le 5^m$ and $t = C\sqrt{m/n}$ for large $C$, this is $\le 2e^{-m}$. Combining (7.28) and (7.26): $\mathbb{P}\{\tfrac12\mathrm{diam}(QT) \ge 2w_s(T) + C\sqrt{m/n}\} \le e^{-m}$, proving Theorem 7.7.1. $\blacksquare$

<a id="pdf-681b6f3d947f-p193-b001"></a>
<!-- pdf-source: page=193; block=1; confidence=0.95 -->
**Exercise 7.7.3 (Gaussian projection).** Prove an analogue of Theorem 7.7.1 for an $m \times n$ Gaussian matrix $G$ with i.i.d. $N(0,1)$ entries: for any bounded $T \subset \mathbb{R}^n$,
$$\operatorname{diam}(GT) \le C\big[w(T) + \sqrt{m}\,\operatorname{diam}(T)\big]$$
with probability at least $1 - 2e^{-m}$, where $w(T)$ is the Gaussian width of $T$.

<a id="pdf-681b6f3d947f-p193-b002"></a>
<!-- pdf-source: page=193; block=2; confidence=0.95 -->
**Exercise 7.7.4 (The reverse bound).** Show Theorem 7.7.1 is optimal by proving the reverse bound, for all bounded $T \subset \mathbb{R}^n$,
$$\mathbb{E}\,\operatorname{diam}(PT) \ge c\Big[w_s(T) + \sqrt{\tfrac{m}{n}}\,\operatorname{diam}(T)\Big].$$
Hint: for the $\gtrsim w_s(T)$ part, reduce $P$ to a one-dimensional projection by dropping terms from its singular value decomposition; for the $\ge \sqrt{m/n}\,\operatorname{diam}(T)$ part, argue about a pair of points in $T$.

<a id="pdf-681b6f3d947f-p193-b003"></a>
<!-- pdf-source: page=193; block=3; confidence=0.95 -->
**Exercise 7.7.5 (Random projections of matrices).** Let $A$ be an $n \times k$ matrix.

(a) If $P$ projects $\mathbb{R}^n$ onto a random $m$-dimensional subspace chosen uniformly in $G_{n,m}$, then with probability $\ge 1 - 2e^{-m}$,
$$\|PA\| \le C\Big[\tfrac{1}{\sqrt{n}}\|A\|_F + \sqrt{\tfrac{m}{n}}\,\|A\|\Big].$$

(b) If $G$ is an $m \times n$ Gaussian matrix with i.i.d. $N(0,1)$ entries, then with probability $\ge 1 - 2e^{-m}$,
$$\|GA\| \le C\big(\|A\|_F + \sqrt{m}\,\|A\|\big).$$

Hint: relate $\|PA\|$ to the diameter of the ellipsoid $P(AB_2^k)$; use Theorem 7.7.1 for (a) and Exercise 7.7.3 for (b).

<a id="pdf-681b6f3d947f-p193-b004"></a>
<!-- pdf-source: page=193; block=4; confidence=0.90 -->
**7.7.1 The phase transition.** Theorem 7.7.1 can equivalently be written as
$$\operatorname{diam}(PT) \le C\max\Big[w_s(T),\ \sqrt{\tfrac{m}{n}}\,\operatorname{diam}(T)\Big].$$
The transition dimension $m$ between the two terms $w_s(T)$ and $\sqrt{m/n}\,\operatorname{diam}(T)$ is found by setting them equal and solving for $m$.

<a id="pdf-681b6f3d947f-p194-b001"></a>
<!-- pdf-source: page=194; block=1; confidence=0.90 -->
Solving for $m$ gives the transition at
$$m = \frac{(\sqrt{n}\,w_s(T))^2}{\operatorname{diam}(T)^2} \asymp \frac{w(T)^2}{\operatorname{diam}(T)^2} \asymp d(T),$$
using Lemma 7.5.6 to pass to Gaussian width and Definition 7.6.2 of stable dimension. Hence Theorem 7.7.1 reads:
$$\operatorname{diam}(PT) \le \begin{cases} C\sqrt{m/n}\,\operatorname{diam}(T), & m \ge d(T),\\ C\,w_s(T), & m \le d(T). \end{cases}$$

<a id="pdf-681b6f3d947f-p194-b002"></a>
<!-- pdf-source: page=194; block=2; confidence=0.90 -->
Figure 7.7 plots $\operatorname{diam}(PT)$ against $m$. For large $m$ the projection shrinks $T$ by $\sim\sqrt{m/n}$ (as in (7.24), Johnson–Lindenstrauss); once $m$ drops below the stable dimension $d(T)$ the shrinking stops and levels off at the spherical width $w_s(T)$ (cf. (7.25), where a Euclidean ball cannot be shrunk by projection).

<a id="pdf-681b6f3d947f-p194-b003"></a>
<!-- pdf-source: page=194; block=3; confidence=0.85 -->
**7.8 Notes.** Bibliographic notes. Slepian's inequality (Thm 7.2.1) is due to Slepian, with modern proofs in several references; the Sudakov–Fernique inequality (Thm 7.2.11) is attributed to Sudakov and Fernique. The Section 7.2 proofs follow the Kahane approach and a Chatterjee smoothing argument.

<a id="pdf-681b6f3d947f-p195-b001"></a>
<!-- pdf-source: page=195; block=1; confidence=0.88 -->
Notes continued (bibliographic): sources for Gordon's inequality and its optimization applications, comparison inequalities in random matrix theory (Gordon, Szarek), and Sudakov's minoration (Thm 7.4.1). The volume bound of Exercise 7.4.5 can be strengthened, using the covering-number bound of Exercise 0.0.6, to
$$\frac{\operatorname{Vol}(P)}{\operatorname{Vol}(B_2^n)} \le \Big(\frac{C\log(1+N/n)}{n}\Big)^{n/2},$$
which is best possible up to $C$. Definitions noted: stable dimension $d(T)$ (new; for a closed convex cone the squared Gaussian width $h(T)$ from (7.19) is the statistical dimension); stable (effective/numerical) rank $r(A) = \|A\|_F^2/\|A\|^2$; and intrinsic dimension $k(\Sigma) = \operatorname{tr}(\Sigma)/\|\Sigma\|$ (elsewhere also called stable rank of a PSD matrix). If $\Sigma = A^{\mathsf T}A$ or $\Sigma = AA^{\mathsf T}$ then $k(\Sigma) = r(A)$.

<a id="pdf-681b6f3d947f-p196-b001"></a>
<!-- pdf-source: page=196; block=1; confidence=0.95 -->
Bibliographic note: Theorem 7.7.1 and its improvement (given in Section 9.2.2) are due to V. Milman [149]; see also [11, Proposition 5.7.1].

<a id="pdf-681b6f3d947f-p197-b001"></a>
<!-- pdf-source: page=197; block=1; confidence=0.98 -->
# 8 Chaining

<a id="pdf-681b6f3d947f-p197-b002"></a>
<!-- pdf-source: page=197; block=2; confidence=0.90 -->
Overview of chaining as a technique for uniform bounds on a random process $(X_t)_{t\in T}$. Section 8.1: Dudley's bound via covering numbers of $T$. Section 8.2: applications to Monte-Carlo integration and a uniform law of large numbers. Section 8.3: bounds via the (combinatorial) VC dimension; Section 8.4: statistical learning theory. Sudakov's (Section 7.4) and Dudley's inequalities are sharp up to a logarithmic factor that cannot be removed in general. Section 8.5: a sharp upper bound with no logarithmic gap via Talagrand's functional $\gamma_2(T)$, proved by generic chaining. Section 8.6: matching lower bound (stated without proof), giving the two-sided majorizing measure theorem (Theorem 8.6.1); its consequence, Talagrand's comparison inequality (Corollary 8.6.2), generalizes the Sudakov–Fernique inequality to all sub-gaussian processes. Section 8.7: Chevet's inequality.

<a id="pdf-681b6f3d947f-p197-b003"></a>
<!-- pdf-source: page=197; block=3; confidence=0.98 -->
## 8.1 Dudley's inequality

<a id="pdf-681b6f3d947f-p197-b004"></a>
<!-- pdf-source: page=197; block=4; confidence=0.92 -->
Sudakov's minoration inequality (Section 7.4) gives a lower bound on $\mathbb{E}\sup_{t\in T} X_t$ for a Gaussian process $(X_t)_{t\in T}$ in terms of the metric entropy of $T$; this section obtains a similar upper bound.

<a id="pdf-681b6f3d947f-p198-b001"></a>
<!-- pdf-source: page=198; block=1; confidence=0.90 -->
The upper bound applies not only to Gaussian processes but to more general processes with sub-gaussian increments.

<a id="pdf-681b6f3d947f-p198-b002"></a>
<!-- pdf-source: page=198; block=2; confidence=0.97 -->
**Definition 8.1.1 (Sub-gaussian increments).** A random process $(X_t)_{t\in T}$ on a metric space $(T,d)$ has sub-gaussian increments if there exists $K\ge 0$ such that
$$\lVert X_t - X_s\rVert_{\psi_2} \le K\, d(t,s) \quad \text{for all } t,s\in T. \tag{8.1}$$

<a id="pdf-681b6f3d947f-p198-b003"></a>
<!-- pdf-source: page=198; block=3; confidence=0.95 -->
**Example 8.1.2.** For a Gaussian process $(X_t)_{t\in T}$ on an abstract set $T$, define the metric $d(t,s) := \lVert X_t - X_s\rVert_{L^2}$. Then $(X_t)_{t\in T}$ has sub-gaussian increments with $K$ an absolute constant.

<a id="pdf-681b6f3d947f-p198-b004"></a>
<!-- pdf-source: page=198; block=4; confidence=0.96 -->
**Theorem 8.1.3 (Dudley's integral inequality).** Let $(X_t)_{t\in T}$ be a mean-zero random process on a metric space $(T,d)$ with sub-gaussian increments as in (8.1). Then
$$\mathbb{E}\sup_{t\in T} X_t \le CK \int_0^\infty \sqrt{\log N(T,d,\varepsilon)}\; d\varepsilon.$$

<a id="pdf-681b6f3d947f-p198-b005"></a>
<!-- pdf-source: page=198; block=5; confidence=0.90 -->
Comparison with Sudakov's inequality (Theorem 7.4.1), which for Gaussian processes states
$$\mathbb{E}\sup_{t\in T} X_t \ge c\,\sup_{\varepsilon>0}\, \varepsilon\,\sqrt{\log N(T,d,\varepsilon)}.$$
There is a gap between the two bounds (illustrated in Figure 8.1) that cannot be closed using entropy numbers alone. Dudley's bound is multi-scale, examining $T$ at all scales $\varepsilon$; the proof proceeds via a discrete version summing over dyadic scales $\varepsilon = 2^{-k}$ (resembling a Riemann sum) before passing to the integral form.

<a id="pdf-681b6f3d947f-p198-b006"></a>
<!-- pdf-source: page=198; block=6; confidence=0.96 -->
**Theorem 8.1.4 (Discrete Dudley's inequality).** Let $(X_t)_{t\in T}$ be a mean-zero random process on a metric space $(T,d)$ with sub-gaussian increments as in (8.1). Then
$$\mathbb{E}\sup_{t\in T} X_t \le CK \sum_{k\in\mathbb{Z}} 2^{-k}\sqrt{\log N(T,d,2^{-k})}. \tag{8.2}$$

<a id="pdf-681b6f3d947f-p199-b001"></a>
<!-- pdf-source: page=199; block=1; confidence=0.95 -->
Figure 8.1: Dudley's inequality upper-bounds $\mathbb{E}\sup_{t\in T} X_t$ by the area under the covering-number curve; Sudakov's inequality lower-bounds the same quantity (up to constants) by the largest rectangle fitting under that curve.

<a id="pdf-681b6f3d947f-p199-b002"></a>
<!-- pdf-source: page=199; block=2; confidence=0.92 -->
Chaining is a multi-scale version of the $\varepsilon$-net argument (used earlier in Theorems 4.4.5 and 7.7.1). Single-scale recap: pick an $\varepsilon$-net $N$ of $T$; each $t\in T$ has a nearest net point $\pi(t)\in N$ with $d(t,\pi(t))\le\varepsilon$. The increment condition (8.1) gives

$$\lVert X_t - X_{\pi(t)}\rVert_{\psi_2} \le K\varepsilon. \tag{8.3}$$

Decompose $\mathbb{E}\sup_{t\in T} X_t \le \mathbb{E}\sup_{t\in T} X_{\pi(t)} + \mathbb{E}\sup_{t\in T}(X_t - X_{\pi(t)})$: the first term is controlled by a union bound over $|N| = \mathcal{N}(T,d,\varepsilon)$ points; the second cannot be handled by (8.3) alone (which holds only for fixed $t$), motivating progressively finer nets $\pi_1(t),\pi_2(t),\dots$ — i.e. chaining.

<a id="pdf-681b6f3d947f-p199-b003"></a>
<!-- pdf-source: page=199; block=3; confidence=0.95 -->
**Proof of Theorem 8.1.4. Step 1 (chaining set-up).** WLOG assume $K=1$ and $T$ finite. Set the dyadic scale

$$\varepsilon_k = 2^{-k},\quad k\in\mathbb{Z} \tag{8.4}$$

and choose $\varepsilon_k$-nets $T_k$ of $T$ with

$$|T_k| = \mathcal{N}(T,d,\varepsilon_k). \tag{8.5}$$

<a id="pdf-681b6f3d947f-p200-b001"></a>
<!-- pdf-source: page=200; block=1; confidence=0.94 -->
Since $T$ is finite, there exist $\kappa\in\mathbb{Z}$ (coarsest) and $K\in\mathbb{Z}$ (finest) with $T_\kappa=\{t_0\}$ and $T_K=T$. For $t\in T$ let $\pi_k(t)$ be a nearest point in $T_k$, so

$$d(t,\pi_k(t))\le\varepsilon_k. \tag{8.6}$$

Because $\mathbb{E}X_{t_0}=0$,

$$\mathbb{E}\sup_{t\in T} X_t = \mathbb{E}\sup_{t\in T}(X_t - X_{t_0}). \tag{8.7}$$

Write the increment as a telescoping sum (8.8); its first and last terms vanish by (8.6), giving

$$X_t - X_{t_0} = \sum_{k=\kappa+1}^{K}\big(X_{\pi_k(t)} - X_{\pi_{k-1}(t)}\big). \tag{8.9}$$

Since the supremum of a sum is at most the sum of suprema,

$$\mathbb{E}\sup_{t\in T}(X_t - X_{t_0}) \le \sum_{k=\kappa+1}^{K}\mathbb{E}\sup_{t\in T}\big(X_{\pi_k(t)} - X_{\pi_{k-1}(t)}\big). \tag{8.10}$$

<a id="pdf-681b6f3d947f-p200-b002"></a>
<!-- pdf-source: page=200; block=2; confidence=0.93 -->
**Step 2 (controlling the increments).** Each term in (8.10), though written as a sup over $T$, is a maximum over the possible pairs $(\pi_k(t),\pi_{k-1}(t))$, whose count is

$$|T_k|\cdot|T_{k-1}| \le |T_k|^2,$$

controlled via (8.5).

<a id="pdf-681b6f3d947f-p201-b001"></a>
<!-- pdf-source: page=201; block=1; confidence=0.90 -->
For fixed $t$, using (8.1) with $K=1$, the triangle inequality, and (8.7):

$$\lVert X_{\pi_k(t)} - X_{\pi_{k-1}(t)}\rVert_{\psi_2} \le d(\pi_k(t),\pi_{k-1}(t)) \le d(\pi_k(t),t)+d(t,\pi_{k-1}(t)) \le \varepsilon_k+\varepsilon_{k-1} \le 2\varepsilon_{k-1}.$$

By Exercise 2.5.10, the expected maximum of $N$ sub-gaussian variables is at most $CL\sqrt{\log N}$ where $L$ is the maximal $\psi_2$ norm. Hence each term of (8.10) satisfies

$$\mathbb{E}\sup_{t\in T}\big(X_{\pi_k(t)} - X_{\pi_{k-1}(t)}\big) \le C\,\varepsilon_{k-1}\sqrt{\log|T_k|}. \tag{8.11}$$

<a id="pdf-681b6f3d947f-p201-b002"></a>
<!-- pdf-source: page=201; block=2; confidence=0.94 -->
**Step 3 (summing up the increments).**

$$\mathbb{E}\sup_{t\in T}(X_t - X_{t_0}) \le C\sum_{k=\kappa+1}^{K}\varepsilon_{k-1}\sqrt{\log|T_k|}. \tag{8.12}$$

Substituting $\varepsilon_k=2^{-k}$ from (8.4) and the bounds (8.5) on $|T_k|$,

$$\mathbb{E}\sup_{t\in T}(X_t - X_{t_0}) \le C_1\sum_{k=\kappa+1}^{K} 2^{-k}\sqrt{\log \mathcal{N}(T,d,2^{-k})}.$$

This proves Theorem 8.1.4. $\blacksquare$

<a id="pdf-681b6f3d947f-p201-b003"></a>
<!-- pdf-source: page=201; block=3; confidence=0.92 -->
**Proof of Dudley's integral inequality, Theorem 8.1.3.** To turn the sum (8.2) into an integral, write $2^{-k} = 2\int_{2^{-k-1}}^{2^{-k}} d\varepsilon$, so

$$\sum_{k\in\mathbb{Z}} 2^{-k}\sqrt{\log \mathcal{N}(T,d,2^{-k})} = 2\sum_{k\in\mathbb{Z}}\int_{2^{-k-1}}^{2^{-k}}\sqrt{\log \mathcal{N}(T,d,2^{-k})}\,d\varepsilon.$$

On each interval $2^{-k}\ge\varepsilon$, hence $\log \mathcal{N}(T,d,2^{-k})\le\log \mathcal{N}(T,d,\varepsilon)$, so the sum is bounded by

$$2\sum_{k\in\mathbb{Z}}\int_{2^{-k-1}}^{2^{-k}}\sqrt{\log \mathcal{N}(T,d,\varepsilon)}\,d\varepsilon = 2\int_0^\infty\sqrt{\log \mathcal{N}(T,d,\varepsilon)}\,d\varepsilon. \qquad\blacksquare$$

<a id="pdf-681b6f3d947f-p201-b004"></a>
<!-- pdf-source: page=201; block=4; confidence=0.90 -->
**Remark 8.1.5 (Supremum of increments).** The chaining argument in fact bounds the absolute increment:

$$\mathbb{E}\sup_{t\in T}|X_t - X_{t_0}| \le CK\int_0^\infty\sqrt{\log \mathcal{N}(T,d,\varepsilon)}\,d\varepsilon.$$

<a id="pdf-681b6f3d947f-p202-b001"></a>
<!-- pdf-source: page=202; block=1; confidence=0.92 -->
Combining the bound for $X_t - X_{t_0}$ with a similar one for $X_s - X_{t_0}$ via the triangle inequality gives $\mathbb{E}\sup_{t,s\in T}|X_t-X_s| \le CK\int_0^\infty \sqrt{\log N(T,d,\varepsilon)}\,d\varepsilon$. The mean-zero assumption $\mathbb{E}X_t=0$ is not needed for these two bounds, but is required in Dudley's Theorem 8.1.3. Dudley's inequality bounds only the expectation; adapting the argument yields a tail bound.

<a id="pdf-681b6f3d947f-p202-b002"></a>
<!-- pdf-source: page=202; block=2; confidence=0.97 -->
**Theorem 8.1.6 (Dudley's integral inequality: tail bound).** Let $(X_t)_{t\in T}$ be a random process on a metric space $(T,d)$ with sub-gaussian increments as in (8.1). Then for every $u\ge 0$, the event
$$\sup_{t,s\in T}|X_t-X_s| \le CK\Big[\int_0^\infty \sqrt{\log N(T,d,\varepsilon)}\,d\varepsilon + u\cdot\operatorname{diam}(T)\Big]$$
holds with probability at least $1-2\exp(-u^2)$.

<a id="pdf-681b6f3d947f-p202-b003"></a>
<!-- pdf-source: page=202; block=3; confidence=0.93 -->
**Exercise 8.1.7.** Prove Theorem 8.1.6. First obtain a high-probability version of (8.11): $\sup_{t\in T}(X_{\pi_k(t)}-X_{\pi_{k-1}(t)}) \le C\varepsilon_{k-1}\big[\sqrt{\log|T_k|}+z\big]$ with probability at least $1-2\exp(-z^2)$. Apply it with $z=z_k$ to control all terms simultaneously; summing yields a bound on $\sup_{t\in T}|X_t-X_{t_0}|$ with probability at least $1-2\sum_k\exp(-z_k^2)$. Choose the $z_k$ for a good bound, e.g. $z_k = u + \sqrt{k-\kappa}$.

<a id="pdf-681b6f3d947f-p202-b004"></a>
<!-- pdf-source: page=202; block=4; confidence=0.95 -->
**Exercise 8.1.8 (Equivalence of Dudley's integral and sum).** In the proof of Theorem 8.1.3 the Dudley sum was bounded by the integral; show the reverse bound $\int_0^\infty \sqrt{\log N(T,d,\varepsilon)}\,d\varepsilon \le C\sum_{k\in\mathbb{Z}} 2^{-k}\sqrt{\log N(T,d,2^{-k})}$.

<a id="pdf-681b6f3d947f-p202-b005"></a>
<!-- pdf-source: page=202; block=5; confidence=0.98 -->
## 8.1.1 Remarks and Examples

<a id="pdf-681b6f3d947f-p202-b006"></a>
<!-- pdf-source: page=202; block=6; confidence=0.96 -->
**Remark 8.1.9 (Limits of Dudley's integral).** Although Dudley's integral is formally over $[0,\infty]$, the upper limit may be taken as $\operatorname{diam}(T)$:
$$\mathbb{E}\sup_{t\in T} X_t \le CK\int_0^{\operatorname{diam}(T)} \sqrt{\log N(T,d,\varepsilon)}\,d\varepsilon. \tag{8.13}$$
Reason: if $\varepsilon>\operatorname{diam}(T)$ a single point is an $\varepsilon$-net, so $\log N(T,d,\varepsilon)=0$.

<a id="pdf-681b6f3d947f-p203-b001"></a>
<!-- pdf-source: page=203; block=1; confidence=0.94 -->
Applying Dudley's inequality to the canonical Gaussian process (as with Sudakov's inequality in Section 7.4.1) immediately yields the following bound.

<a id="pdf-681b6f3d947f-p203-b002"></a>
<!-- pdf-source: page=203; block=2; confidence=0.97 -->
**Theorem 8.1.10 (Dudley's inequality for sets in $\mathbb{R}^n$).** For any set $T\subset\mathbb{R}^n$, $w(T) \le C\int_0^\infty \sqrt{\log N(T,\varepsilon)}\,d\varepsilon.$

<a id="pdf-681b6f3d947f-p203-b003"></a>
<!-- pdf-source: page=203; block=3; confidence=0.95 -->
**Example 8.1.11.** For the unit Euclidean ball $T=B_2^n$, (4.10) gives $N(B_2^n,\varepsilon)\le(3/\varepsilon)^n$ for $\varepsilon\in(0,1]$ and $N(B_2^n,\varepsilon)=1$ for $\varepsilon>1$. Dudley's inequality gives a convergent integral $w(B_2^n)\le C\int_0^1 \sqrt{n\log(3/\varepsilon)}\,d\varepsilon \le C_1\sqrt{n}$. This is optimal: by (7.16) the Gaussian width of $B_2^n$ is equivalent to $\sqrt{n}$ up to a constant.

<a id="pdf-681b6f3d947f-p203-b004"></a>
<!-- pdf-source: page=203; block=4; confidence=0.94 -->
**Exercise 8.1.12 (Dudley's inequality can be loose).** With canonical basis $e_1,\dots,e_n$ of $\mathbb{R}^n$, let $T:=\{\, e_k/\sqrt{1+\log k} : k=1,\dots,n\,\}$. (a) Show $w(T)\le C$ (hint: Exercise 2.5.10). (b) Show $\int_0^\infty \sqrt{\log N(T,d,\varepsilon)}\,d\varepsilon \to \infty$ as $n\to\infty$ (hint: the first $m$ vectors of $T$ form a $(1/\sqrt{\log m})$-separated set).

<a id="pdf-681b6f3d947f-p203-b005"></a>
<!-- pdf-source: page=203; block=5; confidence=0.93 -->
## 8.1.2 * Two-sided Sudakov's inequality

Optional subsection. The gap between Sudakov's and Dudley's inequalities (Exercise 8.1.12) is only logarithmic; the aim is to show Sudakov's inequality in $\mathbb{R}^n$ (Corollary 7.4.3) is optimal up to a $\log n$ factor.

<a id="pdf-681b6f3d947f-p204-b001"></a>
<!-- pdf-source: page=204; block=1; confidence=0.97 -->
**Theorem 8.1.13 (Two-sided Sudakov's inequality).** Let $T\subset\mathbb{R}^n$ and set $s(T):=\sup_{\varepsilon\ge 0}\varepsilon\sqrt{\log N(T,\varepsilon)}$. Then $c\cdot s(T) \le w(T) \le C\log(n)\cdot s(T).$

<a id="pdf-681b6f3d947f-p204-b002"></a>
<!-- pdf-source: page=204; block=2; confidence=0.90 -->
**Proof.** The lower bound is Sudakov's inequality (Corollary 7.4.3). For the upper bound, chaining converges exponentially, so $O(\log n)$ steps suffice. Start chaining at $\kappa$, the smallest integer with $2^{-\kappa}<\operatorname{diam}(T)$, and stop at $K$, the largest integer with $2^{-K}\ge \dfrac{w(T)}{4\sqrt{n}}$. Then the last term of (8.8) may be nonzero, so instead of (8.9) one bounds
$$w(T) \le \sum_{k=\kappa+1}^{K}\mathbb{E}\sup_{t\in T}(X_{\pi_k(t)}-X_{\pi_{k-1}(t)}) + \mathbb{E}\sup_{t\in T}(X_t-X_{\pi_K(t)}). \tag{8.14}$$
For the canonical process $X_t=\langle g,t\rangle$, since $\|t-\pi_K(t)\|_2\le 2^{-K}$, the last term is $\mathbb{E}\sup_{t\in T}\langle g, t-\pi_K(t)\rangle \le 2^{-K}\,\mathbb{E}\|g\|_2 \le 2^{-K}\sqrt{n} \le \tfrac{1}{2}w(T)$ (by the choice of $K$). Substituting into (8.14) and subtracting $\tfrac{1}{2}w(T)$ from both sides yields
$$w(T) \le 2\sum_{k=\kappa+1}^{K}\mathbb{E}\sup_{t\in T}(X_{\pi_k(t)}-X_{\pi_{k-1}(t)}), \tag{8.15}$$
removing the last term. [Bounding of the remaining terms continues beyond this page.]

<a id="pdf-681b6f3d947f-p205-b001"></a>
<!-- pdf-source: page=205; block=1; confidence=0.90 -->
**Proof (continued).** The number of terms in the sum is bounded by $K-\kappa \le \log_2\!\big(\mathrm{diam}(T)/(w(T)/(4\sqrt{n}))\big)$ (by the definitions of $K$ and $\kappa$), then $\le \log_2(4\sqrt{n}\cdot\sqrt{2\pi})$ (by property (f) of Proposition 7.5.2), hence $K-\kappa \le C\log n$. Thus the sum in (8.15) can be replaced by its maximum at the cost of a factor $C\log n$, completing the argument as in the proof of Theorem 8.1.4.

<a id="pdf-681b6f3d947f-p205-b002"></a>
<!-- pdf-source: page=205; block=2; confidence=0.96 -->
**Exercise 8.1.14 (Limits in Dudley's integral).** Prove the following sharpening of Dudley's inequality (Theorem 8.1.10): for any $T\subset\mathbb{R}^n$,
$$w(T) \le C\int_a^b \sqrt{\log N(T,\varepsilon)}\,d\varepsilon, \qquad a=\frac{c\,w(T)}{\sqrt{n}},\quad b=\mathrm{diam}(T).$$

<a id="pdf-681b6f3d947f-p205-b003"></a>
<!-- pdf-source: page=205; block=3; confidence=0.95 -->
**8.2 Application: empirical processes.** Applies Dudley's inequality to empirical processes — random processes indexed by functions.

<a id="pdf-681b6f3d947f-p205-b004"></a>
<!-- pdf-source: page=205; block=4; confidence=0.95 -->
**8.2.1 Monte-Carlo method.** Goal: evaluate $\int_\Omega f\,d\mu$ for $f:\Omega\to\mathbb{R}$ and a probability measure $\mu$ on $\Omega\subset\mathbb{R}^d$ (e.g. $\int_0^1 f(x)\,dx$). Take a random point $X$ with law $\mu$, so $P\{X\in A\}=\mu(A)$ for measurable $A\subset\Omega$ (e.g. $X\sim\mathrm{Unif}[0,1]$). Then $\int_\Omega f\,d\mu = \mathbb{E}\,f(X)$. For i.i.d. copies $X_1,X_2,\dots$ of $X$, the law of large numbers (Theorem 1.3.1) gives
$$\frac{1}{n}\sum_{i=1}^n f(X_i) \to \mathbb{E}\,f(X)\quad\text{almost surely.} \tag{8.16}$$

<a id="pdf-681b6f3d947f-p206-b001"></a>
<!-- pdf-source: page=206; block=1; confidence=0.96 -->
As $n\to\infty$, the integral is approximated by
$$\int_\Omega f\,d\mu \approx \frac{1}{n}\sum_{i=1}^n f(X_i), \tag{8.17}$$
with points $X_i$ drawn at random from $\Omega$; this is the Monte-Carlo method of numerical integration.

<a id="pdf-681b6f3d947f-p206-b002"></a>
<!-- pdf-source: page=206; block=2; confidence=0.95 -->
**Remark 8.2.1 (Error rate).** The average error in (8.17) is $O(1/\sqrt{n})$: by the convergence rate of the LLN (cf. (1.5)),
$$\mathbb{E}\left|\frac{1}{n}\sum_{i=1}^n f(X_i)-\mathbb{E}\,f(X)\right| \le \left[\mathrm{Var}\!\left(\frac{1}{n}\sum_{i=1}^n f(X_i)\right)\right]^{1/2} = O\!\left(\frac{1}{\sqrt{n}}\right). \tag{8.18}$$

<a id="pdf-681b6f3d947f-p206-b003"></a>
<!-- pdf-source: page=206; block=3; confidence=0.94 -->
**Remark 8.2.2.** One need not know $\mu$ to evaluate $\int_\Omega f\,d\mu$ — it suffices to be able to sample $X_i$ according to $\mu$; likewise $f$ need only be known at a few random points.

<a id="pdf-681b6f3d947f-p206-b004"></a>
<!-- pdf-source: page=206; block=4; confidence=0.94 -->
**8.2.2 A uniform law of large numbers.** A single sample $X_1,\dots,X_n$ cannot evaluate the integral of *every* $f$ (a function can oscillate badly between sample points, making (8.17) fail). Restricting to non-oscillating functions helps: the next theorem shows Monte-Carlo (8.17) works simultaneously over the class of Lipschitz functions
$$\mathcal{F} := \{\, f:[0,1]\to\mathbb{R},\ \|f\|_{\mathrm{Lip}}\le L \,\}, \tag{8.19}$$
for any fixed $L$.

<a id="pdf-681b6f3d947f-p207-b001"></a>
<!-- pdf-source: page=207; block=1; confidence=0.96 -->
**Theorem 8.2.3 (Uniform law of large numbers).** Let $X,X_1,X_2,\dots,X_n$ be i.i.d. random variables taking values in $[0,1]$. Then
$$\mathbb{E}\,\sup_{f\in\mathcal{F}}\left|\frac{1}{n}\sum_{i=1}^n f(X_i)-\mathbb{E}\,f(X)\right| \le \frac{CL}{\sqrt{n}}. \tag{8.20}$$

<a id="pdf-681b6f3d947f-p207-b002"></a>
<!-- pdf-source: page=207; block=2; confidence=0.93 -->
**Remark 8.2.4.** Key point: the supremum over $f\in\mathcal{F}$ sits *inside* the expectation. By Markov's inequality, a random sample $X_1,\dots,X_n$ is with high probability "good" — usable to approximate $\int f$ for every $f\in\mathcal{F}$ with error $\le CL/\sqrt{n}$, the same rate the classical LLN (8.18) gives for a single $f$. So making the LLN uniform over $\mathcal{F}$ costs essentially nothing.

<a id="pdf-681b6f3d947f-p207-b003"></a>
<!-- pdf-source: page=207; block=3; confidence=0.96 -->
**Definition 8.2.5.** Let $\mathcal{F}$ be a class of real-valued functions $f:\Omega\to\mathbb{R}$ on a probability space $(\Omega,\Sigma,\mu)$. Let $X$ be a random point in $\Omega$ with law $\mu$, and $X_1,X_2,\dots,X_n$ independent copies of $X$. The random process $(X_f)_{f\in\mathcal{F}}$ defined by
$$X_f := \frac{1}{n}\sum_{i=1}^n f(X_i)-\mathbb{E}\,f(X) \tag{8.21}$$
is called an **empirical process** indexed by $\mathcal{F}$.

<a id="pdf-681b6f3d947f-p207-b004"></a>
<!-- pdf-source: page=207; block=4; confidence=0.95 -->
**Proof of Theorem 8.2.3.** Without loss of generality it suffices to prove the theorem for the normalized class
$$\mathcal{F} := \{\, f:[0,1]\to[0,1],\ \|f\|_{\mathrm{Lip}}\le 1 \,\}. \tag{8.22}$$
The goal is then to bound the magnitude $\mathbb{E}\,\sup_{f\in\mathcal{F}}|X_f|$.

<a id="pdf-681b6f3d947f-p208-b001"></a>
<!-- pdf-source: page=208; block=1; confidence=0.95 -->
**Proof (Step 1: sub-gaussian increments).** For the empirical process $(X_f)_{f\in F}$ from (8.21), fix $f,g\in F$ and write $\|X_f-X_g\|_{\psi_2}=\big\|\tfrac1n\sum_{i=1}^n Z_i\big\|_{\psi_2}$ with $Z_i:=(f-g)(X_i)-\mathbb E(f-g)(X)$. The $Z_i$ are independent, mean zero, so by Proposition 2.6.1, $\|X_f-X_g\|_{\psi_2}\lesssim \tfrac1n\big(\sum_{i=1}^n\|Z_i\|_{\psi_2}^2\big)^{1/2}$. Centering (Lemma 2.6.8) gives $\|Z_i\|_{\psi_2}\lesssim\|(f-g)(X_i)\|_{\psi_2}\lesssim\|f-g\|_\infty$. Hence $\|X_f-X_g\|_{\psi_2}\lesssim \tfrac1n\cdot n^{1/2}\|f-g\|_\infty=\tfrac1{\sqrt n}\|f-g\|_\infty$.

<a id="pdf-681b6f3d947f-p208-b002"></a>
<!-- pdf-source: page=208; block=2; confidence=0.95 -->
**Proof (Step 2: applying Dudley's inequality).** The process has sub-gaussian increments in the $L^\infty$ norm; (8.22) implies $\operatorname{diam}(F)\le 1$ in $L^\infty$. Since $0\in F$, applying Dudley's inequality (Theorem 8.1.3, in the form of Remark 8.1.5; cf. (8.13)) gives $\mathbb E\sup_{f\in F}|X_f|=\mathbb E\sup_{f\in F}|X_f-X_0|\lesssim \tfrac1{\sqrt n}\int_0^1\sqrt{\log N(F,\|\cdot\|_\infty,\varepsilon)}\,d\varepsilon$. Using the covering-number bound $N(F,\|\cdot\|_\infty,\varepsilon)\le (C/\varepsilon)^{C/\varepsilon}$ (Exercise 8.2.6), the integral converges and $\mathbb E\sup_{f\in F}|X_f|\lesssim \tfrac1{\sqrt n}\int_0^1\sqrt{\tfrac{C}{\varepsilon}\log\tfrac{C}{\varepsilon}}\,d\varepsilon\lesssim \tfrac1{\sqrt n}$. Theorem 8.2.3 is proved. $\blacksquare$

<a id="pdf-681b6f3d947f-p208-b003"></a>
<!-- pdf-source: page=208; block=3; confidence=0.94 -->
**Exercise 8.2.6 (Metric entropy of the class of Lipschitz functions).** Consider $F:=\{f:[0,1]\to[0,1],\ \|f\|_{\mathrm{Lip}}\le 1\}$. (Bound on its covering numbers continues on the next page.)

<a id="pdf-681b6f3d947f-p209-b001"></a>
<!-- pdf-source: page=209; block=1; confidence=0.94 -->
**Exercise 8.2.6 (continued).** Show that $N(F,\|\cdot\|_\infty,\varepsilon)\le (2/\varepsilon)^{2/\varepsilon}$ for any $\varepsilon\in(0,1)$. *Hint:* put a mesh of step $\varepsilon$ on $[0,1]^2$; for $f\in F$ find a mesh-following $f_0$ with $\|f-f_0\|_\infty\le\varepsilon$ (Figure 8.5); the number of such $f_0$ is $\le (1/\varepsilon)^{1/\varepsilon}$; then apply Exercise 4.2.9.

<a id="pdf-681b6f3d947f-p209-b002"></a>
<!-- pdf-source: page=209; block=2; confidence=0.94 -->
**Exercise 8.2.7 (An improved bound on the metric entropy).** Improve Exercise 8.2.6 to $N(F,\|\cdot\|_\infty,\varepsilon)\le e^{C/\varepsilon}$ for any $\varepsilon>0$. *Hint:* use the Lipschitz property to bound the number of possible $f_0$ more tightly.

<a id="pdf-681b6f3d947f-p209-b003"></a>
<!-- pdf-source: page=209; block=3; confidence=0.94 -->
**Exercise 8.2.8 (Higher dimensions).** For the unit cube $[0,1]^d$ ($d\ge1$) with $\|\cdot\|_\infty$ metric and $F:=\{f:[0,1]^d\to\mathbb R,\ f(0)=0,\ \|f\|_{\mathrm{Lip}}\le1\}$, show $N(F,\|\cdot\|_\infty,\varepsilon)\le e^{C/\varepsilon^{d}}$ for any $\varepsilon>0$.

<a id="pdf-681b6f3d947f-p209-b004"></a>
<!-- pdf-source: page=209; block=4; confidence=0.92 -->
**Empirical measure (Section 8.2.3).** Let $\mu_n$ be the (random) probability measure uniform on the sample $X_1,\dots,X_n$: $\mu_n(\{X_i\})=\tfrac1n$ for each $i=1,\dots,n$ (8.23). It is called the empirical measure; $\int f\,d\mu=\mathbb E f(X)$ is the population average of $f$, while $\int f\,d\mu_n$ is the sample/empirical average.

<a id="pdf-681b6f3d947f-p210-b001"></a>
<!-- pdf-source: page=210; block=1; confidence=0.92 -->
Notation: $\mu f=\int f\,d\mu=\mathbb E f(X)$ and $\mu_n f=\int f\,d\mu_n=\tfrac1n\sum_{i=1}^n f(X_i)$. The empirical process (8.21) is $X_f=\mu f-\mu_n f$, the deviation of population from empirical expectation. The uniform law of large numbers (8.20) bounds $\mathbb E\sup_{f\in F}|\mu_n f-\mu f|$ (8.24) over the Lipschitz class $F$ of (8.19). Quantity (8.24) is the Wasserstein distance $W_1(\mu,\mu_n)$, equivalent (by Kantorovich–Rubinstein duality) to the transportation cost of $\mu$ into $\mu_n$ with cost proportional to mass moved and distance.

<a id="pdf-681b6f3d947f-p210-b002"></a>
<!-- pdf-source: page=210; block=2; confidence=0.90 -->
**8.3 VC dimension.** Introduces VC dimension (central in statistical learning theory), relating it to covering numbers and, via Dudley's inequality, to random processes and the uniform LLN; learning-theory applications follow in the next section.

<a id="pdf-681b6f3d947f-p210-b003"></a>
<!-- pdf-source: page=210; block=3; confidence=0.90 -->
**8.3.1 Definition and examples.** VC dimension measures the complexity of classes of Boolean functions, where a class $F$ is any collection of functions $f:\Omega\to\{0,1\}$ on a common domain $\Omega$.

<a id="pdf-681b6f3d947f-p210-b004"></a>
<!-- pdf-source: page=210; block=4; confidence=0.95 -->
**Definition 8.3.1 (VC dimension).** For a class $F$ of Boolean functions on $\Omega$, a subset $\Lambda\subseteq\Omega$ is *shattered* by $F$ if every $g:\Lambda\to\{0,1\}$ arises as the restriction of some $f\in F$ to $\Lambda$. The VC dimension $\mathrm{vc}(F)$ is the largest cardinality of a shattered subset $\Lambda\subseteq\Omega$; if no largest exists, $\mathrm{vc}(F)=\infty$.

<a id="pdf-681b6f3d947f-p211-b001"></a>
<!-- pdf-source: page=211; block=1; confidence=0.95 -->
**Example 8.3.2 (Intervals).** Let F be the class of indicators 1[a,b] of closed intervals in R (a ≤ b). The two-point set Λ = {3,5} is shattered: each of the four functions g: Λ→{0,1} is a restriction of some 1[a,b] (e.g. g(3)=1, g(5)=0 arises from f=1[2,4]). Hence vc(F) ≥ 2.

<a id="pdf-681b6f3d947f-p211-b002"></a>
<!-- pdf-source: page=211; block=2; confidence=0.95 -->
**Proof (vc(F) = 2).** No three-point set Λ = {p,q,r} with p < q < r is shattered: the labeling g(p)=1, g(q)=0, g(r)=1 cannot be the restriction of any 1[a,b], since [a,b] would have to contain p and r but exclude the intermediate q, which is impossible. Therefore vc(F) = 2.

<a id="pdf-681b6f3d947f-p211-b003"></a>
<!-- pdf-source: page=211; block=3; confidence=0.94 -->
**Example 8.3.3 (Half-planes).** Let F be the class of indicators of closed half-planes in R². A set Λ of three points in general position is shattered: for each of the 2³ = 8 labelings g: Λ→{0,1}, a half-plane can be arranged to contain exactly the points where g = 1. Hence vc(F) ≥ 3.

<a id="pdf-681b6f3d947f-p212-b001"></a>
<!-- pdf-source: page=212; block=1; confidence=0.93 -->
**Proof (vc(F) = 3).** No four-point set is shattered. For points in general position there are two arrangements, and in each there is a 0/1 labeling g that no half-plane realizes (no half-plane contains exactly the points labeled 1), so g is not a restriction of any f ∈ F. Hence vc(F) = 3. (The non-general-position case is left to the reader.)

<a id="pdf-681b6f3d947f-p212-b002"></a>
<!-- pdf-source: page=212; block=2; confidence=0.93 -->
**Example 8.3.4.** Let Ω = {1,2,3}, with Boolean functions written as length-3 binary strings, and F = {001, 010, 100, 111}. The set Λ = {1,3} is shattered: restricting F to Λ drops the middle digit, producing {00, 01, 10, 11} = all functions Λ→{0,1}, so vc(F) ≥ |Λ| = 2. The set {1,2,3} is not shattered (this would require all eight length-3 strings to lie in F). Hence vc(F) = 2.

<a id="pdf-681b6f3d947f-p212-b003"></a>
<!-- pdf-source: page=212; block=3; confidence=0.95 -->
**Exercise 8.3.5 (Pairs of intervals).** Let F be the class of indicators of sets of the form [a,b] ∪ [c,d] in R. Show that vc(F) = 4.

<a id="pdf-681b6f3d947f-p212-b004"></a>
<!-- pdf-source: page=212; block=4; confidence=0.95 -->
**Exercise 8.3.6 (Circles).** Let F be the class of indicators of all circles in R². Show that vc(F) = 3.

<a id="pdf-681b6f3d947f-p212-b005"></a>
<!-- pdf-source: page=212; block=5; confidence=0.90 -->
**Exercise 8.3.7 (Rectangles).** Let F be the class of indicators of all closed axis-aligned rectangles, i.e. product sets [a,b] × [c,d] in R². (Statement continues on the next page.)

<a id="pdf-681b6f3d947f-p213-b001"></a>
<!-- pdf-source: page=213; block=1; confidence=0.95 -->
**Exercise 8.3.7 (Rectangles, cont.).** For $\mathcal{F}$ the class of indicators of closed axis-aligned rectangles $[a,b] \times [c,d]$ in $\mathbb{R}^2$, show that $\mathrm{vc}(\mathcal{F}) = 4$.

<a id="pdf-681b6f3d947f-p213-b002"></a>
<!-- pdf-source: page=213; block=2; confidence=0.95 -->
**Exercise 8.3.8 (Squares).** Let $\mathcal{F}$ be the class of indicators of all closed axis-aligned squares, i.e. product sets $[a, a+d] \times [b, b+d]$ in $\mathbb{R}^2$. Show that $\mathrm{vc}(\mathcal{F}) = 3$.

<a id="pdf-681b6f3d947f-p213-b003"></a>
<!-- pdf-source: page=213; block=3; confidence=0.95 -->
**Exercise 8.3.9 (Polygons).** Let $\mathcal{F}$ be the class of indicators of all convex polygons in $\mathbb{R}^2$, with no restriction on the number of vertices. Show that $\mathrm{vc}(\mathcal{F}) = \infty$.

<a id="pdf-681b6f3d947f-p213-b004"></a>
<!-- pdf-source: page=213; block=4; confidence=0.92 -->
**Remark 8.3.10 (VC dimension of classes of sets).** VC dimension applies to classes of sets via the correspondence between a Boolean function f on Ω and the subset {x ∈ Ω : f(x) = 1} (and conversely Ω₀ ⊂ Ω ↔ f = 1_{Ω₀}). Thus the set of intervals in R has VC dimension 2, the set of half-planes in R² has VC dimension 3, and so on.

<a id="pdf-681b6f3d947f-p213-b005"></a>
<!-- pdf-source: page=213; block=5; confidence=0.95 -->
**Exercise 8.3.11.** Give a definition of the VC dimension of a class of subsets of Ω without mentioning any functions.

<a id="pdf-681b6f3d947f-p213-b006"></a>
<!-- pdf-source: page=213; block=6; confidence=0.90 -->
**Remark 8.3.12 (More examples).** Stated VC dimensions: all (not necessarily axis-aligned) rectangles in the plane = 7; polygons with k vertices in the plane = 2k + 1; half-spaces in Rⁿ = n + 1.

<a id="pdf-681b6f3d947f-p213-b007"></a>
<!-- pdf-source: page=213; block=7; confidence=0.90 -->
**8.3.2 Pajor's Lemma.** For a class F of Boolean functions on a finite set Ω, |F| is roughly exponential in vc(F). The trivial lower bound is |F| ≥ 2^{vc(F)}; the upper bounds (below) are less trivial.

<a id="pdf-681b6f3d947f-p213-b008"></a>
<!-- pdf-source: page=213; block=8; confidence=0.95 -->
**Lemma 8.3.13 (Pajor's Lemma).** Let F be a class of Boolean functions on a finite set Ω. Then |F| ≤ |{Λ ⊆ Ω : Λ is shattered by F}|, where the empty set Λ = ∅ is counted as shattered on the right-hand side.

<a id="pdf-681b6f3d947f-p213-b009"></a>
<!-- pdf-source: page=213; block=9; confidence=0.92 -->
**Illustration (via Example 8.3.4).** There |F| = 4 and the subsets shattered by F are {1}, {2}, {3}, {1,2}, {1,3}, {2,3} (six of them), so Pajor's inequality reads 4 ≤ 6.

<a id="pdf-681b6f3d947f-p214-b001"></a>
<!-- pdf-source: page=214; block=1; confidence=0.95 -->
**Proof of Pajor's Lemma 8.3.13.** By induction on |Ω|; base case |Ω|=1 is trivial (empty set is counted). Inductive step: for |Ω|=n+1 write Ω = Ω₀ ∪ {x₀} with |Ω₀|=n. Split F into F₀ := {f ∈ F : f(x₀)=0} and F₁ := {f ∈ F : f(x₀)=1}. With S(F) = |{Λ ⊆ Ω : Λ shattered by F}|, the induction hypothesis (applied after restricting F₀, F₁ to Ω₀) gives S(F₀) ≥ |F₀| and S(F₁) ≥ |F₁| (8.25). It remains to show S(F) ≥ S(F₀) + S(F₁) (8.26), since then S(F) ≥ |F₀|+|F₁| = |F|. Each Λ counted by S(F₀) or S(F₁) is shattered by the larger class F. For a Λ shattered by both F₀ and F₁ (counted once in S(F)), the set Λ ∪ {x₀} is also shattered by F and not previously counted, avoiding double-counting; this yields (8.26).

<a id="pdf-681b6f3d947f-p214-b002"></a>
<!-- pdf-source: page=214; block=2; confidence=0.90 -->
**Example 8.3.14.** Illustrates the Pajor induction step on Ω = {1,2,3}, F = {001, 010, 100, 111}. Chopping x₀ = 3 gives Ω₀ = {1,2} and the split F₀ = {010, 100}, F₁ = {001, 111}. Both F₀ and F₁ shatter exactly {1} and {2}, so S(F₀) = S(F₁) = 2. F shatters these same two subsets; two additional shattered subsets are obtained by appending x₀ = 3, giving {1,3} and (continued next page).

<a id="pdf-681b6f3d947f-p215-b001"></a>
<!-- pdf-source: page=215; block=1; confidence=0.90 -->
**Example 8.3.14 (concluded).** The appended sets {1,3} and {2,3} are also shattered by F and were not yet counted, giving at least four subsets shattered by F, so S(F) ≥ 4, confirming key inequality (8.26).

<a id="pdf-681b6f3d947f-p215-b002"></a>
<!-- pdf-source: page=215; block=2; confidence=0.95 -->
**Exercise 8.3.15 (Sharpness of Pajor's Lemma).** Show Pajor's Lemma 8.3.13 is sharp. Hint: take F = binary strings of length n with at most d ones (the Hamming cube).

<a id="pdf-681b6f3d947f-p215-b003"></a>
<!-- pdf-source: page=215; block=3; confidence=0.95 -->
## 8.3.3 Sauer-Shelah Lemma

An upper bound on the cardinality of a function class in terms of its VC dimension.

<a id="pdf-681b6f3d947f-p215-b004"></a>
<!-- pdf-source: page=215; block=4; confidence=0.97 -->
**Theorem 8.3.16 (Sauer-Shelah Lemma).** Let F be a class of Boolean functions on an n-point set Ω, and d = vc(F). Then |F| ≤ Σ_{k=0}^{d} C(n,k) ≤ (en/d)^d.

<a id="pdf-681b6f3d947f-p215-b005"></a>
<!-- pdf-source: page=215; block=5; confidence=0.95 -->
**Proof.** By Pajor's Lemma, |F| is bounded by the number of subsets Λ ⊆ Ω shattered by F; each such Λ has |Λ| ≤ d = vc(F). Hence |F| ≤ |{Λ ⊆ Ω : |Λ| ≤ d}| = Σ_{k=0}^{d} C(n,k), the number of subsets of an n-element set of size at most d, giving the first inequality. The second inequality follows from the binomial-sum bound of Exercise 0.0.5.

<a id="pdf-681b6f3d947f-p215-b006"></a>
<!-- pdf-source: page=215; block=6; confidence=0.95 -->
**Exercise 8.3.17 (Sharpness of Sauer-Shelah Lemma).** Show the Sauer-Shelah lemma is sharp for all n and d. Hint: use the Hamming cube from Exercise 8.3.15.

<a id="pdf-681b6f3d947f-p215-b007"></a>
<!-- pdf-source: page=215; block=7; confidence=0.90 -->
## 8.3.4 Covering numbers via VC dimension

Sauer-Shelah applies only to finite F; for infinite classes (e.g. indicators of half-planes, Example 8.3.3) one can still bound covering numbers via VC dimension. Setup: F a class of Boolean functions on Ω, µ a probability measure on Ω, so F becomes a metric space under the L²(µ) norm.

<a id="pdf-681b6f3d947f-p216-b001"></a>
<!-- pdf-source: page=216; block=1; confidence=0.90 -->
**Definition.** The L²(µ) metric on F is d(f,g) = ‖f − g‖_{L²(µ)} = (∫_Ω |f − g|² dµ)^{1/2}, f,g ∈ F. Covering numbers of F in this norm are denoted N(F, L²(µ), ε). (Discrete case: for Ω = {1,…,N} with uniform µ(i)=1/N, ‖f‖_{L²(µ)} = (1/N Σ_{i=1}^N f(i)²)^{1/2} = (1/√N)‖f‖₂, the scaled Euclidean norm.)

<a id="pdf-681b6f3d947f-p216-b002"></a>
<!-- pdf-source: page=216; block=2; confidence=0.96 -->
**Theorem 8.3.18 (Covering numbers via VC dimension).** Let F be a class of Boolean functions on a probability space (Ω, Σ, µ) with d = vc(F). Then for every ε ∈ (0,1), N(F, L²(µ), ε) ≤ (2/ε)^{Cd}.

<a id="pdf-681b6f3d947f-p216-b003"></a>
<!-- pdf-source: page=216; block=3; confidence=0.90 -->
Remark: compares to the volumetric bound (4.10) — both scale exponentially in dimension, but VC dimension captures combinatorial rather than linear-algebraic complexity. First attempt: if Ω is finite with |Ω| = n, Sauer-Shelah gives N(F, L²(µ), ε) ≤ |F| ≤ (en/d)^d, which is close but depends on n. The goal is to remove the dependence on n by reducing Ω to a smaller subset without harming covering numbers, achieved via the next lemma.

<a id="pdf-681b6f3d947f-p216-b004"></a>
<!-- pdf-source: page=216; block=4; confidence=0.95 -->
**Lemma 8.3.19 (Dimension reduction).** Let F be a class of N Boolean functions on a probability space (Ω, Σ, µ), and assume all functions are ε-separated: ‖f − g‖_{L²(µ)} > ε for all distinct f,g ∈ F. Then there exist a number n ≤ Cε^{-4} log N and an n-point set Ω_n ⊂ Ω such that the restrictions of the functions f ∈ F to Ω_n are all distinct.

<a id="pdf-681b6f3d947f-p216-b005"></a>
<!-- pdf-source: page=216; block=5; confidence=0.90 -->
**Proof.** By the probabilistic method: choose the subset Ω_n at random and show it satisfies the conclusion with positive probability, which implies existence of at least one suitable Ω_n. (Continues beyond supplied pages.)

<a id="pdf-681b6f3d947f-p217-b001"></a>
<!-- pdf-source: page=217; block=1; confidence=0.95 -->
**Proof (continued).** For i.i.d. points $X_1,\dots,X_n\sim\mu$, let $\mu_n$ be the empirical measure assigning each $X_i$ mass $1/n$ (with multiplicity). Goal: with positive probability, $\|f-g\|_{L^2(\mu_n)}^2=\frac1n\sum_{i=1}^n(f-g)(X_i)^2>0$ for all distinct $f,g\in\mathcal F$, which forces the restrictions to $\Omega_n=\{X_1,\dots,X_n\}$ to be distinct.

<a id="pdf-681b6f3d947f-p217-b002"></a>
<!-- pdf-source: page=217; block=2; confidence=0.95 -->
Fix distinct $f,g$ and set $h=(f-g)^2$. Bound the deviation $\|f-g\|_{L^2(\mu_n)}^2-\|f-g\|_{L^2(\mu)}^2=\frac1n\sum_i h(X_i)-\mathbb E h(X)$ by general Hoeffding (Thm 2.6.2). The summands are subgaussian: $\|h(X_i)-\mathbb E h(X)\|_{\psi_2}\lesssim\|h(X)\|_{\psi_2}\lesssim\|h(X)\|_\infty\le1$ (Centering Lemma 2.6.8, eq. (2.17), and $f,g$ Boolean). Hoeffding gives $\mathbb P\{|\,\|f-g\|_{L^2(\mu_n)}^2-\|f-g\|_{L^2(\mu)}^2\,|>\varepsilon^2/4\}\le2\exp(-cn\varepsilon^4)$.

<a id="pdf-681b6f3d947f-p217-b003"></a>
<!-- pdf-source: page=217; block=3; confidence=0.90 -->
Hence with probability $\ge1-2\exp(-cn\varepsilon^4)$, $\|f-g\|_{L^2(\mu_n)}^2\ge\|f-g\|_{L^2(\mu)}^2-\varepsilon^2/4\ge\varepsilon^2-\varepsilon^2/4=3\varepsilon^2/4$, eq. (8.27), using the lemma's separation hypothesis and the triangle inequality. A union bound over the $\le N^2$ distinct pairs makes (8.27) hold simultaneously with probability $\ge1-N^2\cdot2\exp(-cn\varepsilon^4)$, eq. (8.28). Choosing $n=\lceil C'\varepsilon^{-4}\log N\rceil$ makes (8.28) positive, so $\Omega_n$ satisfies the lemma with positive probability.

<a id="pdf-681b6f3d947f-p218-b001"></a>
<!-- pdf-source: page=218; block=1; confidence=0.94 -->
**Proof of Theorem 8.3.18.** Choose $N\ge\mathcal N(\mathcal F,L^2(\mu),\varepsilon)$ $\varepsilon$-separated functions in $\mathcal F$ (they exist by the covering–packing relation, Lemma 4.2.8). Lemma 8.3.19 produces $\Omega_n\subset\Omega$ with $|\Omega_n|=n\le C\varepsilon^{-4}\log N$ whose restrictions are $\varepsilon/2$-separated in $L^2(\mu_n)$ — in particular distinct, giving a class $\mathcal F_n$ of distinct Boolean functions on $\Omega_n$. Sauer–Shelah (Thm 8.3.16) yields $N\le(en/d_n)^{d_n}\le(C\varepsilon^{-4}\log N/d_n)^{d_n}$ with $d_n=\mathrm{vc}(\mathcal F_n)$; simplifying (via $\tfrac{\log N}{2d_n}=\log(N^{1/2d_n})\le N^{1/2d_n}$) gives $N\le(C\varepsilon^{-4})^{2d_n}$. Replace $d_n$ by the larger $d=\mathrm{vc}(\mathcal F)$.

<a id="pdf-681b6f3d947f-p218-b002"></a>
<!-- pdf-source: page=218; block=2; confidence=0.96 -->
**Remark 8.3.20 (Johnson–Lindenstrauss Lemma for coordinate projections).** Notes the parallel between Dimension Reduction Lemma 8.3.19 and the JL Lemma (Thm 5.3.1): both preserve the geometry of $N$ points under projection to dimension $\sim\log N$; JL uses a uniformly random Grassmannian subspace, whereas 8.3.19 uses a coordinate subspace.

<a id="pdf-681b6f3d947f-p218-b003"></a>
<!-- pdf-source: page=218; block=3; confidence=0.95 -->
**Exercise 8.3.21 (Dimension reduction for covering numbers).** For a class $\mathcal F$ bounded by 1 in absolute value on a probability space $(\Omega,\Sigma,\mu)$ and $\varepsilon\in(0,1)$: show there exist $n\le C\varepsilon^{-4}\log\mathcal N(\mathcal F,L^2(\mu),\varepsilon)$ and an $n$-point $\Omega_n\subset\Omega$ with $\mathcal N(\mathcal F,L^2(\mu),\varepsilon)\le\mathcal N(\mathcal F,L^2(\mu_n),\varepsilon/4)$, $\mu_n$ the uniform measure on $\Omega_n$. Hint: as in Lemma 8.3.19 then covering–packing (Lemma 4.2.8).

<a id="pdf-681b6f3d947f-p218-b004"></a>
<!-- pdf-source: page=218; block=4; confidence=0.97 -->
**Exercise 8.3.22.** Theorem 8.3.18 is stated for $\varepsilon\in(0,1)$; determine the bound for larger $\varepsilon$.

<a id="pdf-681b6f3d947f-p219-b001"></a>
<!-- pdf-source: page=219; block=1; confidence=0.95 -->
### 8.3.5 Empirical processes via VC dimension
Develops a general bound for empirical processes over an arbitrary class of Boolean functions, extending the Lipschitz-class example of §8.2.2.

<a id="pdf-681b6f3d947f-p219-b002"></a>
<!-- pdf-source: page=219; block=2; confidence=0.96 -->
**Theorem 8.3.23 (Empirical processes via VC dimension).** For a class $\mathcal F$ of Boolean functions on $(\Omega,\Sigma,\mu)$ with $\mathrm{vc}(\mathcal F)\ge1$ and i.i.d. $X,X_1,\dots,X_n\sim\mu$:
$$\mathbb E\sup_{f\in\mathcal F}\Big|\frac1n\sum_{i=1}^n f(X_i)-\mathbb E f(X)\Big|\le C\sqrt{\tfrac{\mathrm{vc}(\mathcal F)}{n}},\quad(8.29)$$
following from Dudley's inequality plus the §8.3.4 covering-number bound, after symmetrization.

<a id="pdf-681b6f3d947f-p219-b003"></a>
<!-- pdf-source: page=219; block=3; confidence=0.96 -->
**Exercise 8.3.24 (Symmetrization for empirical processes).** For a class $\mathcal F$ on $(\Omega,\Sigma,\mu)$ and random points $X,X_1,\dots,X_n\sim\mu$, prove $\mathbb E\sup_f|\frac1n\sum_i (f(X_i)-\mathbb E f(X))|\le2\,\mathbb E\sup_f|\frac1n\sum_i\varepsilon_i f(X_i)|$, where $\varepsilon_i$ are independent symmetric Bernoulli variables independent of the $X_i$. Hint: modify Symmetrization Lemma 6.4.2.

<a id="pdf-681b6f3d947f-p219-b004"></a>
<!-- pdf-source: page=219; block=4; confidence=0.93 -->
**Proof of Theorem 8.3.23.** By symmetrization the LHS of (8.29) is $\le\frac{2}{\sqrt n}\mathbb E\sup_f|Z_f|$ with $Z_f:=\frac1{\sqrt n}\sum_{i=1}^n\varepsilon_i f(X_i)$. Condition on $(X_i)$ (randomness only in the signs $\varepsilon_i$) and apply Dudley's inequality to $(Z_f)_{f\in\mathcal F}$, dropping the absolute value for now (handled in Ex. 8.3.25). The increments are subgaussian: $\|Z_f-Z_g\|_{\psi_2}=\frac1{\sqrt n}\|\sum_i\varepsilon_i(f-g)(X_i)\|_{\psi_2}\lesssim[\frac1n\sum_i(f-g)(X_i)^2]^{1/2}$, using Proposition 2.6.1 and $\|\varepsilon_i\|_{\psi_2}\lesssim1$ (the $X_i$ being fixed under conditioning). [Continues beyond supplied pages.]

<a id="pdf-681b6f3d947f-p220-b001"></a>
<!-- pdf-source: page=220; block=1; confidence=0.90 -->
**Proof (continued).** The increments satisfy $\lVert Z_f - Z_g\rVert_{\psi_2} \lesssim \lVert f-g\rVert_{L^2(\mu_n)}$, where $\mu_n$ is the uniform (empirical) probability measure on $\{X_1,\dots,X_n\}$. Applying Dudley's inequality (Theorem 8.1.3) conditionally on $(X_i)$ gives
$$\tfrac{2}{\sqrt n}\,\mathbb{E}\sup_{f\in\mathcal F} Z_f \lesssim \tfrac{1}{\sqrt n}\,\mathbb{E}\int_0^1 \sqrt{\log N(\mathcal F, L^2(\mu_n),\varepsilon)}\,d\varepsilon, \tag{8.30}$$
the expectation being over $(X_i)$. Bounding covering numbers via Theorem 8.3.18, $\log N(\mathcal F, L^2(\mu_n),\varepsilon) \lesssim \mathrm{vc}(\mathcal F)\log(2/\varepsilon)$. Substituting into (8.30), the integral of $\sqrt{\log(2/\varepsilon)}$ is bounded by an absolute constant, yielding $\tfrac{2}{\sqrt n}\,\mathbb{E}\sup_{f\in\mathcal F} Z_f \lesssim \sqrt{\mathrm{vc}(\mathcal F)/n}$, as required.

<a id="pdf-681b6f3d947f-p220-b002"></a>
<!-- pdf-source: page=220; block=2; confidence=0.95 -->
**Exercise 8.3.25 (Reinstating absolute value).** The proof bounded $\mathbb{E}\sup_{f\in\mathcal F} Z_f$; give a bound for $\mathbb{E}\sup_{f\in\mathcal F} |Z_f|$. Hint: add the zero function to $\mathcal F$ and use Remark 8.1.5 to write $|Z_f| = |Z_f - Z_0|$; adding one function does not significantly increase the VC dimension.

<a id="pdf-681b6f3d947f-p220-b003"></a>
<!-- pdf-source: page=220; block=3; confidence=0.95 -->
**Setup (Glivenko–Cantelli).** For a random variable $X$ with unknown CDF $F(x) = \mathbb{P}\{X \le x\}$, $x\in\mathbb R$, and an i.i.d. sample $X_1,\dots,X_n$ from the same law, the **empirical distribution function** is
$$F_n(x) := \frac{|\{i\in[n] : X_i \le x\}|}{n}, \qquad x\in\mathbb R,$$
a random function estimating $F$.

<a id="pdf-681b6f3d947f-p221-b001"></a>
<!-- pdf-source: page=221; block=1; confidence=0.93 -->
The quantitative law of large numbers gives, for every $x\in\mathbb R$, $\mathbb{E}|F_n(x)-F(x)| \le C/\sqrt n$ (via the variance computation of Section 1.3 applied to indicators $\mathbf 1\{X_i\le x\}$). Glivenko–Cantelli strengthens this to uniform approximation over $x$.

<a id="pdf-681b6f3d947f-p221-b002"></a>
<!-- pdf-source: page=221; block=2; confidence=0.97 -->
**Theorem 8.3.26 (Glivenko–Cantelli Theorem).** Let $X_1,\dots,X_n$ be independent random variables with common CDF $F$. Then
$$\mathbb{E}\lVert F_n - F\rVert_\infty = \mathbb{E}\sup_{x\in\mathbb R} |F_n(x)-F(x)| \le \frac{C}{\sqrt n}.$$

<a id="pdf-681b6f3d947f-p221-b003"></a>
<!-- pdf-source: page=221; block=3; confidence=0.96 -->
**Proof.** A special case of Theorem 8.3.23. Take $\Omega=\mathbb R$, let $\mathcal F = \{\mathbf 1_{(-\infty,x]} : x\in\mathbb R\}$ be the indicators of half-bounded intervals, and let $\mu$ be the distribution of $X_i$ (i.e. $\mu(A)=\mathbb P\{X\in A\}$). By Example 8.3.2, $\mathrm{vc}(\mathcal F)\le 2$, so Theorem 8.3.23 gives the conclusion. $\square$

<a id="pdf-681b6f3d947f-p221-b004"></a>
<!-- pdf-source: page=221; block=4; confidence=0.94 -->
**Example 8.3.27 (Discrepancy).** Glivenko–Cantelli generalizes to random vectors. For i.i.d. points $X_1,\dots,X_n$ uniform on $[0,1]^2$ and $\mathcal F$ the indicators of all circles in the square, Exercise 8.3.6 gives $\mathrm{vc}(\mathcal F)=3$. Since $\sum_{i=1}^n f(X_i)$ counts points in the circle with indicator $f$ and $\mathbb E f(X)$ is its area, Theorem 8.3.23 yields: with high probability, for every circle $C\subset[0,1]^2$,
$$\#\{\text{points in } C\} = \mathrm{Area}(C)\cdot n + O(\sqrt n).$$
A geometric discrepancy result; it holds for half-planes, rectangles, squares, triangles, polygons with $O(1)$ vertices, and any class of bounded VC dimension.

<a id="pdf-681b6f3d947f-p222-b001"></a>
<!-- pdf-source: page=222; block=1; confidence=0.90 -->
Figure 8.8: by the uniform deviation inequality (Theorem 8.3.23), every circle contains a share of the random sample proportional to its area, with $O(\sqrt n)$ error.

<a id="pdf-681b6f3d947f-p222-b002"></a>
<!-- pdf-source: page=222; block=2; confidence=0.92 -->
**Remark 8.3.28 (Uniform Glivenko–Cantelli classes).** A class $\mathcal F$ of real-valued functions on $\Omega$ is **uniform Glivenko–Cantelli** if for every $\varepsilon>0$,
$$\lim_{n\to\infty}\ \sup_{\mu}\ \mathbb{P}\Big\{ \sup_{f\in\mathcal F}\Big| \tfrac1n\sum_{i=1}^n f(X_i) - \mathbb E f(X)\Big| > \varepsilon \Big\} = 0,$$
sup over all probability measures $\mu$ on $\Omega$, with $X,X_1,\dots,X_n \sim \mu$. Theorem 8.3.23 plus Markov's inequality shows every class of Boolean functions with finite VC dimension is uniform Glivenko–Cantelli.

<a id="pdf-681b6f3d947f-p222-b003"></a>
<!-- pdf-source: page=222; block=3; confidence=0.94 -->
**Exercise 8.3.29 (Sharpness).** Prove that any class of Boolean functions with infinite VC dimension is not uniform Glivenko–Cantelli. Hint: pick a shattered subset $\Lambda\subset\Omega$ of arbitrarily large cardinality $d$ and let $\mu$ be uniform on $\Lambda$ (mass $1/d$ each).

<a id="pdf-681b6f3d947f-p222-b004"></a>
<!-- pdf-source: page=222; block=4; confidence=0.94 -->
**Exercise 8.3.30 (A simpler, weaker bound).** Using the Sauer–Shelah Lemma directly (instead of Pajor's Lemma), prove a weaker version of the uniform deviation inequality (8.29) with right-hand side $C\sqrt{\tfrac{d}{n}\log\tfrac{en}{d}}$, where $d=\mathrm{vc}(\mathcal F)$. Hint: as in the proof of Theorem 8.3.23, combine a concentration inequality with a union bound over $\mathcal F$, controlling $|\mathcal F|$ via Sauer–Shelah.

<a id="pdf-681b6f3d947f-p223-b001"></a>
<!-- pdf-source: page=223; block=1; confidence=1.00 -->
## 8.4 Application: statistical learning theory

<a id="pdf-681b6f3d947f-p223-b002"></a>
<!-- pdf-source: page=223; block=2; confidence=0.98 -->
Setup: an unknown **target function** $T:\Omega\to\mathbb{R}$ is to be learned from its values on a finite sample $X_1,\dots,X_n\in\Omega$, sampled i.i.d. from a common distribution $P$ on $\Omega$. The **training data** is
$$(X_i, T(X_i)),\quad i=1,\dots,n.\tag{8.31}$$
Goal: predict $T(X)$ for a new random point $X\in\Omega$ drawn from the same distribution but not in the training sample.

<a id="pdf-681b6f3d947f-p223-b003"></a>
<!-- pdf-source: page=223; block=3; confidence=0.95 -->
Figure 8.9: learning an unknown target $T:\Omega\to\mathbb{R}$ from its values on an i.i.d. training sample $X_1,\dots,X_n$; goal is to predict $T(X)$ at a new random $X$.

<a id="pdf-681b6f3d947f-p223-b004"></a>
<!-- pdf-source: page=223; block=4; confidence=0.95 -->
Remark: learning resembles Monte-Carlo integration (Section 8.2.1) in inferring properties of a function from a random sample, but is harder — the whole function is learned, not just its integral/average.

<a id="pdf-681b6f3d947f-p223-b005"></a>
<!-- pdf-source: page=223; block=5; confidence=1.00 -->
### 8.4.1 Classification problems

<a id="pdf-681b6f3d947f-p223-b006"></a>
<!-- pdf-source: page=223; block=6; confidence=0.97 -->
**Classification problems**: the target $T$ is Boolean (values in $\{0,1\}$), so $T$ partitions $\Omega$ into two classes.

<a id="pdf-681b6f3d947f-p223-b007"></a>
<!-- pdf-source: page=223; block=7; confidence=0.95 -->
**Example 8.4.1.** Health study of $n$ patients: each patient's $d$ health parameters form a vector $X_i\in\mathbb{R}^d$, with binary label $T(X_i)\in\{0,1\}$ recording diabetes status. Aim: learn the target $T:\mathbb{R}^d\to\{0,1\}$ (continues on next page).

<a id="pdf-681b6f3d947f-p224-b001"></a>
<!-- pdf-source: page=224; block=1; confidence=0.93 -->
**Example 8.4.1 (cont.)** Encoding: $0=$ healthy, $1=$ sick; goal is to diagnose diabetes from the $d$ parameters. Variant: $X_i$ holds the $d$ gene expressions of patient $i$, to diagnose a disease from genetic information.

<a id="pdf-681b6f3d947f-p224-b002"></a>
<!-- pdf-source: page=224; block=2; confidence=0.94 -->
Figure 8.10 illustrates a planar classification: $X$ a random vector in the plane, label $Y\in\{0,1\}$; a solution partitions the plane into regions $f(X)=0$ (healthy) and $f(X)=1$ (sick). Panels show the fit–complexity trade-off: (a) underfitting, (b) overfitting, (c) right fit.

<a id="pdf-681b6f3d947f-p224-b003"></a>
<!-- pdf-source: page=224; block=3; confidence=1.00 -->
### 8.4.2 Risk, fit and complexity

<a id="pdf-681b6f3d947f-p224-b004"></a>
<!-- pdf-source: page=224; block=4; confidence=0.97 -->
A solution is a function $f:\Omega\to\mathbb{R}$; choose $f$ close to $T$ by minimizing the **risk**
$$R(f):=\mathbb{E}\big(f(X)-T(X)\big)^2,\tag{8.32}$$
where $X\sim P$, the same distribution as the sample points.

<a id="pdf-681b6f3d947f-p224-b005"></a>
<!-- pdf-source: page=224; block=5; confidence=0.96 -->
**Example 8.4.2.** For Boolean $T,f$ (classification),
$$R(f)=\mathbb{P}\{f(X)\neq T(X)\},\tag{8.33}$$
i.e. the misclassification probability.

<a id="pdf-681b6f3d947f-p224-b006"></a>
<!-- pdf-source: page=224; block=6; confidence=0.92 -->
The required sample size $n$ depends on problem complexity: more data is needed when $T(X)$ depends on $X$ in an intricate way (continues).

<a id="pdf-681b6f3d947f-p225-b001"></a>
<!-- pdf-source: page=225; block=1; confidence=0.93 -->
Since complexity is usually unknown a priori, restrict candidate $f$ to a class $\mathcal{F}$, the **hypothesis space**. Choice of $\mathcal{F}$ balances fit vs. complexity: too small (e.g. forcing a linear interface, Fig. 8.10a) underfits and yields large $R(f)$; too large risks overfitting (fitting noise, Fig. 8.10b) and needs much data. A good $\mathcal{F}$ (Fig. 8.10c) captures the essential trends.

<a id="pdf-681b6f3d947f-p225-b002"></a>
<!-- pdf-source: page=225; block=2; confidence=1.00 -->
### 8.4.3 Empirical risk

<a id="pdf-681b6f3d947f-p225-b003"></a>
<!-- pdf-source: page=225; block=3; confidence=0.95 -->
Ideal solution minimizing risk $R(f)=\mathbb{E}(f(X)-T(X))^2$ over the hypothesis space:
$$f^*:=\arg\min_{f\in\mathcal{F}} R(f).$$
If $\mathcal{F}$ contains $T$, then risk is zero. But $R(f)$ and $f^*$ cannot be computed from training data — only estimated.

<a id="pdf-681b6f3d947f-p225-b004"></a>
<!-- pdf-source: page=225; block=4; confidence=0.97 -->
**Definition 8.4.3.** The **empirical risk** of $f:\Omega\to\mathbb{R}$ is
$$R_n(f):=\frac{1}{n}\sum_{i=1}^{n}\big(f(X_i)-T(X_i)\big)^2.\tag{8.34}$$
Let $f_n^*:=\arg\min_{f\in\mathcal{F}} R_n(f)$ be the empirical risk minimizer.

<a id="pdf-681b6f3d947f-p225-b005"></a>
<!-- pdf-source: page=225; block=5; confidence=0.95 -->
Both $R_n(f)$ and $f_n^*$ are computable from data; the learning outcome is $f_n^*$. Main question: how large is the **excess risk**
$$R(f_n^*)-R(f^*).$$
Footnote 13: assume the minimum is attained (an approximate minimizer would also serve).

<a id="pdf-681b6f3d947f-p226-b001"></a>
<!-- pdf-source: page=226; block=1; confidence=0.95 -->
**Section 8.4.4 — Bounding the excess risk by the VC dimension.** Specializes the setting to classification problems in which the target `T` is a Boolean function.

<a id="pdf-681b6f3d947f-p226-b002"></a>
<!-- pdf-source: page=226; block=2; confidence=0.97 -->
**Theorem 8.4.4 (Excess risk via VC dimension).** Assume the target `T` is Boolean and the hypothesis space `F` is a class of Boolean functions with finite VC dimension `vc(F) ≥ 1`. Then

$$\mathbb{E}\, R(f_n^*) \le R(f^*) + C\sqrt{\tfrac{\mathrm{vc}(F)}{n}}.$$

<a id="pdf-681b6f3d947f-p226-b003"></a>
<!-- pdf-source: page=226; block=3; confidence=0.97 -->
**Lemma 8.4.5 (Excess risk via uniform deviations).** Pointwise,

$$R(f_n^*) - R(f^*) \le 2\sup_{f\in F} |R_n(f) - R(f)|.$$

<a id="pdf-681b6f3d947f-p226-b004"></a>
<!-- pdf-source: page=226; block=4; confidence=0.96 -->
**Proof (Lemma 8.4.5).** Set `ε := sup_{f∈F} |R_n(f) − R(f)|`. Then

- `R(f_n^*) ≤ R_n(f_n^*) + ε` (since `f_n^* ∈ F`),
- `≤ R_n(f^*) + ε` (since `f_n^*` minimizes `R_n` over `F`),
- `≤ R(f^*) + 2ε` (since `f^* ∈ F`).

Subtracting `R(f^*)` from both sides gives the claim. ∎

<a id="pdf-681b6f3d947f-p226-b005"></a>
<!-- pdf-source: page=226; block=5; confidence=0.94 -->
**Proof of Theorem 8.4.4 (part 1).** By Lemma 8.4.5 it suffices to show

$$\mathbb{E}\sup_{f\in F} |R_n(f) - R(f)| \lesssim \sqrt{\tfrac{\mathrm{vc}(F)}{n}}.$$

Using the definitions (8.34) and (8.32) of empirical and true (population) risk, the left side equals

$$\mathbb{E}\sup_{\ell\in L}\Big| \tfrac1n\sum_{i=1}^n \ell(X_i) - \mathbb{E}\,\ell(X)\Big| \quad (8.35),$$

where `L = {(f − T)^2 : f ∈ F}`. Applying Theorem 8.3.23 directly would only bound this via `vc(L)`, which is not clearly related to `vc(F)`.

<a id="pdf-681b6f3d947f-p227-b001"></a>
<!-- pdf-source: page=227; block=1; confidence=0.94 -->
**Proof of Theorem 8.4.4 (part 2).** Recall from the proof of Theorem 8.3.23 that (8.35) is bounded, up to an absolute constant, by

$$\tfrac{1}{\sqrt n}\,\mathbb{E}\int_0^1 \sqrt{\log N(L, L_2(\mu_n), \varepsilon)}\,d\varepsilon \quad (8.36).$$

The covering numbers satisfy

$$N(L, L_2(\mu_n), \varepsilon) \le N(F, L_2(\mu_n), \varepsilon)\quad\text{for } \varepsilon\in(0,1) \quad (8.37).$$

Hence `L` may be replaced by `F` in (8.36) at the cost of an absolute constant; following the rest of the proof of Theorem 8.3.23 bounds it by `√(vc(F)/n)`, as desired. ∎

<a id="pdf-681b6f3d947f-p227-b002"></a>
<!-- pdf-source: page=227; block=2; confidence=0.92 -->
**Exercise 8.4.6.** Verify inequality (8.37). Hint: for any Boolean `f, g, T`, use the identity `((f − T)^2 − (g − T)^2)^2 = (f − g)^2`.

<a id="pdf-681b6f3d947f-p227-b003"></a>
<!-- pdf-source: page=227; block=3; confidence=0.95 -->
**Section 8.4.5 — Interpretation and examples.**

<a id="pdf-681b6f3d947f-p227-b004"></a>
<!-- pdf-source: page=227; block=4; confidence=0.93 -->
Theorem 8.4.4 states the average excess risk of learning from a sample of size `n` is proportional to `√(vc(F)/n)`. Equivalently, to bound the expected excess risk by `ε` it suffices to take

$$n \asymp \varepsilon^{-2}\,\mathrm{vc}(F),$$

i.e. the sample size need only exceed the VC dimension of `F` up to a constant factor.

<a id="pdf-681b6f3d947f-p227-b005"></a>
<!-- pdf-source: page=227; block=5; confidence=0.90 -->
Example (Figure 8.10): learn an unknown `T : R^2 → {0,1}` (a classification/labeling problem). Collect `n` training points `X_1,…,X_n` sampled i.i.d. from a distribution `P` on the plane with known labels `T(X_i)`, then choose a hypothesis space `F` neither too large (overfitting) nor too small (underfitting).

<a id="pdf-681b6f3d947f-p228-b001"></a>
<!-- pdf-source: page=228; block=1; confidence=0.95 -->
**Setup.** Choose the hypothesis class of circle indicators

$$F := \{ \mathbf{1}_C : \text{circles } C \subset \mathbb{R}^2 \} \quad (8.38),$$

with `vc(F) = 3` (Exercise 8.3.6). Define the empirical risk

$$R_n(f) := \tfrac1n\sum_{i=1}^n (f(X_i) - T(X_i))^2,$$

and the empirical risk minimizer `f_n^* := \arg\min_{f\in F} R_n(f)`, output as the solution.

<a id="pdf-681b6f3d947f-p228-b002"></a>
<!-- pdf-source: page=228; block=2; confidence=0.92 -->
**Exercise 8.4.7.** Check that `f_n^*` is the function in `F` minimizing the number of data points `X_i` where it disagrees with the labels `T(X_i)`.

<a id="pdf-681b6f3d947f-p228-b003"></a>
<!-- pdf-source: page=228; block=3; confidence=0.94 -->
The risk of a Boolean function is `R(f) = P{f(X) ≠ T(X)}`, the probability of mislabeling a fresh point `X` from the same distribution. With `vc(F) = 3`, Theorem 8.4.4 gives

$$\mathbb{E}\, R(f_n^*) \le R(f^*) + \tfrac{C}{\sqrt n},$$

so on average `f_n^*` predicts within `1/√n` error of the best circle `f^*` in `F`.

<a id="pdf-681b6f3d947f-p228-b004"></a>
<!-- pdf-source: page=228; block=4; confidence=0.90 -->
**Exercise 8.4.8 (Random outputs).** The model (8.31) assumes the output `T(X)` is fully determined by input `X`, which is rarely realistic (e.g. disease diagnosis from genetic data). More typically the output `Y` is a random variable correlated with `X`, and the goal is still to predict `Y` from `X` as well as possible.

<a id="pdf-681b6f3d947f-p228-b005"></a>
<!-- pdf-source: page=228; block=5; confidence=0.90 -->
Footnote: `F` may also include all half-spaces, viewed as circles with infinite radius centered at infinity.

<a id="pdf-681b6f3d947f-p229-b001"></a>
<!-- pdf-source: page=229; block=1; confidence=0.90 -->
Extends the learning theory of Theorem 8.4.4 to training data $(X_i,Y_i)$, $i=1,\dots,n$, i.i.d. copies of $(X,Y)$ with input random point $X\in\Omega$ and output random variable $Y$.

<a id="pdf-681b6f3d947f-p229-b002"></a>
<!-- pdf-source: page=229; block=2; confidence=0.90 -->
**Exercise 8.4.9 (Learning in the class of Lipschitz functions).** Hypothesis class $F:=\{f:[0,1]\to[0,1],\ \lVert f\rVert_{\mathrm{Lip}}\le L\}$ and target $T:[0,1]\to[0,1]$.
(a) Show $X_f:=R_n(f)-R(f)$ has sub-gaussian increments: $\lVert X_f-X_g\rVert_{\psi_2}\le \tfrac{C(L)}{\sqrt n}\lVert f-g\rVert_\infty$ for all $f,g\in F$.
(b) Via Dudley's inequality deduce $\mathbb{E}\sup_{f\in F}\lvert R_n(f)-R(f)\rvert\le \tfrac{C(L)}{\sqrt n}$ (hint: as in proof of Theorem 8.2.3).
(c) Conclude excess risk $\mathbb{E}\,R(f_n^*)-R(f^*)\le \tfrac{C(L)}{\sqrt n}$. Here $C(L)$ may vary between parts but depends only on $L$.

<a id="pdf-681b6f3d947f-p229-b003"></a>
<!-- pdf-source: page=229; block=3; confidence=0.97 -->
# 8.5 Generic chaining

<a id="pdf-681b6f3d947f-p229-b004"></a>
<!-- pdf-source: page=229; block=4; confidence=0.92 -->
Dudley's inequality can be loose (cf. Exercise 8.1.12) because the covering numbers $N(T,d,\varepsilon)$ do not carry enough information to control $\mathbb{E}\sup_{t\in T}X_t$.

<a id="pdf-681b6f3d947f-p229-b005"></a>
<!-- pdf-source: page=229; block=5; confidence=0.95 -->
## 8.5.1 A makeover of Dudley's inequality

<a id="pdf-681b6f3d947f-p229-b006"></a>
<!-- pdf-source: page=229; block=6; confidence=0.90 -->
Generic chaining gives accurate two-sided bounds on $\mathbb{E}\sup_{t\in T}X_t$ for sub-gaussian processes via the geometry of $T$, sharpening the chaining of Theorem 8.1.4. Recall the chaining bound (8.12), restated as (8.39):
$$\mathbb{E}\sup_{t\in T}X_t\lesssim \sum_{k=\kappa+1}^{\infty}\varepsilon_{k-1}\sqrt{\log\lvert T_k\rvert}.$$

<a id="pdf-681b6f3d947f-p230-b001"></a>
<!-- pdf-source: page=230; block=1; confidence=0.92 -->
Here $\varepsilon_k$ are decreasing positive numbers and $T_k$ are $\varepsilon_k$-nets with $\lvert T_\kappa\rvert=1$; in Theorem 8.1.4 the choice was $\varepsilon_k=2^{-k}$, $\lvert T_k\rvert=N(T,d,\varepsilon_k)$ (smallest nets). Reverse this: fix the cardinality of $T_k$ and minimize $\varepsilon_k$. Fix subsets $T_k\subset T$ with $\lvert T_0\rvert=1$, $\lvert T_k\rvert\le 2^{2^k}$, $k=1,2,\dots$ (8.40) — an admissible sequence. Put $\varepsilon_k=\sup_{t\in T}d(t,T_k)$, so each $T_k$ is an $\varepsilon_k$-net. Then (8.39) becomes $\mathbb{E}\sup_{t}X_t\lesssim\sum_{k=1}^\infty 2^{k/2}\sup_t d(t,T_{k-1})$, and after re-indexing (8.41):
$$\mathbb{E}\sup_{t\in T}X_t\lesssim \sum_{k=0}^{\infty}2^{k/2}\sup_{t\in T}d(t,T_k).$$

<a id="pdf-681b6f3d947f-p230-b002"></a>
<!-- pdf-source: page=230; block=2; confidence=0.95 -->
## 8.5.2 Talagrand's $\gamma_2$ functional and generic chaining

<a id="pdf-681b6f3d947f-p230-b003"></a>
<!-- pdf-source: page=230; block=3; confidence=0.90 -->
Bound (8.41) is only an equivalent restatement of Dudley's inequality; generic chaining will move the supremum outside the sum in (8.41).

<a id="pdf-681b6f3d947f-p230-b004"></a>
<!-- pdf-source: page=230; block=4; confidence=0.94 -->
**Definition 8.5.1 (Talagrand's $\gamma_2$ functional).** For a metric space $(T,d)$, a sequence $(T_k)_{k=0}^\infty$ of subsets is admissible if the cardinalities satisfy (8.40). The $\gamma_2$ functional is
$$\gamma_2(T,d)=\inf_{(T_k)}\sup_{t\in T}\sum_{k=0}^{\infty}2^{k/2}d(t,T_k),$$
with infimum over all admissible sequences.

<a id="pdf-681b6f3d947f-p230-b005"></a>
<!-- pdf-source: page=230; block=5; confidence=0.90 -->
Since the supremum in $\gamma_2$ is outside the sum, $\gamma_2$ is smaller than the Dudley sum in (8.41); this gap, though seemingly minor, can be real. Footnote 15: the distance from $t\in T$ to $A\subset T$ is $d(t,A):=\inf\{d(t,a):a\in A\}$.

<a id="pdf-681b6f3d947f-p231-b001"></a>
<!-- pdf-source: page=231; block=1; confidence=0.90 -->
**Exercise 8.5.2 ($\gamma_2$ functional and Dudley's sum).** For $T:=\{0\}\cup\{\tfrac{e_k}{\sqrt{1+\log k}},\ k=1,\dots,n\}\subset\mathbb{R}^n$ (as in Exercise 8.1.12):
(a) Show the $\gamma_2$ functional (Euclidean metric) is bounded, $\gamma_2(T,d)=\inf_{(T_k)}\sup_{t}\sum_{k=0}^\infty 2^{k/2}d(t,T_k)\le C$ (hint: use the first $2^{2^k}$ vectors of $T$ for $T_k$).
(b) Check Dudley's sum is unbounded: $\inf_{(T_k)}\sum_{k=0}^\infty 2^{k/2}\sup_t d(t,T_k)\to\infty$ as $n\to\infty$.

<a id="pdf-681b6f3d947f-p231-b002"></a>
<!-- pdf-source: page=231; block=2; confidence=0.90 -->
States an improvement of Dudley's inequality in which the Dudley sum/integral is replaced by the tighter $\gamma_2$ functional.

<a id="pdf-681b6f3d947f-p231-b003"></a>
<!-- pdf-source: page=231; block=3; confidence=0.95 -->
**Theorem 8.5.3 (Generic chaining bound).** Let $(X_t)_{t\in T}$ be a mean-zero random process on metric space $(T,d)$ with sub-gaussian increments as in (8.1). Then
$$\mathbb{E}\sup_{t\in T}X_t\le CK\,\gamma_2(T,d).$$

<a id="pdf-681b6f3d947f-p231-b004"></a>
<!-- pdf-source: page=231; block=4; confidence=0.88 -->
**Proof.** Uses the chaining method of Theorem 8.1.4 done more accurately.
*Step 1 (chaining set-up):* assume $K=1$ and $T$ finite; take an admissible sequence $(T_k)$ with $T_0=\{t_0\}$. Walk from $t_0$ to $t\in T$ along $t_0=\pi_0(t)\to\pi_1(t)\to\cdots\to\pi_K(t)=t$ with $\pi_k(t)\in T_k$ best approximations, $d(t,\pi_k(t))=d(t,T_k)$. Telescoping (8.42): $X_t-X_{t_0}=\sum_{k=1}^{K}(X_{\pi_k(t)}-X_{\pi_{k-1}(t)})$.
*Step 2 (controlling increments):* seek a uniform high-probability bound (8.43): $\lvert X_{\pi_k(t)}-X_{\pi_{k-1}(t)}\rvert\le 2^{k/2}d(t,T_k)$ for all $k\in\mathbb{N}$, all $t\in T$. (Proof continues beyond the supplied pages.)

<a id="pdf-681b6f3d947f-p232-b001"></a>
<!-- pdf-source: page=232; block=1; confidence=0.90 -->
Summing the increment inequalities over all $k$ yields the desired bound in terms of $\gamma_2(T,d)$.

<a id="pdf-681b6f3d947f-p232-b002"></a>
<!-- pdf-source: page=232; block=2; confidence=0.94 -->
**Proof (Step 2, establishing (8.43)).** Fix $k,t$. Sub-gaussianity gives $\|X_{\pi_k(t)}-X_{\pi_{k-1}(t)}\|_{\psi_2}\le d(\pi_k(t),\pi_{k-1}(t))$. Hence for every $u\ge 0$ the event
$$|X_{\pi_k(t)}-X_{\pi_{k-1}(t)}|\le C\,u\,2^{k/2}d(\pi_k(t),\pi_{k-1}(t))\quad(8.44)$$
holds with probability at least $1-2\exp(-8u^2 2^k)$ (choose $C$ large for the constant $8$). Union bound over $|T_k|\cdot|T_{k-1}|\le|T_k|^2\le 2^{2k+1}$ pairs, then over all $k\in\mathbb N$, makes (8.44) hold simultaneously for all $t\in T$, $k\in\mathbb N$ with probability at least
$$1-\sum_{k=1}^\infty 2^{2k+1}\cdot 2\exp(-8u^2 2^k)\ge 1-2\exp(-u^2)\quad(u>c).$$

<a id="pdf-681b6f3d947f-p232-b003"></a>
<!-- pdf-source: page=232; block=3; confidence=0.95 -->
**Proof (Step 3, summing the increments).** On the event where (8.44) holds for all $t,k$, sum over $k\in\mathbb N$ and substitute into the chaining sum (8.42):
$$|X_t-X_{t_0}|\le C u\sum_{k=1}^\infty 2^{k/2}d(\pi_k(t),\pi_{k-1}(t)).\quad(8.45)$$
By the triangle inequality $d(\pi_k(t),\pi_{k-1}(t))\le d(t,\pi_k(t))+d(t,\pi_{k-1}(t))$; using this and re-indexing bounds the right side of (8.45) by $\gamma_2(T,d)$, giving $|X_t-X_{t_0}|\le C_1 u\,\gamma_2(T,d)$. Taking the supremum over $T$: $\sup_{t\in T}|X_t-X_{t_0}|\le C_2 u\,\gamma_2(T,d)$, valid with probability at least $1-2\exp(-u^2)$ for $u>c$. Therefore
$$\Big\|\sup_{t\in T}|X_t-X_{t_0}|\Big\|_{\psi_2}\le C_3\,\gamma_2(T,d).$$

<a id="pdf-681b6f3d947f-p233-b001"></a>
<!-- pdf-source: page=233; block=1; confidence=0.90 -->
This yields the conclusion of Theorem 8.5.3.

<a id="pdf-681b6f3d947f-p233-b002"></a>
<!-- pdf-source: page=233; block=2; confidence=0.90 -->
**Remark 8.5.4 (Supremum of increments).** Generic chaining also gives the uniform bound $\mathbb E\sup_{t,s\in T}|X_t-X_s|\le CK\,\gamma_2(T,d)$, valid even without the mean-zero assumption $\mathbb E X_t=0$. The argument also yields a tail bound for $\sup_{t\in T}X_t$, improved next.

<a id="pdf-681b6f3d947f-p233-b003"></a>
<!-- pdf-source: page=233; block=3; confidence=0.96 -->
**Theorem 8.5.5 (Generic chaining: tail bound).** For a random process $(X_t)_{t\in T}$ on a metric space $(T,d)$ with sub-gaussian increments as in (8.1), and every $u\ge 0$, the event
$$\sup_{t,s\in T}|X_t-X_s|\le CK\big[\gamma_2(T,d)+u\cdot\mathrm{diam}(T)\big]$$
holds with probability at least $1-2\exp(-u^2)$.

<a id="pdf-681b6f3d947f-p233-b004"></a>
<!-- pdf-source: page=233; block=4; confidence=0.92 -->
**Exercise 8.5.6.** Prove Theorem 8.5.5: use a variant of increment bound (8.44) with $u+2^{k/2}$ in place of $u2^{k/2}$, and bound $\sum_{k=1}^\infty d(\pi_k(t),\pi_{k-1}(t))$ by modifying the chain via a "lazy walk": stay at $\pi_k(t)$ for $q-1$ steps until $d(t,\pi_{k+q}(t))\le\tfrac12 d(t,\pi_k(t))$, then jump, making the sum of steps geometrically convergent.

<a id="pdf-681b6f3d947f-p233-b005"></a>
<!-- pdf-source: page=233; block=5; confidence=0.95 -->
**Exercise 8.5.7 (Dudley's integral vs. $\gamma_2$ functional).** Show the $\gamma_2$ functional is bounded by Dudley's integral: for any metric space $(T,d)$,
$$\gamma_2(T,d)\le C\int_0^\infty\sqrt{\log N(T,d,\varepsilon)}\,d\varepsilon.$$

<a id="pdf-681b6f3d947f-p233-b006"></a>
<!-- pdf-source: page=233; block=6; confidence=0.90 -->
**Section 8.6 — Talagrand's majorizing measure and comparison theorems.** The $\gamma_2$ functional (Definition 8.5.1) is harder to compute than metric entropy, but unlike Dudley's integral it bounds Gaussian processes optimally up to an absolute constant, as stated in the following theorem.

<a id="pdf-681b6f3d947f-p234-b001"></a>
<!-- pdf-source: page=234; block=1; confidence=0.96 -->
**Theorem 8.6.1 (Talagrand's majorizing measure theorem).** Let $(X_t)_{t\in T}$ be a mean-zero Gaussian process on a set $T$ with canonical metric (7.13), $d(t,s)=\|X_t-X_s\|_{L^2}$. Then
$$c\cdot\gamma_2(T,d)\le \mathbb E\sup_{t\in T}X_t\le C\cdot\gamma_2(T,d).$$

<a id="pdf-681b6f3d947f-p234-b002"></a>
<!-- pdf-source: page=234; block=2; confidence=0.90 -->
The upper bound follows from generic chaining (Theorem 8.5.3); the lower bound (proof omitted) is a multi-scale strengthening of Sudakov's inequality (Theorem 7.4.1). Since the upper bound holds for any sub-gaussian process, combining both bounds shows any sub-gaussian process is bounded (via $\gamma_2$) by a Gaussian process.

<a id="pdf-681b6f3d947f-p234-b003"></a>
<!-- pdf-source: page=234; block=3; confidence=0.96 -->
**Corollary 8.6.2 (Talagrand's comparison inequality).** Let $(X_t)_{t\in T}$ be a mean-zero random process and $(Y_t)_{t\in T}$ a mean-zero Gaussian process. If for all $t,s\in T$, $\|X_t-X_s\|_{\psi_2}\le K\|Y_t-Y_s\|_{L^2}$, then
$$\mathbb E\sup_{t\in T}X_t\le CK\,\mathbb E\sup_{t\in T}Y_t.$$

<a id="pdf-681b6f3d947f-p234-b004"></a>
<!-- pdf-source: page=234; block=4; confidence=0.95 -->
**Proof.** Take the canonical metric $d(t,s)=\|Y_t-Y_s\|_{L^2}$. Apply generic chaining (Theorem 8.5.3) then the lower bound of Theorem 8.6.1:
$$\mathbb E\sup_{t\in T}X_t\le CK\gamma_2(T,d)\le CK\,\mathbb E\sup_{t\in T}Y_t.\qquad\blacksquare$$

<a id="pdf-681b6f3d947f-p234-b005"></a>
<!-- pdf-source: page=234; block=5; confidence=0.90 -->
Corollary 8.6.2 extends Sudakov–Fernique's inequality (Theorem 7.2.11) to sub-gaussian processes, at the cost of an absolute constant factor.

<a id="pdf-681b6f3d947f-p234-b006"></a>
<!-- pdf-source: page=234; block=6; confidence=0.90 -->
Apply Corollary 8.6.2 to the canonical Gaussian process $Y_x=\langle g,x\rangle$, $x\in T\subset\mathbb R^n$. Its magnitude $w(T)=\mathbb E\sup_{x\in T}\langle g,x\rangle$ is the Gaussian width of $T$ (Section 7.5), giving the next corollary.

<a id="pdf-681b6f3d947f-p234-b007"></a>
<!-- pdf-source: page=234; block=7; confidence=0.90 -->
**Corollary 8.6.3 (Talagrand's comparison inequality: geometric form).** Let $(X_x)_{x\in T}$ be a mean-zero random process on $T\subset\mathbb R^n$ with $\|X_x-X_y\|_{\psi_2}\le K\|x-y\|_2$ for all $x,y\in T$. [Statement continues on the next page.]

<a id="pdf-681b6f3d947f-p235-b001"></a>
<!-- pdf-source: page=235; block=1; confidence=0.90 -->
Concluding inequality of the preceding statement: `E sup_{x∈T} X_x ≤ C K w(T)`, where `w(T)` is the Gaussian width.

<a id="pdf-681b6f3d947f-p235-b002"></a>
<!-- pdf-source: page=235; block=2; confidence=0.90 -->
**Exercise 8.6.4.** For a process `(X_x)_{x∈T}` on `T ⊂ R^n` (not necessarily mean zero) with `X_0 = 0` and sub-gaussian increments `‖X_x − X_y‖_{ψ2} ≤ K ‖x − y‖_2` for all `x, y ∈ T ∪ {0}`, prove `E sup_{x∈T} |X_x| ≤ C K γ(T)`, where `γ(T)` is the Gaussian complexity. Hint: apply Remark 8.5.4 and the majorizing measure theorem to bound via `w(T ∪ {0})`, then convert to Gaussian complexity using Exercise 7.6.9.

<a id="pdf-681b6f3d947f-p235-b003"></a>
<!-- pdf-source: page=235; block=3; confidence=0.92 -->
**Exercise 8.6.5.** In the setting of Exercise 8.6.4, show that for every `u ≥ 0`, `sup_{x∈T} |X_x| ≤ C K ( w(T) + u · rad(T) )` with probability at least `1 − 2 exp(−u²)`. Hint: argue as in Exercise 8.6.4 using Theorem 8.5.5 and Exercise 7.6.9.

<a id="pdf-681b6f3d947f-p235-b004"></a>
<!-- pdf-source: page=235; block=4; confidence=0.93 -->
**Exercise 8.6.6.** In the setting of Exercise 8.6.4, verify `( E sup_{x∈T} |X_x|^p )^{1/p} ≤ C √p · K γ(T)`.

<a id="pdf-681b6f3d947f-p235-b005"></a>
<!-- pdf-source: page=235; block=5; confidence=0.95 -->
**Section 8.7 (Chevet's inequality).** As an application of Talagrand's comparison inequality (Corollary 8.6.2), the goal is a uniform bound on the random quadratic form

`sup_{x∈T, y∈S} ⟨A x, y⟩`   (8.46)

for a random matrix `A` and general sets `T`, `S`. Earlier norm-of-random-matrix analyses (Theorems 4.4.5, 7.3.1) treated `T`, `S` as Euclidean balls; here they are arbitrary geometric sets, and the bound depends on two parameters: the Gaussian width and the radius,

`rad(T) := sup_{x∈T} ‖x‖_2`   (8.47).

<a id="pdf-681b6f3d947f-p236-b001"></a>
<!-- pdf-source: page=236; block=1; confidence=0.97 -->
**Theorem 8.7.1 (Sub-gaussian Chevet's inequality).** Let `A` be an `m × n` random matrix with independent, mean-zero, sub-gaussian entries `A_{ij}`, and let `T ⊂ R^n`, `S ⊂ R^m` be arbitrary bounded sets. Then

`E sup_{x∈T, y∈S} ⟨A x, y⟩ ≤ C K [ w(T) rad(S) + w(S) rad(T) ]`,

where `K = max_{ij} ‖A_{ij}‖_{ψ2}`.

<a id="pdf-681b6f3d947f-p236-b002"></a>
<!-- pdf-source: page=236; block=2; confidence=0.95 -->
Taking `T = S^{n−1}` and `S = S^{m−1}` recovers the operator-norm bound `E ‖A‖ ≤ C K ( √n + √m )`, obtained earlier in Section 4.4.2 by a different method.

<a id="pdf-681b6f3d947f-p236-b003"></a>
<!-- pdf-source: page=236; block=3; confidence=0.95 -->
**Proof of Theorem 8.7.1.** Follow the method of Theorem 7.3.1, replacing Sudakov–Fernique by Talagrand's comparison inequality. Assume WLOG `K = 1`. Bound the process `X_{uv} := ⟨A u, v⟩`, `u ∈ T`, `v ∈ S`. For `(u,v), (w,z) ∈ T × S`,

`‖X_{uv} − X_{wz}‖_{ψ2} = ‖ Σ_{i,j} A_{ij}(u_i v_j − w_i z_j) ‖_{ψ2}`
`≤ ( Σ_{i,j} ‖A_{ij}(u_i v_j − w_i z_j)‖_{ψ2}^2 )^{1/2}`  (Proposition 2.6.1)
`≤ ( Σ_{i,j} |u_i v_j − w_i z_j|^2 )^{1/2}`  (since `‖A_{ij}‖_{ψ2} ≤ 1`)
`= ‖u v^T − w z^T‖_F = ‖(u v^T − w v^T) + (w v^T − w z^T)‖_F`
`≤ ‖(u − w) v^T‖_F + ‖w (v − z)^T‖_F = ‖u − w‖_2 ‖v‖_2 + ‖v − z‖_2 ‖w‖_2`
`≤ ‖u − w‖_2 rad(S) + ‖v − z‖_2 rad(T)`,

using add/subtract and the triangle inequality. This shows `(X_{uv})` has sub-gaussian increments.

<a id="pdf-681b6f3d947f-p236-b004"></a>
<!-- pdf-source: page=236; block=4; confidence=0.95 -->
**Proof (continued).** Choose the comparison Gaussian process suggested by the increment computation:

`Y_{uv} := ⟨g, u⟩ rad(S) + ⟨h, v⟩ rad(T)`,

with `g ∼ N(0, I_n)` and `h ∼ N(0, I_m)` independent Gaussian vectors.

<a id="pdf-681b6f3d947f-p237-b001"></a>
<!-- pdf-source: page=237; block=1; confidence=0.95 -->
**Proof (continued).** The increments of `Y` are

`‖Y_{uv} − Y_{wz}‖_{L2}^2 = ‖u − w‖_2^2 rad(S)^2 + ‖v − z‖_2^2 rad(T)^2`

(checked as in Theorem 7.3.1). Comparing processes gives `‖X_{uv} − X_{wz}‖_{ψ2} ≲ ‖Y_{uv} − Y_{wz}‖_2`. By Talagrand's comparison inequality (Corollary 8.6.3),

`E sup_{u∈T, v∈S} X_{uv} ≲ E sup_{u∈T, v∈S} Y_{uv} = E sup_{u∈T} ⟨g, u⟩ rad(S) + E sup_{v∈S} ⟨h, v⟩ rad(T) = w(T) rad(S) + w(S) rad(T)`,

as claimed. ∎

<a id="pdf-681b6f3d947f-p237-b002"></a>
<!-- pdf-source: page=237; block=2; confidence=0.93 -->
**Exercise 8.7.2.** Chevet's inequality is optimal up to an absolute constant. For `A` with independent `N(0,1)` entries and bounded `T ⊂ R^n`, `S ⊂ R^m`, show the reverse bound

`E sup_{x∈T, y∈S} ⟨A x, y⟩ ≥ c [ w(T) rad(S) + w(S) rad(T) ]`.

Hint: use `E sup_{x∈T, y∈S} ⟨A x, y⟩ ≥ sup_{x∈T} E sup_{y∈S} ⟨A x, y⟩`.

<a id="pdf-681b6f3d947f-p237-b003"></a>
<!-- pdf-source: page=237; block=3; confidence=0.93 -->
**Exercise 8.7.3.** Under the assumptions of Theorem 8.7.1, prove a tail bound for `sup_{x∈T, y∈S} ⟨A x, y⟩`. Hint: use Exercise 8.6.5.

<a id="pdf-681b6f3d947f-p237-b004"></a>
<!-- pdf-source: page=237; block=4; confidence=0.94 -->
**Exercise 8.7.4.** If the entries of `A` are `N(0,1)`, show Theorem 8.7.1 holds with sharp constant 1:

`E sup_{x∈T, y∈S} ⟨A x, y⟩ ≤ w(T) rad(S) + w(S) rad(T)`.

Hint: use Sudakov–Fernique's inequality (Theorem 7.2.11) in place of Talagrand's comparison inequality.

<a id="pdf-681b6f3d947f-p237-b005"></a>
<!-- pdf-source: page=237; block=5; confidence=0.90 -->
**Section 8.8 (Notes).** Chaining appears already in Kolmogorov's proof of his continuity theorem for Brownian motion (ref. [156, Ch. 1]). Dudley's integral inequality (Theorem 8.1.3) traces to R. Dudley; the Section 8.1 exposition follows [130, Ch. 11], [199, Sec. 1.2], [212, Sec. 5.3]. The upper bound in Theorem 8.1.13 (a reverse Sudakov inequality) is apparently folklore.

<a id="pdf-681b6f3d947f-p238-b001"></a>
<!-- pdf-source: page=238; block=1; confidence=0.80 -->
## 8.8 Notes (Chaining)

<a id="pdf-681b6f3d947f-p238-b002"></a>
<!-- pdf-source: page=238; block=2; confidence=0.90 -->
Bibliographic notes: Monte-Carlo methods and Markov chains [38]; empirical-process theory in statistics/ML [211,210,171,143]. In empirical-process terms, Theorem 8.2.3 says the class of Lipschitz functions F is uniform Glivenko-Cantelli; presentation and the link to Wasserstein distance / transportation follow [212, Ex. 5.15], with [224] for transportation of measures.

<a id="pdf-681b6f3d947f-p238-b003"></a>
<!-- pdf-source: page=238; block=3; confidence=0.90 -->
VC dimension (Section 8.3) originates with Vapnik–Chervonenkis [217]; modern treatments in [211, 130, 212, 138, 143]. Pajor's Lemma 8.3.13 is due to A. Pajor [164]; see [79], [130], [212, Thm 7.19], [211, Lem. 2.6.2].

<a id="pdf-681b6f3d947f-p238-b004"></a>
<!-- pdf-source: page=238; block=4; confidence=0.90 -->
Sauer–Shelah Lemma (Theorem 8.3.16) was proved independently by Vapnik–Chervonenkis [217], N. Sauer [180], and Perles–Shelah [184]. Various proofs [25, 138, 130] and variants [101,196,197,6,219] are known.

<a id="pdf-681b6f3d947f-p238-b005"></a>
<!-- pdf-source: page=238; block=5; confidence=0.90 -->
Theorem 8.3.18 is due to R. Dudley [70] (see [130], [211, Thm 2.6.4]). The dimension-reduction Lemma 8.3.19 is implicit in Dudley's proof, stated explicitly in [146] and reproduced in [212, Lem. 7.17]. Generalizations of VC theory from {0,1} to real-valued function classes: [146,176], [212, Sec. 7.3–7.4].

<a id="pdf-681b6f3d947f-p238-b006"></a>
<!-- pdf-source: page=238; block=6; confidence=0.90 -->
Bounds on empirical processes via VC dimension (Theorem 8.3.23) trace to Vapnik–Chervonenkis [217]; see [143,18,211,176], [212, Ch. 7]. Presentation follows [212, Cor. 7.18]; the result can be derived from [18, Thm 6] and [33, Sec. 5].

<a id="pdf-681b6f3d947f-p238-b007"></a>
<!-- pdf-source: page=238; block=7; confidence=0.90 -->
Glivenko–Cantelli theorem (Theorem 8.3.26) is a 1933 result [82,48] predating VC theory; see [130, Sec. 14.2], [211,71]. Example 8.3.27 concerns discrepancy theory ([137]). Section 8.4 introduces statistical learning theory; tutorials [30,143] and books [106,99,123].

<a id="pdf-681b6f3d947f-p238-b008"></a>
<!-- pdf-source: page=238; block=8; confidence=0.90 -->
Generic chaining (Section 8.5) was developed by M. Talagrand from 1985 (after Fernique [75]) as a sharp method for bounding Gaussian processes; presentation follows the book [199]. The upper bound on sub-gaussian processes is Theorem 8.5.3.

<a id="pdf-681b6f3d947f-p239-b001"></a>
<!-- pdf-source: page=239; block=1; confidence=0.90 -->
Theorem 8.5.3 corresponds to [199, Thm 2.2.22]; the lower/majorizing-measure bound (Theorem 8.6.1) to [199, Thm 2.4.1]; Talagrand's comparison inequality (Corollary 8.6.2) to [199, Thm 2.4.12]. Alternative presentations [212, Ch. 6]; a different proof of the majorizing measure theorem by R. van Handel [214,215]. The high-probability generic chaining bound (Theorem 8.5.5) is [199, Thm 2.2.27], also proved by S. Dirksen [63].

<a id="pdf-681b6f3d947f-p239-b002"></a>
<!-- pdf-source: page=239; block=2; confidence=0.90 -->
Section 8.7 presents Chevet's inequality for sub-gaussian processes (literature states it only for Gaussian processes). Due to S. Chevet [54]; constants improved by Y. Gordon [84], giving the form in Exercise 8.7.4. Exposition [11, Sec. 9.4]; variants/applications [205,2].

<a id="pdf-681b6f3d947f-p240-b001"></a>
<!-- pdf-source: page=240; block=1; confidence=0.97 -->
# 9. Deviations of random matrices and geometric consequences

<a id="pdf-681b6f3d947f-p240-b002"></a>
<!-- pdf-source: page=240; block=2; confidence=0.92 -->
For an $m\times n$ random matrix $A$, the chapter establishes a uniform deviation inequality showing that with high probability the approximate equality $\|Ax\|_2 \approx \mathbb{E}\|Ax\|_2$ (9.1) holds simultaneously for all $x$ in an arbitrary subset $T\subset\mathbb{R}^n$; quantitatively, $\|Ax\|_2 = \mathbb{E}\|Ax\|_2 + O(\gamma(T))$ for all $x\in T$ (9.2), where $\gamma(T)$ is the Gaussian complexity (Section 7.6.2). Section 9.1 derives (9.2) from Talagrand's comparison inequality. Consequences (Sections 9.2–9.4) include two-sided bounds on random matrices, random projections of geometric sets, covariance estimation, Johnson–Lindenstrauss and its infinite-set generalization, and the $M^*$ bound and Escape theorem.

<a id="pdf-681b6f3d947f-p240-b003"></a>
<!-- pdf-source: page=240; block=3; confidence=0.97 -->
## 9.1 Matrix deviation inequality

<a id="pdf-681b6f3d947f-p240-b004"></a>
<!-- pdf-source: page=240; block=4; confidence=0.95 -->
**Theorem 9.1.1 (Matrix deviation inequality).** Let $A$ be an $m\times n$ matrix whose rows $A_i$ are independent, isotropic, sub-gaussian random vectors in $\mathbb{R}^n$. Then for any subset $T\subset\mathbb{R}^n$,
$$\mathbb{E}\,\sup_{x\in T}\bigl|\,\|Ax\|_2 - \sqrt{m}\,\|x\|_2\,\bigr| \le CK^2\,\gamma(T),$$
where $\gamma(T)$ is the Gaussian complexity (Section 7.6.2) and $K=\max_i\|A_i\|_{\psi_2}$.

<a id="pdf-681b6f3d947f-p241-b001"></a>
<!-- pdf-source: page=241; block=1; confidence=0.97 -->
## 9.1 Matrix deviation inequality

<a id="pdf-681b6f3d947f-p241-b002"></a>
<!-- pdf-source: page=241; block=2; confidence=0.90 -->
Before proving the theorem, one checks that $\mathbb{E}\,\|Ax\|_2 \approx \sqrt{m}\,\|x\|_2$, so that Theorem 9.1.1 indeed yields (9.2).

<a id="pdf-681b6f3d947f-p241-b003"></a>
<!-- pdf-source: page=241; block=3; confidence=0.90 -->
**Exercise 9.1.2 (Deviation around expectation).** Deduce from Theorem 9.1.1 that
$$\mathbb{E}\,\sup_{x\in T}\bigl|\,\|Ax\|_2 - \mathbb{E}\,\|Ax\|_2\,\bigr| \le CK^2\gamma(T).$$
Hint: bound the difference between $\mathbb{E}\,\|Ax\|_2$ and $\sqrt{m}\,\|x\|_2$ using concentration of norm (Theorem 3.1.1).

<a id="pdf-681b6f3d947f-p241-b004"></a>
<!-- pdf-source: page=241; block=4; confidence=0.92 -->
Theorem 9.1.1 will be deduced from Talagrand's comparison inequality (Corollary 8.6.3, specifically Exercise 8.6.4). It suffices to check that the process $X_x := \|Ax\|_2 - \sqrt{m}\,\|x\|_2$, indexed by $x\in\mathbb{R}^n$, has sub-gaussian increments.

<a id="pdf-681b6f3d947f-p241-b005"></a>
<!-- pdf-source: page=241; block=5; confidence=0.95 -->
**Theorem 9.1.3 (Sub-gaussian increments).** Let $A$ be an $m\times n$ matrix whose rows $A_i$ are independent, isotropic, sub-gaussian random vectors in $\mathbb{R}^n$. Then the process $X_x := \|Ax\|_2 - \sqrt{m}\,\|x\|_2$ has sub-gaussian increments:
$$\|X_x - X_y\|_{\psi_2} \le CK^2\|x-y\|_2 \qquad (9.3)$$
for all $x,y\in\mathbb{R}^n$, where $K = \max_i \|A_i\|_{\psi_2}$.

<a id="pdf-681b6f3d947f-p241-b006"></a>
<!-- pdf-source: page=241; block=6; confidence=0.94 -->
**Proof of Theorem 9.1.1.** By Theorem 9.1.3 and Talagrand's comparison inequality (Exercise 8.6.4), $\mathbb{E}\,\sup_{x\in T}|X_x| \le CK^2\gamma(T)$, as announced. It remains to prove Theorem 9.1.3, which is done in stages of increasing generality.

<a id="pdf-681b6f3d947f-p241-b007"></a>
<!-- pdf-source: page=241; block=7; confidence=0.95 -->
### 9.1.1 Theorem 9.1.3 for unit vector $x$ and zero vector $y$

<a id="pdf-681b6f3d947f-p241-b008"></a>
<!-- pdf-source: page=241; block=8; confidence=0.94 -->
**Proof step.** Assume $\|x\|_2 = 1$ and $y = 0$. Then (9.3) reduces to
$$\left\| \|Ax\|_2 - \sqrt{m} \right\|_{\psi_2} \le CK^2. \qquad (9.4)$$

<a id="pdf-681b6f3d947f-p242-b001"></a>
<!-- pdf-source: page=242; block=1; confidence=0.93 -->
**Proof step.** $Ax$ is a random vector in $\mathbb{R}^m$ with independent sub-gaussian coordinates $\langle A_i, x\rangle$ satisfying $\mathbb{E}\,\langle A_i,x\rangle^2 = 1$ by isotropy. Concentration of Norm (Theorem 3.1.1) then yields (9.4).

<a id="pdf-681b6f3d947f-p242-b002"></a>
<!-- pdf-source: page=242; block=2; confidence=0.95 -->
### 9.1.2 Theorem 9.1.3 for unit vectors $x,y$ and the squared process

<a id="pdf-681b6f3d947f-p242-b003"></a>
<!-- pdf-source: page=242; block=3; confidence=0.93 -->
**Proof step.** Assume $\|x\|_2 = \|y\|_2 = 1$; then (9.3) becomes
$$\left\| \|Ax\|_2 - \|Ay\|_2 \right\|_{\psi_2} \le CK^2\|x-y\|_2. \qquad (9.5)$$
First prove a squared-norm version:
$$\|Ax\|_2^2 - \|Ay\|_2^2 = \big(\|Ax\|_2 + \|Ay\|_2\big)\big(\|Ax\|_2 - \|Ay\|_2\big) \lesssim \sqrt{m}\,\|x-y\|_2. \qquad (9.6)$$
Define
$$Z := \frac{\|Ax\|_2^2 - \|Ay\|_2^2}{\|x-y\|_2} = \frac{\langle A(x-y), A(x+y)\rangle}{\|x-y\|_2} = \langle Au, Av\rangle, \qquad (9.7)$$
where $u := (x-y)/\|x-y\|_2$ and $v := x+y$. The goal is $|Z| \lesssim \sqrt{m}$ with high probability. Since coordinates of $Au, Av$ are $\langle A_i,u\rangle, \langle A_i,v\rangle$, one has $Z = \sum_{i=1}^m \langle A_i,u\rangle\langle A_i,v\rangle$, a sum of independent random variables.

<a id="pdf-681b6f3d947f-p242-b004"></a>
<!-- pdf-source: page=242; block=4; confidence=0.95 -->
**Lemma 9.1.4.** The random variables $\langle A_i,u\rangle\langle A_i,v\rangle$ are independent, mean zero, and sub-exponential; more precisely,
$$\big\| \langle A_i,u\rangle\langle A_i,v\rangle \big\|_{\psi_1} \le 2K^2.$$

<a id="pdf-681b6f3d947f-p243-b001"></a>
<!-- pdf-source: page=243; block=1; confidence=0.95 -->
**Proof.** Independence follows from the construction. For mean zero, the two factors $\langle A_i,u\rangle$ and $\langle A_i,v\rangle$ need not be independent, but are uncorrelated: by isotropy,
$$\mathbb{E}\,\langle A_i, x-y\rangle\langle A_i, x+y\rangle = \mathbb{E}\big[\langle A_i,x\rangle^2 - \langle A_i,y\rangle^2\big] = 1 - 1 = 0,$$
so $\mathbb{E}\,\langle A_i,u\rangle\langle A_i,v\rangle = 0$. By Lemma 2.7.7 (product of sub-gaussians is sub-exponential),
$$\big\|\langle A_i,u\rangle\langle A_i,v\rangle\big\|_{\psi_1} \le \|\langle A_i,u\rangle\|_{\psi_2}\,\|\langle A_i,v\rangle\|_{\psi_2} \le K\|u\|_2 \cdot K\|v\|_2 \le 2K^2,$$
using $\|u\|_2 = 1$ and $\|v\|_2 \le \|x\|_2 + \|y\|_2 \le 2$.

<a id="pdf-681b6f3d947f-p243-b002"></a>
<!-- pdf-source: page=243; block=2; confidence=0.90 -->
To bound $Z$, apply Bernstein's inequality (Corollary 2.8.3) for a sum of independent, mean-zero, sub-exponential random variables.

<a id="pdf-681b6f3d947f-p243-b003"></a>
<!-- pdf-source: page=243; block=3; confidence=0.90 -->
**Exercise 9.1.5.** Applying Bernstein's inequality (Corollary 2.8.3) and simplifying gives
$$\mathbb{P}\big\{ |Z| \ge s\sqrt{m} \big\} \le 2\exp\!\left(-\frac{cs^2}{K^4}\right)$$
for $0 \le s \le \sqrt{m}$ (in this range the sub-gaussian tail dominates; use $2K^2$ in place of $K$ per Lemma 9.1.4). Recalling the definition of $Z$ gives the desired bound (9.6).

<a id="pdf-681b6f3d947f-p243-b004"></a>
<!-- pdf-source: page=243; block=4; confidence=0.95 -->
### 9.1.3 Theorem 9.1.3 for unit vectors $x,y$ and the original process

<a id="pdf-681b6f3d947f-p243-b005"></a>
<!-- pdf-source: page=243; block=5; confidence=0.95 -->
**Lemma 9.1.6 (Unit $y$, original process).** Let $x,y \in S^{n-1}$. Then
$$\left\| \|Ax\|_2 - \|Ay\|_2 \right\|_{\psi_2} \le CK^2\|x-y\|_2.$$

<a id="pdf-681b6f3d947f-p243-b006"></a>
<!-- pdf-source: page=243; block=6; confidence=0.90 -->
**Proof.** Fix $s \ge 0$. By definition of the sub-gaussian norm (cf. (2.14), Remark 2.5.3), it suffices to prove
$$p(s) := \mathbb{P}\left\{ \frac{|\|Ax\|_2 - \|Ay\|_2|}{\|x-y\|_2} \ge s \right\} \le 4\exp\!\left(-\frac{cs^2}{K^4}\right). \qquad (9.8)$$

<a id="pdf-681b6f3d947f-p244-b001"></a>
<!-- pdf-source: page=244; block=1; confidence=0.95 -->
**Proof (continued).** Small and large *s* are treated separately.

*Case 1: s ≤ 2√m.* Multiply the inequality defining p(s) by ∥Ax∥₂ + ∥Ay∥₂; with Z as in (9.7),

p(s) = P{|Z| ≥ s(∥Ax∥₂ + ∥Ay∥₂)} ≤ P{|Z| ≥ s∥Ax∥₂}.

Since ∥Ax∥₂ ≈ √m with high probability by (9.4), split into the events ∥Ax∥₂ ≥ √m/2 and ∥Ax∥₂ < √m/2 (where |Z| ≥ s√m/2):

p(s) ≤ P{|Z| ≥ s√m/2} + P{∥Ax∥₂ < √m/2} =: p₁(s) + p₂(s).

Exercise 9.1.5 gives p₁(s) ≤ 2·exp(−cs²/K⁴). By (9.4) and the triangle inequality, p₂(s) ≤ P{|∥Ax∥₂ − √m| > √m/2} ≤ 2·exp(−cs²/K⁴). Summing, p(s) ≤ 4·exp(−cs²/K⁴).

<a id="pdf-681b6f3d947f-p244-b002"></a>
<!-- pdf-source: page=244; block=2; confidence=0.95 -->
**Proof (continued).** *Case 2: s > 2√m.* Simplify inequality (9.8) defining p(s): by the triangle inequality |∥Ax∥₂ − ∥Ay∥₂| ≤ ∥A(x − y)∥₂. Hence, with u := (x − y)/∥x − y∥₂,

p(s) ≤ P{∥Au∥₂ ≥ s} ≤ P{∥Au∥₂ − √m ≥ s/2}  (since s > 2√m) ≤ 2·exp(−cs²/K⁴)  (by (9.4)).

In both cases the desired estimate (9.8) holds, completing the proof of the lemma.

<a id="pdf-681b6f3d947f-p245-b001"></a>
<!-- pdf-source: page=245; block=1; confidence=0.98 -->
## 9.1.4 Theorem 9.1.3 in full generality

<a id="pdf-681b6f3d947f-p245-b002"></a>
<!-- pdf-source: page=245; block=2; confidence=0.94 -->
**Proof.** Establish (9.3) for arbitrary x, y ∈ Rⁿ. By scaling, assume ∥x∥₂ = 1 and ∥y∥₂ ≥ 1 (9.9). Define the contraction of y onto the unit sphere ȳ := y/∥y∥₂ (9.10). By the triangle inequality,

∥Xx − Xy∥_{ψ₂} ≤ ∥Xx − Xȳ∥_{ψ₂} + ∥Xȳ − Xy∥_{ψ₂}.

Since x and ȳ are unit vectors, Lemma 9.1.6 bounds the first part: ∥Xx − Xȳ∥_{ψ₂} ≤ CK²∥x − ȳ∥₂. Since ȳ and y are collinear, ∥Xȳ − Xy∥_{ψ₂} = ∥ȳ − y∥₂ · ∥Xȳ∥_{ψ₂}, and (9.4) gives ∥Xȳ∥_{ψ₂} ≤ CK² (ȳ a unit vector). Combining,

∥Xx − Xy∥_{ψ₂} ≤ CK²(∥x − ȳ∥₂ + ∥ȳ − y∥₂)  (9.11).

The RHS must be bounded by ∥x − y∥₂; although the triangle inequality gives the reverse bound, it can be approximately reversed here (Figure 9.1: ∥x − ȳ∥₂ + ∥ȳ − y∥₂ ≤ √2·∥x − y∥₂), as confirmed by Exercise 9.1.7.

<a id="pdf-681b6f3d947f-p245-b003"></a>
<!-- pdf-source: page=245; block=3; confidence=0.96 -->
**Exercise 9.1.7 (Reverse triangle inequality).** For vectors x, y, ȳ ∈ Rⁿ satisfying (9.9) and (9.10), show that ∥x − ȳ∥₂ + ∥ȳ − y∥₂ ≤ √2·∥x − y∥₂.

<a id="pdf-681b6f3d947f-p246-b001"></a>
<!-- pdf-source: page=246; block=1; confidence=0.96 -->
**Proof (concluded).** Using Exercise 9.1.7, (9.11) yields the desired bound ∥Xx − Xy∥_{ψ₂} ≤ CK²∥x − y∥₂. Theorem 9.1.3 is completely proved.

<a id="pdf-681b6f3d947f-p246-b002"></a>
<!-- pdf-source: page=246; block=2; confidence=0.95 -->
**Exercise 9.1.8 (tail bounds).** Under the conditions of Theorem 9.1.1: for any u ≥ 0, the event

|sup_{x∈T} (∥Ax∥₂ − √m·∥x∥₂)| ≤ CK²[w(T) + u·rad(T)]  (9.12)

holds with probability at least 1 − 2·exp(−u²), where rad(T) is the radius of T from (8.47). Hint: high-probability Talagrand comparison inequality (Exercise 8.6.5).

<a id="pdf-681b6f3d947f-p246-b003"></a>
<!-- pdf-source: page=246; block=3; confidence=0.96 -->
**Exercise 9.1.9.** Argue that the RHS of (9.12) can be further bounded by CK²·u·γ(T) for u ≥ 1, and conclude that Exercise 9.1.8 implies Theorem 9.1.1.

<a id="pdf-681b6f3d947f-p246-b004"></a>
<!-- pdf-source: page=246; block=4; confidence=0.95 -->
**Exercise 9.1.10 (Deviation of squares).** Under the conditions of Theorem 9.1.1, show that

|E sup_{x∈T} (∥Ax∥₂² − m·∥x∥₂²)| ≤ CK⁴·γ(T)² + CK²·√m·rad(T)·γ(T).

Hint: reduce to the deviation inequality via a² − b² = (a − b)(a + b).

<a id="pdf-681b6f3d947f-p246-b005"></a>
<!-- pdf-source: page=246; block=5; confidence=0.95 -->
**Exercise 9.1.11 (Deviation of random projections).** Prove a version of the matrix deviation inequality (Theorem 9.1.1) for random projections. Let P be the orthogonal projection in Rⁿ onto an m-dimensional subspace uniformly distributed in the Grassmannian G_{n,m}. Show that for any T ⊂ Rⁿ,

|E sup_{x∈T} (∥Px∥₂ − √(m/n)·∥x∥₂)| ≤ CK²·γ(T)/√n.

<a id="pdf-681b6f3d947f-p246-b006"></a>
<!-- pdf-source: page=246; block=6; confidence=0.97 -->
## 9.2 Random matrices, random projections and covariance estimation

The matrix deviation inequality has several important consequences, presented here and in the next section.

<a id="pdf-681b6f3d947f-p246-b007"></a>
<!-- pdf-source: page=246; block=7; confidence=0.96 -->
### 9.2.1 Two-sided bounds on random matrices

Applying the matrix deviation inequality to the unit Euclidean sphere T = S^{n−1} recovers the two-sided bounds on random matrices from Section 4.6. For T = S^{n−1}: rad(T) = 1 and w(T) ≤ √n.

<a id="pdf-681b6f3d947f-p247-b001"></a>
<!-- pdf-source: page=247; block=1; confidence=0.96 -->
The matrix deviation inequality (Exercise 9.1.8) with the triangle inequality gives that
$$\sqrt{m} - CK^2(\sqrt{n}+u) \le \|Ax\|_2 \le \sqrt{m} + CK^2(\sqrt{n}+u) \quad \forall x\in S^{n-1}$$
holds with probability at least $1-2\exp(-u^2)$. Interpreting this via (4.5) as a two-sided bound on the extreme singular values yields $\sqrt{m}-CK^2(\sqrt{n}+u) \le s_n(A) \le s_1(A) \le \sqrt{m}+CK^2(\sqrt{n}+u)$, recovering Theorem 4.6.1.

<a id="pdf-681b6f3d947f-p247-b002"></a>
<!-- pdf-source: page=247; block=2; confidence=0.99 -->
**9.2.2 Sizes of random projections of geometric sets**

<a id="pdf-681b6f3d947f-p247-b003"></a>
<!-- pdf-source: page=247; block=3; confidence=0.97 -->
**Proposition 9.2.1 (Sizes of random projections of sets).** Let $T\subset\mathbb{R}^n$ be bounded, and let $A$ be an $m\times n$ matrix whose rows $A_i$ are independent, isotropic, sub-gaussian random vectors in $\mathbb{R}^n$. Then the scaled matrix $P := \tfrac{1}{\sqrt{n}}A$ (a "sub-gaussian projection") satisfies
$$\mathbb{E}\,\mathrm{diam}(PT) \le \sqrt{\tfrac{m}{n}}\,\mathrm{diam}(T) + CK^2 w_s(T),$$
where $w_s(T)$ is the spherical width of $T$ and $K = \max_i \|A_i\|_{\psi_2}$.

<a id="pdf-681b6f3d947f-p247-b004"></a>
<!-- pdf-source: page=247; block=4; confidence=0.96 -->
**Proof.** Theorem 9.1.1 with the triangle inequality gives $\mathbb{E}\sup_{x\in T}\|Ax\|_2 \le \sqrt{m}\,\sup_{x\in T}\|x\|_2 + CK^2\gamma(T)$, i.e. in terms of radii $\mathbb{E}\,\mathrm{rad}(AT) \le \sqrt{m}\,\mathrm{rad}(T) + CK^2\gamma(T)$. Applying this to the difference set $T-T$ gives $\mathbb{E}\,\mathrm{diam}(AT) \le \sqrt{m}\,\mathrm{diam}(T) + CK^2 w(T)$, using (7.22) to pass from Gaussian complexity to Gaussian width. Dividing both sides by $\sqrt{n}$ finishes the proof. $\square$

<a id="pdf-681b6f3d947f-p247-b005"></a>
<!-- pdf-source: page=247; block=5; confidence=0.92 -->
Proposition 9.2.1 is sharper than the older projection bounds (Exercise 7.7.3): the diameter scales by the exact factor $\sqrt{m/n}$ with no absolute constant in front.

<a id="pdf-681b6f3d947f-p248-b001"></a>
<!-- pdf-source: page=248; block=1; confidence=0.96 -->
**Exercise 9.2.2 (Sizes of projections: high-probability bounds).** Using the high-probability matrix deviation inequality (Exercise 9.1.8), show that for $\varepsilon>0$,
$$\mathrm{diam}(PT) \le (1+\varepsilon)\sqrt{\tfrac{m}{n}}\,\mathrm{diam}(T) + CK^2 w_s(T)$$
holds with probability at least $1-\exp(-c\varepsilon^2 m/K^4)$.

<a id="pdf-681b6f3d947f-p248-b002"></a>
<!-- pdf-source: page=248; block=2; confidence=0.95 -->
**Exercise 9.2.3.** Deduce a version of Proposition 9.2.1 for the original model of $P$ from Section 7.7, i.e. a random projection onto a random $m$-dimensional subspace $E\sim\mathrm{Unif}(G_{n,m})$. Hint: for $m\ll n$, the matrix $A$ in the matrix deviation inequality is an approximate projection (Section 4.6).

<a id="pdf-681b6f3d947f-p248-b003"></a>
<!-- pdf-source: page=248; block=3; confidence=0.99 -->
**9.2.3 Covariance estimation for lower-dimensional distributions**

<a id="pdf-681b6f3d947f-p248-b004"></a>
<!-- pdf-source: page=248; block=4; confidence=0.93 -->
Revisiting covariance estimation (Sections 4.7, 5.6): $\Sigma$ of an $n$-dimensional distribution needs $m=O(n)$ samples in the sub-gaussian case and $m=O(n\log n)$ in general. When the distribution is approximately low-dimensional, i.e. $\Sigma^{1/2}$ has low stable rank $r$, one expects $m=O(r)$ to suffice. Remark 5.6.3 noted this for the general case up to logarithmic oversampling; the following result handles the sub-gaussian case with no logarithmic oversampling, extending Theorem 4.7.1.

<a id="pdf-681b6f3d947f-p248-b005"></a>
<!-- pdf-source: page=248; block=5; confidence=0.97 -->
**Theorem 9.2.4 (Covariance estimation for lower-dimensional distributions).** Let $X$ be a sub-gaussian random vector in $\mathbb{R}^n$: assume there is $K\ge 1$ with $\|\langle X,x\rangle\|_{\psi_2} \le K\|\langle X,x\rangle\|_{L^2}$ for all $x\in\mathbb{R}^n$. Then for every positive integer $m$,
$$\mathbb{E}\|\Sigma_m - \Sigma\| \le CK^4\left(\sqrt{\tfrac{r}{m}} + \tfrac{r}{m}\right)\|\Sigma\|,$$
where $r = \mathrm{tr}(\Sigma)/\|\Sigma\|$ is the stable rank of $\Sigma^{1/2}$.

<a id="pdf-681b6f3d947f-p249-b001"></a>
<!-- pdf-source: page=249; block=1; confidence=0.95 -->
**Proof.** As in Theorem 4.7.1, bring the distribution to isotropic position: $\|\Sigma_m-\Sigma\| = \|\Sigma^{1/2}R_m\Sigma^{1/2}\|$ where $R_m = \tfrac{1}{m}\sum_{i=1}^m Z_iZ_i^T - I_n$. Since the matrix is symmetric PSD, this equals $\max_{x\in S^{n-1}}\langle\Sigma^{1/2}R_m\Sigma^{1/2}x,x\rangle = \max_{x\in T}\langle R_m x,x\rangle$ with the ellipsoid $T:=\Sigma^{1/2}S^{n-1}$, which by definition of $R_m$ equals $\max_{x\in T}\big|\tfrac{1}{m}\sum_{i=1}^m\langle Z_i,x\rangle^2 - \|x\|_2^2\big| = \tfrac{1}{m}\max_{x\in T}\big|\|Ax\|_2^2 - m\|x\|_2^2\big|$, where $A$ has rows $Z_i$. The $Z_i$ are mean-zero, isotropic, sub-gaussian with $\|Z_i\|_{\psi_2}\lesssim 1$ (hiding $K$). Matrix deviation inequality (Exercise 9.1.10) gives $\mathbb{E}\|\Sigma_m-\Sigma\| \lesssim \tfrac{1}{m}\big(\gamma(T)^2 + \sqrt{m}\,\mathrm{rad}(T)\gamma(T)\big)$. For the ellipsoid, $\mathrm{rad}(T)=\|\Sigma\|^{1/2}$ and $\gamma(T)\le(\mathrm{tr}\,\Sigma)^{1/2}$, so $\mathbb{E}\|\Sigma_m-\Sigma\| \lesssim \tfrac{1}{m}\big(\mathrm{tr}\,\Sigma + \sqrt{m\|\Sigma\|\,\mathrm{tr}\,\Sigma}\big)$. Substituting $\mathrm{tr}(\Sigma)=r\|\Sigma\|$ and simplifying completes the proof. $\square$

<a id="pdf-681b6f3d947f-p249-b002"></a>
<!-- pdf-source: page=249; block=2; confidence=0.96 -->
**Exercise 9.2.5 (Tail bound).** Prove a high-probability version of Theorem 9.2.4 (cf. Exercises 4.7.3, 5.6.4): for any $u\ge 0$,
$$\|\Sigma_m-\Sigma\| \le CK^4\left(\sqrt{\tfrac{r+u}{m}} + \tfrac{r+u}{m}\right)\|\Sigma\|$$
with probability at least $1-2e^{-u}$.

<a id="pdf-681b6f3d947f-p249-b003"></a>
<!-- pdf-source: page=249; block=3; confidence=0.99 -->
**9.3 Johnson-Lindenstrauss Lemma for infinite sets**

<a id="pdf-681b6f3d947f-p249-b004"></a>
<!-- pdf-source: page=249; block=4; confidence=0.94 -->
Applying the matrix deviation inequality to a finite set $T$ recovers the Johnson-Lindenstrauss Lemma of Section 5.3, and more.

<a id="pdf-681b6f3d947f-p250-b001"></a>
<!-- pdf-source: page=250; block=1; confidence=0.98 -->
**Section 9.3.1 — Recovering the classical Johnson-Lindenstrauss.** Shows the matrix deviation inequality implies the classical JL Lemma (Theorem 5.3.1).

<a id="pdf-681b6f3d947f-p250-b002"></a>
<!-- pdf-source: page=250; block=2; confidence=0.95 -->
Let $X$ be $N$ points in $\mathbb{R}^n$ and set $T := \{(x-y)/\lVert x-y\rVert_2 : x,y\in X \text{ distinct}\}$. Its Gaussian complexity satisfies $\gamma(T)\le C\sqrt{\log N}$ (9.13) (Exercise 7.5.10). Matrix deviation inequality (Theorem 9.1.1) then gives, with high probability, $\sup_{x,y\in X}\big|\tfrac{\lVert Ax-Ay\rVert_2}{\lVert x-y\rVert_2}-\sqrt{m}\big|\lesssim\sqrt{\log N}$ (9.14). Multiplying (9.14) by $\tfrac{1}{\sqrt m}\lVert x-y\rVert_2$ and rearranging shows the scaled matrix $Q:=\tfrac{1}{\sqrt m}A$ is an approximate isometry on $X$: $(1-\varepsilon)\lVert x-y\rVert_2\le\lVert Qx-Qy\rVert_2\le(1+\varepsilon)\lVert x-y\rVert_2$ for all $x,y\in X$, with $\varepsilon\lesssim\sqrt{\tfrac{\log N}{m}}$. Fixing $\varepsilon>0$ and choosing $m\gtrsim\varepsilon^{-2}\log N$ makes $Q$ an $\varepsilon$-isometry w.h.p., recovering Theorem 5.3.1. Probability $0.99$ obtained via Markov's inequality; dependence on the sub-gaussian norm $K$ suppressed.

<a id="pdf-681b6f3d947f-p250-b003"></a>
<!-- pdf-source: page=250; block=3; confidence=0.97 -->
**Exercise 9.3.1.** Quantify the success probability and $K$-dependence in the above argument; i.e. use the matrix deviation inequality to give an alternative solution to Exercise 5.3.3.

<a id="pdf-681b6f3d947f-p250-b004"></a>
<!-- pdf-source: page=250; block=4; confidence=0.96 -->
**Section 9.3.2 — Johnson-Lindenstrauss lemma for infinite sets.** The previous argument only used finiteness of $X$ to bound the Gaussian complexity in (9.13), so a version of JL holds for general (not necessarily finite) sets.

<a id="pdf-681b6f3d947f-p251-b001"></a>
<!-- pdf-source: page=251; block=1; confidence=0.97 -->
**Proposition 9.3.2 (Additive Johnson-Lindenstrauss Lemma).** Let $X\subset\mathbb{R}^n$ and let $A$ be an $m\times n$ matrix whose rows $A_i$ are independent, isotropic, sub-gaussian random vectors in $\mathbb{R}^n$. Then with high probability (say $0.99$) the scaled matrix $Q:=\tfrac{1}{\sqrt m}A$ satisfies $\lVert x-y\rVert_2-\delta\le\lVert Qx-Qy\rVert_2\le\lVert x-y\rVert_2+\delta$ for all $x,y\in X$, where $\delta=\tfrac{CK^2 w(X)}{\sqrt m}$ and $K=\max_i\lVert A_i\rVert_{\psi_2}$.

<a id="pdf-681b6f3d947f-p251-b002"></a>
<!-- pdf-source: page=251; block=2; confidence=0.96 -->
**Proof.** Take $T=X-X$ (the difference set) and apply matrix deviation inequality (Theorem 9.1.1): with high probability $\sup_{x,y\in X}\big|\lVert Ax-Ay\rVert_2-\sqrt m\,\lVert x-y\rVert_2\big|\le CK^2\gamma(X-X)=2CK^2 w(X)$, using (7.22) in the last step. Dividing both sides by $\sqrt m$ completes the proof. $\square$

<a id="pdf-681b6f3d947f-p251-b003"></a>
<!-- pdf-source: page=251; block=3; confidence=0.95 -->
The error $\delta$ here is additive, unlike the multiplicative error of the finite-set JL Lemma (Theorem 5.3.1); this difference is in general necessary. **Exercise 9.3.3 (Additive error).** If $X$ has non-empty interior, show the classical JL conclusion (5.10) forces $m\ge n$, i.e. no dimension reduction is possible.

<a id="pdf-681b6f3d947f-p251-b004"></a>
<!-- pdf-source: page=251; block=4; confidence=0.93 -->
**Remark 9.3.4 (Stable dimension).** The additive JL Lemma can be phrased via the stable dimension $d(X)\asymp\dfrac{w(X)^2}{\operatorname{diam}(X)^2}$ (Section 7.6). Fixing $\varepsilon>0$ and choosing $m\ge(CK^4/\varepsilon^2)d(T)$ gives $\delta\le\varepsilon\operatorname{diam}(X)$ in Proposition 9.3.2, so $Q$ preserves distances in $X$ up to a small fraction of the diameter.

<a id="pdf-681b6f3d947f-p252-b001"></a>
<!-- pdf-source: page=252; block=1; confidence=0.95 -->
**Section 9.4 — Random sections: $M^*$ bound and Escape Theorem.** For $T\subset\mathbb{R}^n$ and a random subspace $E$ of given dimension, asks how large $T\cap E$ typically is. Two answers: a general bound on the expected diameter of $T\cap E$ (the $M^*$ bound, §9.4.1), and the Escape Theorem giving $T\cap E=\emptyset$ (§9.4.2). Both follow from the matrix deviation inequality.

<a id="pdf-681b6f3d947f-p252-b002"></a>
<!-- pdf-source: page=252; block=2; confidence=0.95 -->
**Section 9.4.1 — $M^*$ bound.** Realize the random subspace as $E:=\ker A$ for an $m\times n$ random matrix $A$. Always $\dim(E)\ge n-m$, and for continuous distributions $\dim(E)=n-m$ almost surely.

<a id="pdf-681b6f3d947f-p252-b003"></a>
<!-- pdf-source: page=252; block=3; confidence=0.95 -->
**Example 9.4.1.** If $A$ is Gaussian (independent $N(0,1)$ entries), rotation invariance makes $E=\ker(A)$ uniform on the Grassmannian: $E\sim\mathrm{Unif}(G_{n,\,n-m})$.

<a id="pdf-681b6f3d947f-p252-b004"></a>
<!-- pdf-source: page=252; block=4; confidence=0.97 -->
**Theorem 9.4.2 ($M^*$ bound).** Let $T\subset\mathbb{R}^n$ and let $A$ be an $m\times n$ matrix whose rows $A_i$ are independent, isotropic, sub-gaussian random vectors in $\mathbb{R}^n$. Then the random subspace $E=\ker A$ satisfies $\mathbb{E}\,\operatorname{diam}(T\cap E)\le\dfrac{CK^2 w(T)}{\sqrt m}$, where $K=\max_i\lVert A_i\rVert_{\psi_2}$.

<a id="pdf-681b6f3d947f-p253-b001"></a>
<!-- pdf-source: page=253; block=1; confidence=0.98 -->
## 9.4 Random sections: M* bound and Escape Theorem

<a id="pdf-681b6f3d947f-p253-b002"></a>
<!-- pdf-source: page=253; block=2; confidence=0.97 -->
**Proof.** Apply Theorem 9.1.1 to $T-T$: $\mathbb{E}\sup_{x,y\in T}\big|\,\|Ax-Ay\|_2 - \sqrt{m}\,\|x-y\|_2\,\big| \le CK^2\gamma(T-T) = 2CK^2 w(T)$. Restricting the supremum to $x,y\in T\cap\ker A$ makes $\|Ax-Ay\|_2=0$ (since $A(x-y)=0$), giving $\mathbb{E}\sup_{x,y\in T\cap\ker A}\sqrt{m}\,\|x-y\|_2 \le 2CK^2 w(T)$. Dividing by $\sqrt{m}$ yields $\mathbb{E}\,\mathrm{diam}(T\cap\ker A) \le CK^2 w(T)/\sqrt{m}$.

<a id="pdf-681b6f3d947f-p253-b003"></a>
<!-- pdf-source: page=253; block=3; confidence=0.96 -->
**Exercise 9.4.3 (Affine sections).** Verify the M* bound holds for all affine sections, not only sections through the origin: $\mathbb{E}\max_{z\in\mathbb{R}^n}\mathrm{diam}(T\cap E_z) \le CK^2 w(T)/\sqrt{m}$, where $E_z = z + \ker A$.

<a id="pdf-681b6f3d947f-p253-b004"></a>
<!-- pdf-source: page=253; block=4; confidence=0.95 -->
**Remark 9.4.4 (Stable dimension).** The random subspace $E$ has $\dim(E)\ge n-m$; with $m\ll n$ it has nearly full dimension. Using the stable dimension $d(T)\asymp w(T)^2/\mathrm{diam}(T)^2$ (Section 7.6): fixing $\varepsilon>0$, the M* bound reads $\mathbb{E}\,\mathrm{diam}(T\cap E)\le \varepsilon\cdot\mathrm{diam}(T)$ provided $m \ge C(K^4/\varepsilon^2)\,d(T)$ (9.15). The bound becomes nontrivial once the codimension of $E$ exceeds a multiple of the stable dimension. Equivalently, $\dim E$ plus a multiple of the stable dimension should be $\le n$. Example: if $T$ is a centered Euclidean ball in a subspace $F\subset\mathbb{R}^n$, then $\mathrm{diam}(T\cap E)<\mathrm{diam}(T)$ is possible only if $\dim E + \dim F \le n$.

<a id="pdf-681b6f3d947f-p254-b001"></a>
<!-- pdf-source: page=254; block=1; confidence=0.95 -->
**Example 9.4.5 (The $\ell_1$ ball).** Let $T=B_1^n$, the unit ball of the $\ell_1$ norm in $\mathbb{R}^n$. Since $w(T)\asymp\sqrt{\log n}$ (by (7.18)), the M* bound (Theorem 9.4.2) gives $\mathbb{E}\,\mathrm{diam}(T\cap E)\lesssim\sqrt{\log n/m}$; for $m=0.1n$, $\mathbb{E}\,\mathrm{diam}(T\cap E)\lesssim\sqrt{\log n/n}$ (9.16). Compared with $\mathrm{diam}(T)=2$, the diameter shrinks by almost $\sqrt{n}$ under intersection with $E$ of dimension $0.9n$. Intuition: the bulk of the octahedron $B_1^n$ is the inscribed ball $\tfrac{1}{\sqrt{n}}B_2^n$; a random subspace $E$ tends to pass through the bulk and miss the vertex outliers, so $\mathrm{diam}(T\cap E)\approx 1/\sqrt{n}$.

<a id="pdf-681b6f3d947f-p254-b002"></a>
<!-- pdf-source: page=254; block=2; confidence=0.96 -->
**Exercise 9.4.6 (M* bound with high probability).** Use the high-probability version of the matrix deviation inequality (Exercise 9.1.8) to derive a high-probability version of the M* bound.

<a id="pdf-681b6f3d947f-p254-b003"></a>
<!-- pdf-source: page=254; block=3; confidence=0.94 -->
### 9.4.2 Escape theorem

A random subspace $E$ may miss a set $T\subset\mathbb{R}^n$ entirely, e.g. when $T$ lies on the sphere; then $T\cap E$ is typically empty under essentially the same conditions as in the M* bound (Figure 9.3).

<a id="pdf-681b6f3d947f-p255-b001"></a>
<!-- pdf-source: page=255; block=1; confidence=0.97 -->
**Theorem 9.4.7 (Escape theorem).** Let $T\subset S^{n-1}$. Let $A$ be an $m\times n$ matrix whose rows $A_i$ are independent, isotropic, sub-gaussian random vectors in $\mathbb{R}^n$. If $m \ge CK^4 w(T)^2$ (9.17), then the random subspace $E=\ker A$ satisfies $T\cap E=\emptyset$ with probability at least $1-2\exp(-cm/K^4)$, where $K=\max_i\|A_i\|_{\psi_2}$.

<a id="pdf-681b6f3d947f-p255-b002"></a>
<!-- pdf-source: page=255; block=2; confidence=0.97 -->
**Proof.** By the high-probability matrix deviation inequality (Exercise 9.1.8), $\sup_{x\in T}\big|\,\|Ax\|_2 - \sqrt{m}\,\big| \le C_1 K^2(w(T)+u)$ (9.18) holds with probability at least $1-2\exp(-u^2)$. Assume this event and that $T\cap E\ne\emptyset$. For $x\in T\cap E$, $\|Ax\|_2=0$, so $\sqrt{m}\le C_1 K^2(w(T)+u)$. Choosing $u=\sqrt{m}/(2C_1K^2)$ gives $\sqrt{m}\le C_1 K^2 w(T)+\sqrt{m}/2$, hence $\sqrt{m}\le 2C_1 K^2 w(T)$. This contradicts (9.17) for $C$ large enough, so the event forces $T\cap E=\emptyset$.

<a id="pdf-681b6f3d947f-p255-b003"></a>
<!-- pdf-source: page=255; block=3; confidence=0.96 -->
**Exercise 9.4.8 (Sharpness).** Discuss the sharpness of the Escape theorem when $T$ is the unit sphere of some subspace of $\mathbb{R}^n$.

<a id="pdf-681b6f3d947f-p255-b004"></a>
<!-- pdf-source: page=255; block=4; confidence=0.96 -->
**Exercise 9.4.9 (Escape from a point set).** Prove a version of the Escape theorem using a rotation of a point set instead of a random subspace: given $T\subset S^{n-1}$ and a set $X$ of $N$ points in $\mathbb{R}^n$, if $\sigma_{n-1}(T) < 1/N$ then there exists a rotation $U\in O(n)$ with $T\cap UX=\emptyset$. Here $\sigma_{n-1}$ is the normalized Lebesgue (area) measure on $S^{n-1}$. Hint: take $U\in\mathrm{Unif}(SO(n))$ (Section 5.2.5) and apply a union bound to show $\mathbb{P}(\exists x\in X:\ Ux\in T)<1$.

<a id="pdf-681b6f3d947f-p256-b001"></a>
<!-- pdf-source: page=256; block=1; confidence=0.98 -->
## 9.5 Notes

<a id="pdf-681b6f3d947f-p256-b002"></a>
<!-- pdf-source: page=256; block=2; confidence=0.93 -->
Matrix deviation inequality (Theorem 9.1.1) and its proof are from [132]. For Gaussian $A$ with $T$ a subset of the unit sphere, it follows from Gaussian comparison: the upper bound on $\|Gx\|_2$ from Sudakov–Fernique's inequality (Theorem 7.2.11), the lower bound from Gordon's inequality (Exercise 7.2.14). Schechtman [181] proved a version for Gaussian $A$ and general (not necessarily Euclidean) norms, presented in Section 11.1. Earlier sub-gaussian versions appear in [117, 145, 63]; a sparse-matrix variant (for the sparse Johnson–Lindenstrauss transform) is in [31].

<a id="pdf-681b6f3d947f-p256-b003"></a>
<!-- pdf-source: page=256; block=3; confidence=0.95 -->
The quadratic dependence on $K$ in Theorem 9.1.1 was improved to $K\sqrt{\log K}$ in [109], which is optimal. This improves the subgaussian-norm dependence in all consequences of Theorem 9.1.1, including Theorems 3.1.1, 4.6.1, Proposition 9.2.1, Theorems 5.3.1, 9.4.2, 9.4.7, 10.2.1, and Corollary 10.3.4.

<a id="pdf-681b6f3d947f-p256-b004"></a>
<!-- pdf-source: page=256; block=4; confidence=0.94 -->
A version of Proposition 9.2.1 is due to V. Milman [149] (see [11, Prop. 5.7.1]). Theorem 9.2.4 (covariance estimation for lower-dimensional distributions) is due to Koltchinskii and Lounici [119], via the majorizing measure theorem; van Handel [213] derives the Gaussian case from decoupling, conditioning, and Slepian's lemma. The bound in Theorem 9.2.4 can be reversed [119, 213].

<a id="pdf-681b6f3d947f-p256-b005"></a>
<!-- pdf-source: page=256; block=5; confidence=0.92 -->
The infinite-set Johnson–Lindenstrauss lemma (Proposition 9.3.2) is from [132]. The $M^*$ bound (Section 9.4.1); the version given, Theorem 9.4.2, is from [132] (see [11, §7.3–7.4, 9.3], [87, 144, 223] for variants). The escape theorem (Section 9.4.2, "escape from the mesh") was originally proved by Gordon [87] for Gaussian $A$ with a sharp constant in (9.17), via Gordon's inequality (Exercise 7.2.14). Matching lower bounds are known for spherically convex sets [190, 9], where the exact hitting probability follows from integral geometry [9]. Oymak and Tropp [163] proved the sharp result is universal (extends to non-Gaussian matrices). The book's Theorem 9.4.7 holds for a more general class of random matrices but without sharp constants, and is from [132].

<a id="pdf-681b6f3d947f-p257-b001"></a>
<!-- pdf-source: page=257; block=1; confidence=0.93 -->
(Continuing from [132].) As shown in Section 10.5.1, the escape theorem is an important tool for signal recovery problems.

<a id="pdf-681b6f3d947f-p258-b001"></a>
<!-- pdf-source: page=258; block=1; confidence=0.97 -->
# 10 Sparse Recovery

<a id="pdf-681b6f3d947f-p258-b002"></a>
<!-- pdf-source: page=258; block=2; confidence=0.92 -->
Applications of high-dimensional probability to data science: signal recovery in compressed sensing and structured regression via convex optimization. A general approach based on the $M^*$ bound (Section 10.2) is specialized to sparse recovery (Section 10.3) and low-rank matrix recovery (Section 10.4). Using the escape theorem instead of the $M^*$ bound yields exact (error-free) sparse recovery (Section 10.5), which also introduces the restricted isometry property as a deterministic sufficient condition. Section 10.6 analyzes Lasso via the matrix deviation inequality.

<a id="pdf-681b6f3d947f-p258-b003"></a>
<!-- pdf-source: page=258; block=3; confidence=0.97 -->
## 10.1 High-dimensional signal recovery problems

<a id="pdf-681b6f3d947f-p258-b004"></a>
<!-- pdf-source: page=258; block=4; confidence=0.92 -->
**Model.** A signal is a vector $x \in \mathbb{R}^n$. Given $m$ random, linear, possibly noisy measurements represented as $y \in \mathbb{R}^m$:
$$y = Ax + w, \qquad (10.1)$$
where $A$ is a known $m \times n$ measurement matrix and $w \in \mathbb{R}^m$ is an unknown noise vector. The goal is to recover $x$ from $A$ and $y$. Equivalently, with $A_i \in \mathbb{R}^n$ the rows of $A$,
$$y_i = \langle A_i, x\rangle + w_i, \qquad i = 1, \dots, m. \qquad (10.2)$$
A probabilistic model is then assumed (statement truncated at the end of the page).

<a id="pdf-681b6f3d947f-p259-b001"></a>
<!-- pdf-source: page=259; block=1; confidence=0.95 -->
Continues §10.1. The measurement matrix $A$ in (10.1) is a realization of a random matrix; its rows $A_i$ are assumed independent random vectors, which makes the observations $y_i$ independent. Figure 10.1 illustrates recovering a signal $x$ from random linear measurements $y$.

<a id="pdf-681b6f3d947f-p259-b002"></a>
<!-- pdf-source: page=259; block=2; confidence=0.95 -->
**Example 10.1.1 (Audio sampling).** $x$ is a digitized audio signal; the measurement vector $y$ is obtained by sampling $x$ at $m$ randomly chosen time points (Figure 10.2).

<a id="pdf-681b6f3d947f-p259-b003"></a>
<!-- pdf-source: page=259; block=3; confidence=0.97 -->
**Example 10.1.2 (Linear regression).** Models the relationship between $n$ predictor variables and a response using $m$ observations, written $Y = X\beta + w$, where $X$ is an $m\times n$ matrix of sampled predictors, $Y\in\mathbb{R}^m$ the sampled responses, $\beta\in\mathbb{R}^n$ the coefficient vector to recover, and $w$ a noise vector.

<a id="pdf-681b6f3d947f-p260-b001"></a>
<!-- pdf-source: page=260; block=1; confidence=0.90 -->
Continues Example 10.1.2: genetics illustration where $X_{ij}$ is the expression of gene $j$ in patient $i$, $Y_i$ encodes patient $i$'s disease status, and the goal is to recover $\beta$ measuring each gene's effect.

<a id="pdf-681b6f3d947f-p260-b002"></a>
<!-- pdf-source: page=260; block=2; confidence=0.95 -->
**§10.1.1 Incorporating prior information about the signal.** Many recovery problems operate in the regime $m \ll n$ (far fewer measurements than unknowns; e.g. $\sim100$ patients vs. $\sim10{,}000$ genes). Here (10.1) is ill-posed even in the noiseless case $w=0$: solutions form a linear subspace of dimension at least $n-m$. Prior information is imposed as
$$x \in T \quad (10.3)$$
with $T\subset\mathbb{R}^n$ a known set; smaller $T$ requires fewer measurements $m$.

<a id="pdf-681b6f3d947f-p260-b003"></a>
<!-- pdf-source: page=260; block=3; confidence=0.95 -->
**§10.2 Signal recovery based on the $M^*$ bound.** Noiseless problem: $y = Ax$, $x\in T$, with $x\in\mathbb{R}^n$ unknown, $T\subset\mathbb{R}^n$ the known prior set, $A$ a known $m\times n$ random matrix. Candidate solution: any $x'$ consistent with measurements and prior,
$$\text{find } x' : \; y = Ax', \; x' \in T. \quad (10.4)$$
If $T$ is convex this is a convex feasibility program, numerically solvable.

<a id="pdf-681b6f3d947f-p261-b001"></a>
<!-- pdf-source: page=261; block=1; confidence=0.90 -->
States that the naïve program (10.4) works well, to be deduced from the $M^*$ bound of §9.4.1.

<a id="pdf-681b6f3d947f-p261-b002"></a>
<!-- pdf-source: page=261; block=2; confidence=0.97 -->
**Theorem 10.2.1.** If the rows $A_i$ of $A$ are independent, isotropic, sub-gaussian random vectors, then any solution $\hat{x}$ of program (10.4) satisfies
$$\mathbb{E}\,\|\hat{x} - x\|_2 \le \frac{C K^2 w(T)}{\sqrt{m}},$$
where $K = \max_i \|A_i\|_{\psi_2}$.

<a id="pdf-681b6f3d947f-p261-b003"></a>
<!-- pdf-source: page=261; block=3; confidence=0.97 -->
**Proof.** Since $x,\hat{x}\in T$ and $Ax = A\hat{x} = y$, both lie in $T\cap E_x$ with $E_x := x + \ker A$ (Figure 10.3). The affine version of the $M^*$ bound (Exercise 9.4.3) gives
$$\mathbb{E}\,\|\hat{x}-x\|_2 \le \mathbb{E}\,\operatorname{diam}(T\cap E_x) \le \frac{CK^2 w(T)}{\sqrt{m}}. \qquad\blacksquare$$

<a id="pdf-681b6f3d947f-p261-b004"></a>
<!-- pdf-source: page=261; block=4; confidence=0.95 -->
**Remark 10.2.2 (Stable dimension).** Arguing as in Remark 9.4.4, one gets the non-trivial bound
$$\mathbb{E}\,\|\hat{x}-x\|_2 \le \varepsilon\cdot\operatorname{diam}(T)$$
provided $m \ge C(K^4/\varepsilon^2)\,d(T)$, i.e. approximate recovery holds once $m$ exceeds a multiple of the stable dimension $d(T)$ of $T$. Since $d(T)$ can be much smaller than the ambient dimension $n$, recovery is possible in the ill-posed regime $m \ll n$.

<a id="pdf-681b6f3d947f-p262-b001"></a>
<!-- pdf-source: page=262; block=1; confidence=0.97 -->
**Remark 10.2.3 (Convexity).** A non-convex prior set $T$ can be replaced by its convex hull $\operatorname{conv}(T)$, making program (10.4) convex and tractable. Recovery guarantees of Theorem 10.2.1 are unchanged because $w(\operatorname{conv}(T)) = w(T)$ (Proposition 7.5.2).

<a id="pdf-681b6f3d947f-p262-b002"></a>
<!-- pdf-source: page=262; block=2; confidence=0.96 -->
**Exercise 10.2.4 (Noisy measurements).** Extend Theorem 10.2.1 to the noisy model $y = Ax + w$ of (10.1): show $\mathbb{E}\,\|\hat{x} - x\|_2 \le \dfrac{CK^2 w(T) + \|w\|_2}{\sqrt{m}}$. Hint: modify the argument giving the $M^*$ bound.

<a id="pdf-681b6f3d947f-p262-b003"></a>
<!-- pdf-source: page=262; block=3; confidence=0.95 -->
**Exercise 10.2.5 (Mean squared error).** Prove the Theorem 10.2.1 error bound extends to the mean squared error $\mathbb{E}\,\|\hat{x} - x\|_2^2$. Hint: modify the $M^*$ bound accordingly.

<a id="pdf-681b6f3d947f-p262-b004"></a>
<!-- pdf-source: page=262; block=4; confidence=0.96 -->
**Exercise 10.2.6 (Recovery by optimization).** Let $T$ be the unit ball of a norm $\|\cdot\|_T$ on $\mathbb{R}^n$. Show the conclusion of Theorem 10.2.1 holds for the solution of: minimize $\|x'\|_T$ subject to $y = Ax'$.

<a id="pdf-681b6f3d947f-p262-b005"></a>
<!-- pdf-source: page=262; block=5; confidence=0.95 -->
**10.3 Recovery of sparse signals — 10.3.1 Sparsity.** Motivating example of a prior set $T$: $x$ is expected sparse (most coefficients zero, exactly or approximately), e.g. few genes affecting a disease, or band-limited audio signals that are sparse in the frequency (Fourier) domain rather than time. Exact sparsity is measured by the support size $\|x\|_0 := |\operatorname{supp}(x)| = |\{i : x_i \neq 0\}|$.

<a id="pdf-681b6f3d947f-p263-b001"></a>
<!-- pdf-source: page=263; block=1; confidence=0.96 -->
Assume $\|x\|_0 = s \ll n$ (10.5). This is the special case of the general assumption (10.3) with $T = \{x \in \mathbb{R}^n : \|x\|_0 \le s\}$.

<a id="pdf-681b6f3d947f-p263-b002"></a>
<!-- pdf-source: page=263; block=2; confidence=0.95 -->
**Exercise 10.3.1 (Well posed).** Argue that if $A$ is in general position and $m \ge 2\|x\|_0$, the solution to the sparse recovery problem (10.1) is unique if it exists (choosing a suitable definition of general position).

<a id="pdf-681b6f3d947f-p263-b003"></a>
<!-- pdf-source: page=263; block=3; confidence=0.93 -->
Even when well posed, (10.1) may be computationally hard: it is easy given the support of $x$, but the support is usually unknown, and exhaustive search over supports of size $s$ is infeasible since $\binom{n}{s} \ge 2^s$. Effective approaches for the general constraint (10.3) and for sparse recovery follow.

<a id="pdf-681b6f3d947f-p263-b004"></a>
<!-- pdf-source: page=263; block=4; confidence=0.95 -->
**Exercise 10.3.2.** (a) $\|\cdot\|_0$ is not a norm on $\mathbb{R}^n$. (b) $\|\cdot\|_p$ is not a norm on $\mathbb{R}^n$ for $0 < p < 1$ (unit balls illustrated in Figure 10.4). (c) For every $x \in \mathbb{R}^n$, $\|x\|_0 = \lim_{p \to 0+} \|x\|_p^p$.

<a id="pdf-681b6f3d947f-p263-b005"></a>
<!-- pdf-source: page=263; block=5; confidence=0.90 -->
**10.3.2 Convexifying the sparsity by the $\ell_1$ norm, and recovery guarantees.** Specialize the general guarantees of Section 10.2 to sparse recovery by choosing a sparsity-promoting prior $T$; the choice $T := \{x \in \mathbb{R}^n : \|x\|_0 \le s\}$ is not tractable.

<a id="pdf-681b6f3d947f-p264-b001"></a>
<!-- pdf-source: page=264; block=1; confidence=0.95 -->
To make $T$ convex, replace the $\ell_0$ "norm" by the $\ell_p$ norm with the smallest exponent $p>0$ that is a true norm, namely $p=1$. Choose $T$ to be the scaled $\ell_1$ ball $T := \sqrt{s}\,B_1^n$; the factor $\sqrt{s}$ makes $T$ accommodate all $s$-sparse unit vectors.

<a id="pdf-681b6f3d947f-p264-b002"></a>
<!-- pdf-source: page=264; block=2; confidence=0.96 -->
**Exercise 10.3.3.** Check that $\{x \in \mathbb{R}^n : \|x\|_0 \le s,\ \|x\|_2 \le 1\} \subset \sqrt{s}\,B_1^n$.

<a id="pdf-681b6f3d947f-p264-b003"></a>
<!-- pdf-source: page=264; block=3; confidence=0.96 -->
For $T = \sqrt{s}\,B_1^n$, the general recovery program (10.4) becomes: find $x'$ with $y = Ax'$ and $\|x'\|_1 \le \sqrt{s}$ (10.6). This is convex and computationally tractable.

<a id="pdf-681b6f3d947f-p264-b004"></a>
<!-- pdf-source: page=264; block=4; confidence=0.97 -->
**Corollary 10.3.4 (Sparse recovery guarantees).** If the unknown $s$-sparse signal $x \in \mathbb{R}^n$ satisfies $\|x\|_2 \le 1$, it is approximately recovered from the random measurement $y = Ax$ by a solution $\hat{x}$ of (10.6), with error $\mathbb{E}\,\|\hat{x} - x\|_2 \le CK^2 \sqrt{\dfrac{s \log n}{m}}$.

<a id="pdf-681b6f3d947f-p264-b005"></a>
<!-- pdf-source: page=264; block=5; confidence=0.96 -->
**Proof.** Set $T = \sqrt{s}\,B_1^n$. Apply Theorem 10.2.1 together with the Gaussian width bound (7.18): $w(T) = \sqrt{s}\,w(B_1^n) \le C\sqrt{s \log n}$. $\blacksquare$

<a id="pdf-681b6f3d947f-p264-b006"></a>
<!-- pdf-source: page=264; block=6; confidence=0.95 -->
**Remark 10.3.5.** The error is small when $m \gtrsim s \log n$ (with a suitably large constant): the number of measurements is nearly linear in the sparsity $s$ with only logarithmic dependence on the ambient dimension $n$. Thus sparse recovery succeeds in the high-dimensional regime $m \ll n$.

<a id="pdf-681b6f3d947f-p264-b007"></a>
<!-- pdf-source: page=264; block=7; confidence=0.90 -->
**Exercise 10.3.6 (Sparse recovery by convex optimization).** [Statement truncated in the source.]

<a id="pdf-681b6f3d947f-p265-b001"></a>
<!-- pdf-source: page=265; block=1; confidence=0.90 -->
# 10.3 Recovery of sparse signals

<a id="pdf-681b6f3d947f-p265-b002"></a>
<!-- pdf-source: page=265; block=2; confidence=0.90 -->
**Exercise (a).** Show an unknown $s$-sparse signal $x$ (no norm restriction) is approximately recovered by the convex program
$$\text{minimize } \|x'\|_1 \text{ s.t. } y = Ax'. \tag{10.7}$$
The recovery error satisfies $\mathbb{E}\,\|\widehat{x}-x\|_2 \le C K^2 \sqrt{\tfrac{s\log n}{m}}\,\|x\|_2$.

**(b)** Argue an analogous result holds for approximately sparse signals; state and prove such a guarantee.

<a id="pdf-681b6f3d947f-p265-b003"></a>
<!-- pdf-source: page=265; block=3; confidence=0.92 -->
**Subsection 10.3.3 (convex hull of sparse vectors, logarithmic improvement).** Motivation: the replacement of $s$-sparse vectors by the octahedron $\sqrt{s}\,B_1^n$ (Exercise 10.3.3) is nearly sharp; the convex hull of sparse vectors is approximately a truncated $\ell_1$ ball.

**Definitions.** Set of sparse vectors
$$S_{n,s} := \{x\in\mathbb{R}^n : \|x\|_0 \le s,\ \|x\|_2 \le 1\},$$
and truncated $\ell_1$ ball
$$T_{n,s} := \sqrt{s}\,B_1^n \cap B_2^n = \{x\in\mathbb{R}^n : \|x\|_1 \le \sqrt{s},\ \|x\|_2 \le 1\}.$$

<a id="pdf-681b6f3d947f-p265-b004"></a>
<!-- pdf-source: page=265; block=4; confidence=0.90 -->
**Exercise 10.3.7 (convex hull of sparse vectors).**

**(a)** Check $\operatorname{conv}(S_{n,s}) \subset T_{n,s}$.

**(b)** For $x\in T_{n,s}$, partition the support into disjoint $I_1, I_2,\dots$ where $I_1$ indexes the $s$ largest coefficients in magnitude, $I_2$ the next $s$, etc. Show $\sum_{i\ge 1}\|x_{I_i}\|_2 \le 2$, where $x_I$ is the restriction of $x$ to $I$. *Hint:* $\|x_{I_1}\|_2\le 1$; for $i\ge 2$ each coordinate of $x_{I_i}$ is below the average coordinate of $x_{I_{i-1}}$, giving $\|x_{I_i}\|_2 \le (1/\sqrt{s})\|x_{I_{i-1}}\|_1$; sum the bounds.

**(c)** Deduce from (b) that $T_{n,s} \subset 2\,\operatorname{conv}(S_{n,s})$.

<a id="pdf-681b6f3d947f-p265-b005"></a>
<!-- pdf-source: page=265; block=5; confidence=0.92 -->
**Exercise 10.3.8 (Gaussian width of the set of sparse vectors).** Using Exercise 10.3.7, show
$$w(T_{n,s}) \le 2\,w(S_{n,s}) \le C\sqrt{s\log(en/s)}.$$

<a id="pdf-681b6f3d947f-p266-b001"></a>
<!-- pdf-source: page=266; block=1; confidence=0.88 -->
**Exercise 10.3.8 (continued).** Improve the logarithmic factor in the sparse-recovery error bound of Corollary 10.3.4 to
$$\mathbb{E}\,\|\widehat{x}-x\|_2 \le C\sqrt{\tfrac{s\log(en/s)}{m}}.$$
This shows $m \gtrsim s\log(en/s)$ measurements suffice for sparse recovery.

<a id="pdf-681b6f3d947f-p266-b002"></a>
<!-- pdf-source: page=266; block=2; confidence=0.90 -->
**Exercise 10.3.9 (Sharpness).** Show
$$w(T_{n,s}) \ge w(S_{n,s}) \ge c\sqrt{s\log(2n/s)}.$$
*Hint:* construct a large $\varepsilon$-separated subset of $S_{n,s}$ to lower-bound its covering numbers, then apply Sudakov's minoration inequality (Theorem 7.4.1).

<a id="pdf-681b6f3d947f-p266-b003"></a>
<!-- pdf-source: page=266; block=3; confidence=0.88 -->
**Exercise 10.3.10 (Garnaev–Gluskin's theorem).** Improve the logarithmic factor in bound (9.4.5) on sections of the $\ell_1$ ball: show
$$\mathbb{E}\,\operatorname{diam}(B_1^n \cap E) \lesssim \sqrt{\tfrac{\log(en/m)}{m}},$$
so the logarithmic factor in (9.16) is unnecessary. *Hint:* fix $\rho>0$, apply the $M^*$ bound to the truncated octahedron $T_\rho := B_1^n \cap \rho B_2^n$, bound $w(T_\rho)$ via Exercise 10.3.8, note $\operatorname{rad}(T_\rho\cap E)\le\delta$ (for $\delta\le\rho$) implies $\operatorname{rad}(T\cap E)\le\delta$, then optimize in $\rho$.

<a id="pdf-681b6f3d947f-p266-b004"></a>
<!-- pdf-source: page=266; block=4; confidence=0.90 -->
# 10.4 Low-rank matrix recovery

Matrix analog of sparse recovery: the unknown signal is a $d\times d$ matrix $X$ instead of $x\in\mathbb{R}^n$. Two notions of matrix sparsity: (i) few nonzero entries, measured by $\|X\|_0$ — handled by vectorizing $X$ into $\mathbb{R}^{d^2}$ and applying Section 10.3; (ii) low rank, treated here. Rank is the $\ell_0$ norm of the singular-value vector
$$s(X) := (s_i(X))_{i=1}^d. \tag{10.8}$$
Recover unknown $d\times d$ matrix from $m$ random measurements
$$y_i = \langle A_i, X\rangle, \quad i=1,\dots,m. \tag{10.9}$$

<a id="pdf-681b6f3d947f-p267-b001"></a>
<!-- pdf-source: page=267; block=1; confidence=0.90 -->
The $A_i$ are independent $d\times d$ matrices and $\langle A_i, X\rangle = \operatorname{tr}(A_i^{\mathsf T} X)$ is the canonical matrix inner product. For $d=1$, (10.9) reduces to vector recovery (10.2). With $m$ linear equations in $d\times d$ variables, the problem is ill-posed when $m < d^2$; to solve it in this range assume low rank $\operatorname{rank}(X) \le r \ll d$.

<a id="pdf-681b6f3d947f-p267-b002"></a>
<!-- pdf-source: page=267; block=2; confidence=0.90 -->
**Definition (10.4.1, nuclear/trace norm).** Since rank is non-convex (the $\ell_0$ norm of $s(X)$), replace $\ell_0$ by $\ell_1$ to obtain the nuclear (trace) norm
$$\|X\|_* := \|s(X)\|_1 = \sum_{i=1}^d s_i(X) = \operatorname{tr}\!\big(\sqrt{X^{\mathsf T}X}\big).$$

<a id="pdf-681b6f3d947f-p267-b003"></a>
<!-- pdf-source: page=267; block=3; confidence=0.90 -->
**Exercise 10.4.1.** Prove $\|\cdot\|_*$ is a norm on $d\times d$ matrices. *Hint:* it follows from the identity $\|X\|_* = \max\{|\langle X, U\rangle| : U \in O(d)\}$, where $O(d)$ is the set of $d\times d$ orthogonal matrices; prove the identity via the SVD of $X$.

<a id="pdf-681b6f3d947f-p267-b004"></a>
<!-- pdf-source: page=267; block=4; confidence=0.90 -->
**Exercise 10.4.2 (nuclear, Frobenius and operator norms).** Check
$$\langle X, Y\rangle \le \|X\|_* \cdot \|Y\|, \tag{10.10}$$
and conclude $\|X\|_F^2 \le \|X\|_* \cdot \|X\|$. *Hint:* view $\|\cdot\|_*$, $\|\cdot\|_F$, $\|\cdot\|$ as matrix analogs of the vector $\ell_1$, $\ell_2$, $\ell_\infty$ norms.

<a id="pdf-681b6f3d947f-p267-b005"></a>
<!-- pdf-source: page=267; block=5; confidence=0.90 -->
**Definition.** Nuclear-norm unit ball $B_* := \{X\in\mathbb{R}^{d\times d} : \|X\|_* \le 1\}$.

**Exercise 10.4.3 (Gaussian width of $B_*$).** Show $w(B_*) \le 2\sqrt{d}$. *Hint:* use (10.10) followed by Theorem 7.3.1.

<a id="pdf-681b6f3d947f-p268-b001"></a>
<!-- pdf-source: page=268; block=1; confidence=0.90 -->
**Exercise 10.4.4.** (Matrix version of Exercise 10.3.3.) Verify the inclusion $\{X \in \mathbb{R}^{d\times d} : \operatorname{rank}(X) \le r,\ \|X\|_F \le 1\} \subset \sqrt{r}\, B_*$, where $B_*$ is the nuclear-norm unit ball.

<a id="pdf-681b6f3d947f-p268-b002"></a>
<!-- pdf-source: page=268; block=2; confidence=0.98 -->
## 10.4.2 Guarantees for low-rank matrix recovery

<a id="pdf-681b6f3d947f-p268-b003"></a>
<!-- pdf-source: page=268; block=3; confidence=0.95 -->
Matrix version of convex program (10.6) for low-rank recovery problem (10.9):

$$\text{Find } X' :\ y_i = \langle A_i, X'\rangle\ \forall i=1,\dots,m;\quad \|X'\|_* \le \sqrt{r}. \tag{10.11}$$

<a id="pdf-681b6f3d947f-p268-b004"></a>
<!-- pdf-source: page=268; block=4; confidence=0.93 -->
**Exercise 10.4.5 (Low-rank matrix recovery: guarantees).** Let the random matrices $A_i$ be independent with all independent, sub-gaussian entries. Assume the unknown $d\times d$ matrix $X$ of rank $r$ satisfies $\|X\|_F \le 1$. Show that $X$ is approximately recovered from measurements $y_i$ by a solution $\widehat{X}$ of (10.11), with recovery error

$$\mathbb{E}\,\|\widehat{X} - X\|_F \le C K^2 \sqrt{\tfrac{rd}{m}}.$$

(A footnote notes the independence of entries can be relaxed.)

<a id="pdf-681b6f3d947f-p268-b005"></a>
<!-- pdf-source: page=268; block=5; confidence=0.95 -->
**Remark 10.4.6.** The recovery error is small when $m \gtrsim rd$ (with a large enough hidden constant), permitting recovery of low-rank matrices even when $m \ll d^2$, i.e. when the rank-free matrix recovery problem is ill-posed.

<a id="pdf-681b6f3d947f-p268-b006"></a>
<!-- pdf-source: page=268; block=6; confidence=0.95 -->
**Exercise 10.4.7.** Extend the matrix recovery result to approximately low-rank matrices.

<a id="pdf-681b6f3d947f-p268-b007"></a>
<!-- pdf-source: page=268; block=7; confidence=0.95 -->
**Exercise 10.4.8 (Low-rank matrix recovery by convex optimization).** Show that a rank-$r$ matrix $X$ is approximately recovered by solving

$$\text{minimize } \|X'\|_*\ \text{ s.t. } y_i = \langle A_i, X'\rangle\ \forall i=1,\dots,m.$$

<a id="pdf-681b6f3d947f-p268-b008"></a>
<!-- pdf-source: page=268; block=8; confidence=0.96 -->
**Exercise 10.4.9 (Rectangular matrices).** Extend the matrix recovery result from square to rectangular $d_1 \times d_2$ matrices.

<a id="pdf-681b6f3d947f-p269-b001"></a>
<!-- pdf-source: page=269; block=1; confidence=0.98 -->
# 10.5 Exact recovery and the restricted isometry property

<a id="pdf-681b6f3d947f-p269-b002"></a>
<!-- pdf-source: page=269; block=2; confidence=0.95 -->
The sparse recovery guarantees can be improved so the recovery error for sparse $x$ is exactly zero. Two approaches: (i) deduce exact recovery from Escape Theorem 9.4.7; (ii) a deterministic condition on $A$ guaranteeing exact recovery, the restricted isometry property (RIP), which random matrices satisfy.

<a id="pdf-681b6f3d947f-p269-b003"></a>
<!-- pdf-source: page=269; block=3; confidence=0.97 -->
## 10.5.1 Exact recovery based on the Escape Theorem

<a id="pdf-681b6f3d947f-p269-b004"></a>
<!-- pdf-source: page=269; block=4; confidence=0.92 -->
A solution $\widehat{x}$ of program (10.6) lies in the intersection of the prior set $T$ (here the $\ell_1$ ball $\sqrt{s}\,B_1^n$) with the affine subspace $E_x = x + \ker A$. The $\ell_1$ ball is a polytope and the $s$-sparse unit vector $x$ lies on its $(s-1)$-dimensional edge. If the random subspace $E_x$ is tangent to the ball at $x$, then $x$ is the unique intersection point and the solution is exact, $\widehat{x} = x$. Tangency holds iff the tangent cone $T(x)$ (rays from $x$ into the $\ell_1$ ball) meets $E_x$ only at $x$, equivalently iff the spherical part $S(x)$ of $T(x)$ is disjoint from $E_x$ — precisely the conclusion of Escape Theorem 9.4.7. (Figure 10.5.)

<a id="pdf-681b6f3d947f-p270-b001"></a>
<!-- pdf-source: page=270; block=1; confidence=0.95 -->
Noiseless sparse recovery problem $y = Ax$, solved via

$$\text{minimize } \|x'\|_1\ \text{ s.t. } y = Ax'. \tag{10.12}$$

<a id="pdf-681b6f3d947f-p270-b002"></a>
<!-- pdf-source: page=270; block=2; confidence=0.95 -->
**Theorem 10.5.1 (Exact sparse recovery).** Let the rows $A_i$ of $A$ be independent, isotropic, sub-gaussian random vectors, and $K := \max_i \|A_i\|_{\psi_2}$. With probability at least $1 - 2\exp(-cm/K^4)$ the following holds: if $x \in \mathbb{R}^n$ is $s$-sparse and $m \ge C K^4 s \log n$, then a solution $\widehat{x}$ of (10.12) is exact, $\widehat{x} = x$.

<a id="pdf-681b6f3d947f-p270-b003"></a>
<!-- pdf-source: page=270; block=3; confidence=0.93 -->
To prove the theorem, show the recovery error $h := \widehat{x} - x$ is zero. First establish that $h$ has more "energy" on the support of $x$ than outside it.

<a id="pdf-681b6f3d947f-p270-b004"></a>
<!-- pdf-source: page=270; block=4; confidence=0.96 -->
**Lemma 10.5.2.** Let $S := \operatorname{supp}(x)$. Then $\|h_{S^c}\|_1 \le \|h_S\|_1$, where $h_S \in \mathbb{R}^S$ is the restriction of $h \in \mathbb{R}^n$ to coordinates $S \subset \{1,\dots,n\}$.

<a id="pdf-681b6f3d947f-p270-b005"></a>
<!-- pdf-source: page=270; block=5; confidence=0.95 -->
**Proof.** Since $\widehat{x}$ minimizes (10.12), $\|\widehat{x}\|_1 \le \|x\|_1$ (10.13). Also, by the triangle inequality with $x_S = x$, $x_{S^c} = 0$,

$$\|\widehat{x}\|_1 = \|x+h\|_1 = \|x_S + h_S\|_1 + \|x_{S^c} + h_{S^c}\|_1 \ge \|x\|_1 - \|h_S\|_1 + \|h_{S^c}\|_1.$$

Substituting into (10.13) and cancelling $\|x\|_1$ gives $\|h_{S^c}\|_1 \le \|h_S\|_1$. $\blacksquare$

<a id="pdf-681b6f3d947f-p270-b006"></a>
<!-- pdf-source: page=270; block=6; confidence=0.96 -->
**Lemma 10.5.3.** The error vector satisfies $\|h\|_1 \le 2\sqrt{s}\,\|h\|_2$.

<a id="pdf-681b6f3d947f-p271-b001"></a>
<!-- pdf-source: page=271; block=1; confidence=0.90 -->
**Section 10.5. Exact recovery and the restricted isometry property.**

<a id="pdf-681b6f3d947f-p271-b002"></a>
<!-- pdf-source: page=271; block=2; confidence=0.85 -->
**Proof (of Lemma 10.5.3).** By Lemma 10.5.2 and Cauchy–Schwarz: $\|h\|_1 = \|h_S\|_1 + \|h_{S^c}\|_1 \le 2\|h_S\|_1 \le 2\sqrt{s}\,\|h_S\|_2$. Since $\|h_S\|_2 \le \|h\|_2$, the claim follows.

<a id="pdf-681b6f3d947f-p271-b003"></a>
<!-- pdf-source: page=271; block=3; confidence=0.92 -->
**Proof of Theorem 10.5.1.** Suppose recovery is not exact, so $h = \hat{x} - x \ne 0$. By Lemma 10.5.3 the normalized error lies in $T_s := \{ z \in S^{n-1} : \|z\|_1 \le 2\sqrt{s} \}$. Since $Ah = A\hat{x} - Ax = y - y = 0$, we get $h/\|h\|_2 \in T_s \cap \ker A$ (10.14). Escape Theorem 9.4.7 makes this intersection empty with high probability provided $m \ge C K^4 w(T_s)^2$. Now $w(T_s) \le 2\sqrt{s}\, w(B_1^n) \le C\sqrt{s \log n}$ (10.15), using bound (7.18) on the Gaussian width of the $\ell_1$ ball. Hence if $m \ge C K^4 s \log n$ the intersection in (10.14) is empty w.h.p., contradicting the inclusion; so $h \ne 0$ fails w.h.p.

<a id="pdf-681b6f3d947f-p271-b004"></a>
<!-- pdf-source: page=271; block=4; confidence=0.90 -->
**Exercise 10.5.4.** Show that Theorem 10.5.1 holds under the weaker measurement bound $m \ge C K^4 s \log(en/s)$. Hint: use Exercise 10.3.8.

<a id="pdf-681b6f3d947f-p271-b005"></a>
<!-- pdf-source: page=271; block=5; confidence=0.90 -->
**Exercise 10.5.5.** Give a geometric interpretation of the proof of Theorem 10.5.1 via Figure 10.5b; describe what it says about the tangent cone $T(x)$ and its spherical part $S(x)$.

<a id="pdf-681b6f3d947f-p271-b006"></a>
<!-- pdf-source: page=271; block=6; confidence=0.88 -->
**Exercise 10.5.6.** Extend the sparse recovery result (Theorem 10.5.1) to noisy measurements $y = Ax + w$, possibly modifying the recovery program by making the constraint $y = Ax'$ approximate.

<a id="pdf-681b6f3d947f-p272-b001"></a>
<!-- pdf-source: page=272; block=1; confidence=0.90 -->
**Remark 10.5.7.** Theorem 10.5.1 shows one can solve underdetermined linear systems $y = Ax$ with $m \ll n$ equations in $n$ variables when the solution is sparse.

<a id="pdf-681b6f3d947f-p272-b002"></a>
<!-- pdf-source: page=272; block=2; confidence=0.90 -->
**Section 10.5.2. Restricted isometries.** (Optional subsection.) Prior recovery results were probabilistic (random $A$, high probability); this asks for a deterministic condition guaranteeing a given $A$ enables sparse recovery — the restricted isometry property (RIP).

<a id="pdf-681b6f3d947f-p272-b003"></a>
<!-- pdf-source: page=272; block=3; confidence=0.93 -->
**Definition 10.5.8 (RIP).** An $m \times n$ matrix $A$ satisfies RIP with parameters $\alpha, \beta, s$ if $\alpha\|v\|_2 \le \|Av\|_2 \le \beta\|v\|_2$ for all $v \in \mathbb{R}^n$ with $\|v\|_0 \le s$. Equivalently, the restriction of $A$ to any $s$-dimensional coordinate subspace is an approximate isometry in the sense of (4.5). ($\|v\|_0$ is the number of nonzero coordinates.)

<a id="pdf-681b6f3d947f-p272-b004"></a>
<!-- pdf-source: page=272; block=4; confidence=0.90 -->
**Exercise 10.5.9.** Check that RIP holds iff the singular values satisfy $\alpha \le s_s(A_I) \le s_1(A_I) \le \beta$ for every $I \subset [n]$ with $|I| = s$, where $A_I$ is the $m \times s$ submatrix of $A$ formed from the columns indexed by $I$.

<a id="pdf-681b6f3d947f-p272-b005"></a>
<!-- pdf-source: page=272; block=5; confidence=0.93 -->
**Theorem 10.5.10 (RIP implies exact recovery).** If an $m \times n$ matrix $A$ satisfies RIP with parameters $\alpha, \beta$ and $(1+\lambda)s$, where $\lambda > (\beta/\alpha)^2$, then every $s$-sparse $x \in \mathbb{R}^n$ is recovered exactly by program (10.12): $\hat{x} = x$.

<a id="pdf-681b6f3d947f-p272-b006"></a>
<!-- pdf-source: page=272; block=6; confidence=0.90 -->
**Proof (Step 1: decomposing the support).** Goal: show the error $h = \hat{x} - x$ is zero, decomposing $h$ as in Exercise 10.3.7. Let $I_0$ be the support of $x$; let $I_1$ index the $\lambda s$ largest-magnitude coefficients of $h_{I_0^c}$, $I_2$ the next $\lambda s$ largest, and so on. Set $I_{0,1} = I_0 \cup I_1$.

<a id="pdf-681b6f3d947f-p273-b001"></a>
<!-- pdf-source: page=273; block=1; confidence=0.92 -->
**Proof (cont.).** Since $Ah = A\hat{x} - Ax = y - y = 0$, the triangle inequality gives $0 = \|Ah\|_2 \ge \|A_{I_{0,1}} h_{I_{0,1}}\|_2 - \|A_{I_{0,1}^c} h_{I_{0,1}^c}\|_2$ (10.16).

**Step 2 (applying RIP).** As $|I_{0,1}| \le s + \lambda s$, RIP gives $\|A_{I_{0,1}} h_{I_{0,1}}\|_2 \ge \alpha\|h_{I_{0,1}}\|_2$; triangle inequality plus RIP give $\|A_{I_{0,1}^c} h_{I_{0,1}^c}\|_2 \le \sum_{i\ge 2}\|A_{I_i} h_{I_i}\|_2 \le \beta\sum_{i\ge 2}\|h_{I_i}\|_2$. Substituting into (10.16): $\beta\sum_{i\ge 2}\|h_{I_i}\|_2 \ge \alpha\|h_{I_{0,1}}\|_2$ (10.17).

<a id="pdf-681b6f3d947f-p273-b002"></a>
<!-- pdf-source: page=273; block=2; confidence=0.92 -->
**Step 3 (summing up).** Each coefficient of $h_{I_i}$ is bounded by the average of $h_{I_{i-1}}$, i.e. $\|h_{I_{i-1}}\|_1/(\lambda s)$ for $i \ge 2$, so $\|h_{I_i}\|_2 \le \tfrac{1}{\sqrt{\lambda s}}\|h_{I_{i-1}}\|_1$. Summing, $\sum_{i\ge 2}\|h_{I_i}\|_2 \le \tfrac{1}{\sqrt{\lambda s}}\sum_{i\ge 1}\|h_{I_i}\|_1 = \tfrac{1}{\sqrt{\lambda s}}\|h_{I_0^c}\|_1 \le \tfrac{1}{\sqrt{\lambda s}}\|h_{I_0}\|_1$ (Lemma 10.5.2) $\le \tfrac{1}{\sqrt{\lambda}}\|h_{I_0}\|_2 \le \tfrac{1}{\sqrt{\lambda}}\|h_{I_{0,1}}\|_2$. Plugging into (10.17): $\tfrac{\beta}{\sqrt{\lambda}}\|h_{I_{0,1}}\|_2 \ge \alpha\|h_{I_{0,1}}\|_2$. Since $\beta/\sqrt{\lambda} < \alpha$ by hypothesis, $h_{I_{0,1}} = 0$. As $I_{0,1}$ contains the largest coefficient of $h$, it follows that $h = 0$. $\blacksquare$

<a id="pdf-681b6f3d947f-p273-b003"></a>
<!-- pdf-source: page=273; block=3; confidence=0.90 -->
It is unknown how to deterministically construct matrices $A$ with good RIP parameters (i.e. $\beta = O(\alpha)$ and $s$ as large as $m$ up to log factors), but random matrices $A$ satisfy RIP with high probability.

<a id="pdf-681b6f3d947f-p274-b001"></a>
<!-- pdf-source: page=274; block=1; confidence=0.95 -->
**Theorem 10.5.11 (Random matrices satisfy RIP).** Let $A$ be an $m\times n$ matrix whose rows $A_i$ are independent, isotropic, sub-gaussian random vectors, and set $K := \max_i \lVert A_i\rVert_{\psi_2}$. If $m \ge CK^4 s \log(en/s)$, then with probability at least $1 - 2\exp(-cm/K^4)$, $A$ satisfies RIP with parameters $\alpha = 0.9\sqrt{m}$, $\beta = 1.1\sqrt{m}$ and $s$.

<a id="pdf-681b6f3d947f-p274-b002"></a>
<!-- pdf-source: page=274; block=2; confidence=0.80 -->
**Proof.** By Exercise 10.5.9 it suffices to control the singular values of all $m\times s$ submatrices $A_I$; do this via the two-sided bound of Theorem 4.6.1 plus a union bound. Fix $I$. Theorem 4.6.1 gives $\sqrt{m} - r \le s_s(A_I) \le s_1(A_I) \le \sqrt{m} + r$ with probability $\ge 1 - 2\exp(-t^2)$, where $r = C_0 K^2(\sqrt{s} + t)$. Setting $t = \sqrt{m}/(20 C_0 K^2)$ and using the hypothesis on $m$ with a large enough constant $C$ makes $r \le 0.1\sqrt{m}$, yielding
$$0.9\sqrt{m} \le s_s(A_I) \le s_1(A_I) \le 1.1\sqrt{m} \tag{10.18}$$
with probability $\ge 1 - 2\exp(-2cm^2/K^4)$ ($c>0$ absolute). Taking a union bound over the $\binom{n}{s}$ subsets $I \subset [n]$, (10.18) holds with probability $\ge 1 - 2\exp(-2cm^2/K^4)\binom{n}{s} > 1 - 2\exp(-cm^2/K^4)$, using $\binom{n}{s} \le \exp(s\log(en/s))$ (eq. (0.0.5)) and the assumption on $m$. $\square$

<a id="pdf-681b6f3d947f-p274-b003"></a>
<!-- pdf-source: page=274; block=3; confidence=0.92 -->
**Second proof of Theorem 10.5.1.** These results give another route to exact recovery. By Theorem 10.5.11, $A$ satisfies RIP with $\alpha = 0.9\sqrt{m}$, $\beta = 1.1\sqrt{m}$ and $3s$. Hence Theorem 10.5.10 with $\lambda = 2$ guarantees exact recovery, so Theorem 10.5.1 holds, including the logarithmic improvement of Exercise 10.5.4. $\square$

<a id="pdf-681b6f3d947f-p274-b004"></a>
<!-- pdf-source: page=274; block=4; confidence=0.95 -->
**Exercise 10.5.12 (RIP for random projections).** Let $P$ be the orthogonal projection in $\mathbb{R}^n$ onto an $m$-dimensional random subspace uniformly distributed in the Grassmannian $G_{n,m}$. (a) Prove $P$ satisfies RIP with good parameters (as in Theorem 10.5.11, up to normalization). (b) Deduce a version of Theorem 10.5.1 for exact recovery from random projections.

<a id="pdf-681b6f3d947f-p275-b001"></a>
<!-- pdf-source: page=275; block=1; confidence=0.95 -->
**§10.6 Lasso algorithm for sparse regression.** Introduces an alternative sparse-recovery method, developed in statistics for sparse linear regression, called Lasso ("least absolute shrinkage and selection operator").

<a id="pdf-681b6f3d947f-p275-b002"></a>
<!-- pdf-source: page=275; block=2; confidence=0.93 -->
**§10.6.1 Statistical formulation.** Classical linear regression: $Y = X\beta + w$ (10.19), with $X$ a known $m\times n$ predictor matrix, $Y\in\mathbb{R}^m$ the response sample, $\beta\in\mathbb{R}^n$ the unknown coefficient vector, $w$ noise. Ordinary least squares minimizes the $\ell_2$ error: minimize $\lVert Y - X\beta'\rVert_2$ s.t. $\beta'\in\mathbb{R}^n$ (10.20). Adding sparsity $\lVert\beta\rVert_0 \le s$ with $s \ll n$, and replacing the nonconvex $\ell_0$ by its convex proxy $\ell_1$, gives Lasso: minimize $\lVert Y - X\beta'\rVert_2$ s.t. $\lVert\beta'\rVert_1 \le R$ (10.21), where $R$ sets the desired sparsity level. This is a tractable convex program.

<a id="pdf-681b6f3d947f-p275-b003"></a>
<!-- pdf-source: page=275; block=3; confidence=0.90 -->
**§10.6.2 Mathematical formulation and guarantees.** Restate the regression problem (10.19) in sparse-recovery notation as $y = Ax + w$.

<a id="pdf-681b6f3d947f-p276-b001"></a>
<!-- pdf-source: page=276; block=1; confidence=0.93 -->
Here $A$ is a known $m\times n$ matrix, $y\in\mathbb{R}^m$ known, $x\in\mathbb{R}^n$ the unknown to recover, and $w\in\mathbb{R}^m$ noise (fixed or random and independent of $A$). Lasso (10.21) becomes: minimize $\lVert y - Ax'\rVert_2$ s.t. $\lVert x'\rVert_1 \le R$ (10.22).

<a id="pdf-681b6f3d947f-p276-b002"></a>
<!-- pdf-source: page=276; block=2; confidence=0.95 -->
**Theorem 10.6.1 (Performance of Lasso).** Suppose the rows $A_i$ of $A$ are independent, isotropic, sub-gaussian, with $K := \max_i \lVert A_i\rVert_{\psi_2}$. Then with probability $\ge 1 - 2\exp(-s\log n)$ the following holds: if the unknown signal $x\in\mathbb{R}^n$ is $s$-sparse and $m \ge CK^4 s \log n$ (10.23), then any solution $\widehat{x}$ of program (10.22) with $R := \lVert x\rVert_1$ satisfies
$$\lVert \widehat{x} - x\rVert_2 \le C\sigma \sqrt{\tfrac{s\log n}{m}},$$
where $\sigma = \lVert w\rVert_2/\sqrt{m}$.

<a id="pdf-681b6f3d947f-p276-b003"></a>
<!-- pdf-source: page=276; block=3; confidence=0.93 -->
**Remark 10.6.2 (Noise).** $\sigma^2$ is the average squared noise per measurement: $\sigma^2 = \lVert w\rVert_2^2/m = \tfrac{1}{m}\sum_{i=1}^m w_i^2$. When $m \gtrsim s\log n$, Theorem 10.6.1 bounds the recovery error by the average noise $\sigma$, and larger $m$ makes the error smaller.

<a id="pdf-681b6f3d947f-p276-b004"></a>
<!-- pdf-source: page=276; block=4; confidence=0.95 -->
**Remark 10.6.3 (Exact recovery).** In the noiseless model $y = Ax$ we have $w = 0$, so Lasso recovers $x$ exactly: $\widehat{x} = x$.

<a id="pdf-681b6f3d947f-p276-b005"></a>
<!-- pdf-source: page=276; block=5; confidence=0.90 -->
**Proof (strategy).** Similar to the exact-recovery proof of Theorem 10.5.1, but using the Matrix Deviation Inequality (Theorem 9.1.1) directly instead of the Escape theorem. Goal: bound the error vector $h := \widehat{x} - x$.

<a id="pdf-681b6f3d947f-p276-b006"></a>
<!-- pdf-source: page=276; block=6; confidence=0.95 -->
**Exercise 10.6.4.** Check that $h$ satisfies the conclusions of Lemmas 10.5.2 and 10.5.3, so that $\lVert h\rVert_1 \le 2\sqrt{s}\,\lVert h\rVert_2$ (10.24). Hint: the proofs rest on $\lVert\widehat{x}\rVert_1 \le \lVert x\rVert_1$, which holds here.

<a id="pdf-681b6f3d947f-p277-b001"></a>
<!-- pdf-source: page=277; block=1; confidence=0.95 -->
With nonzero noise `w`, one cannot expect `Ah = 0` as in Theorem 10.5.1; instead upper and lower bounds on `∥Ah∥₂` are derived.

<a id="pdf-681b6f3d947f-p277-b002"></a>
<!-- pdf-source: page=277; block=2; confidence=0.97 -->
**Lemma 10.6.5 (Upper bound on ∥Ah∥₂).** `∥Ah∥₂² ≤ 2⟨h, Aᵀw⟩`  (10.25).

<a id="pdf-681b6f3d947f-p277-b003"></a>
<!-- pdf-source: page=277; block=3; confidence=0.96 -->
**Proof.** Since `x̂` minimizes the Lasso program (10.22), `∥y − Ax̂∥₂ ≤ ∥y − Ax∥₂`. Using `y = Ax + w` and `h = x̂ − x`: `y − Ax̂ = w − Ah` and `y − Ax = w`, giving `∥w − Ah∥₂ ≤ ∥w∥₂`. Squaring yields `∥w∥₂² − 2⟨w, Ah⟩ + ∥Ah∥₂² ≤ ∥w∥₂²`; simplifying gives (10.25). ∎

<a id="pdf-681b6f3d947f-p277-b004"></a>
<!-- pdf-source: page=277; block=4; confidence=0.96 -->
**Lemma 10.6.6 (Lower bound on ∥Ah∥₂).** With probability at least `1 − 2exp(−4s log n)`, `∥Ah∥₂² ≥ (m/4)∥h∥₂²`.

<a id="pdf-681b6f3d947f-p277-b005"></a>
<!-- pdf-source: page=277; block=5; confidence=0.93 -->
**Proof.** By (10.24) the normalized error `h/∥h∥₂` lies in `Tₛ := {z ∈ Sⁿ⁻¹ : ∥z∥₁ ≤ 2√s}`. Apply the matrix deviation inequality in high-probability form (Exercise 9.1.8) with `u = 2√(s log n)`: with probability at least `1 − 2exp(−4s log n)`, `sup_{z∈Tₛ} |∥Az∥₂ − √m| ≤ C₁K²(w(Tₛ) + 2√(s log n)) ≤ C₂K²√(s log n) ≤ √m/2`, the last steps recalling (10.15) and using the assumption on `m` (with `C` in (10.23) chosen large enough). By the triangle inequality `∥Az∥₂ ≥ √m/2` for all `z ∈ Tₛ`; substituting `z := h/∥h∥₂` completes the proof. ∎

<a id="pdf-681b6f3d947f-p278-b001"></a>
<!-- pdf-source: page=278; block=1; confidence=0.95 -->
The final ingredient for Theorem 10.6.1 is an upper bound on the right-hand side of (10.25).

<a id="pdf-681b6f3d947f-p278-b002"></a>
<!-- pdf-source: page=278; block=2; confidence=0.96 -->
**Lemma 10.6.7.** With probability at least `1 − 2exp(−4s log n)`, `⟨h, Aᵀw⟩ ≤ CK∥h∥₂∥w∥₂√(s log n)`  (10.26).

<a id="pdf-681b6f3d947f-p278-b003"></a>
<!-- pdf-source: page=278; block=3; confidence=0.93 -->
**Proof.** As in Lemma 10.6.6, `z = h/∥h∥₂ ∈ Tₛ`. Dividing (10.26) by `∥h∥₂`, it suffices to bound `sup_{z∈Tₛ} ⟨z, Aᵀw⟩` with high probability via Talagrand's comparison inequality (Corollary 8.6.3), which requires sub-gaussian increments — verified next.

<a id="pdf-681b6f3d947f-p278-b004"></a>
<!-- pdf-source: page=278; block=4; confidence=0.95 -->
**Exercise 10.6.8.** Show the random process `Xₜ := ⟨t, Aᵀw⟩`, `t ∈ Rⁿ`, has sub-gaussian increments with `∥Xₜ − Xₛ∥_{ψ₂} ≤ CK∥w∥₂·∥t − s∥₂`. Hint: proof of sub-gaussian Chevet's inequality (Theorem 8.7.1).

<a id="pdf-681b6f3d947f-p278-b005"></a>
<!-- pdf-source: page=278; block=5; confidence=0.93 -->
Applying Talagrand's comparison inequality in high-probability form (Exercise 8.6.5) with `u = 2√(s log n)`: with probability at least `1 − 2exp(−4s log n)`, `sup_{z∈Tₛ} ⟨z, Aᵀw⟩ ≤ C₁K∥w∥₂(w(Tₛ) + 2√(s log n)) ≤ C₂K∥w∥₂√(s log n)` (recalling (10.15)), completing Lemma 10.6.7. ∎

<a id="pdf-681b6f3d947f-p278-b006"></a>
<!-- pdf-source: page=278; block=6; confidence=0.90 -->
**Proof of Theorem 10.6.1.** Combining Lemmas 10.6.5 and 10.6.6 with (10.26), by a union bound, with probability at least `1 − 4exp(−4s log n)`, `(m/4)∥h∥₂² ≤ CK∥h∥₂∥w∥₂√(s log n)`. Solving for `∥h∥₂` gives `∥h∥₂ ≤ CK·(∥w∥₂/√m)·√(s log n / m)`. ∎

<a id="pdf-681b6f3d947f-p279-b001"></a>
<!-- pdf-source: page=279; block=1; confidence=0.95 -->
**Exercise 10.6.9.** Show Theorem 10.6.1 holds with `log n` replaced by `log(en/s)`, a stronger guarantee. Hint: Exercise 10.3.8.

<a id="pdf-681b6f3d947f-p279-b002"></a>
<!-- pdf-source: page=279; block=2; confidence=0.95 -->
**Exercise 10.6.10.** Deduce the exact recovery guarantee (Theorem 10.5.1) directly from the Lasso guarantee (Theorem 10.6.1); the resulting probability may be slightly weaker.

<a id="pdf-681b6f3d947f-p279-b003"></a>
<!-- pdf-source: page=279; block=3; confidence=0.93 -->
Unconstrained Lasso: `minimize ∥y − Ax′∥₂² + λ∥x′∥₁`  (10.27), a convex problem with tunable sparsity parameter `λ`. By Lagrange multipliers the constrained and unconstrained versions are equivalent for appropriate `R` and `λ`, though this does not directly prescribe `λ`.

<a id="pdf-681b6f3d947f-p279-b004"></a>
<!-- pdf-source: page=279; block=4; confidence=0.90 -->
**Exercise 10.6.11.** Assume `m ≳ s log n`. Choose `λ ≳ √(log n)·∥w∥₂`. Then with high probability the solution `x̂` of unconstrained Lasso (10.27) satisfies `∥x̂ − x∥₂ ≲ (λ/m)√s`.

<a id="pdf-681b6f3d947f-p279-b005"></a>
<!-- pdf-source: page=279; block=5; confidence=0.97 -->
# 10.7 Notes

<a id="pdf-681b6f3d947f-p279-b006"></a>
<!-- pdf-source: page=279; block=6; confidence=0.85 -->
Bibliographic notes: the chapter's applications span compressed sensing and high-dimensional structured regression, following the tutorial [223] (with surveys/books [56, 78, 100, 42]). The `M*`-bound signal recovery (Section 10.2) follows [223] (Theorem 10.2.1, Corollary 10.3.4); the Garnaev–Gluskin bound (Exercise 10.3.10) is from [80] (see [136], [78, Ch. 10]). Low-rank matrix recovery (Section 10.4) follows [223, Sec. 10] (survey [58]). Exact sparse recovery (Section 10.5) and the escape-theorem approach (Section 10.5.1) follow [223, Sec. 9] (see [56, 78, 52, 189]).

<a id="pdf-681b6f3d947f-p280-b001"></a>
<!-- pdf-source: page=280; block=1; confidence=0.95 -->
Chapter notes for Sparse Recovery. Escape-theorem applications yield sharp phase transitions for the number of measurements needed for recovery: first for sparse signals with uniform random projections [68], see also [67, 64, 65, 66]; later for general feasible sets T and general measurement matrices [9, 162, 163]. The RIP-based exact-recovery approach of Section 10.5.2 is due to Candès–Tao [46] (see [78, Ch. 6]); an early form of Theorem 10.5.10 appears in [46], and the proof given was communicated by Y. Plan, similar to [44]. That random matrices satisfy RIP (Theorem 10.5.11) underlies compressed sensing [78, §9.1, 12.5], [222, §5.6]. The Lasso of Section 10.6 is due to Tibshirani [204]; Theorem 10.6.1 and parts of its proof trace to Bickel–Ritov–Tsybakov [22] (via a different, non-matrix-deviation argument); see also [100, Ch. 11], [42, Ch. 6].

<a id="pdf-681b6f3d947f-p281-b001"></a>
<!-- pdf-source: page=281; block=1; confidence=0.97 -->
**Chapter 11 — Dvoretzky–Milman's Theorem.** Extends the matrix deviation inequality (Ch. 9) to general norms, and to general sub-additive functions on Rⁿ, then uses it to prove Dvoretzky–Milman's theorem describing an m-dimensional random projection of an arbitrary set T ⊂ Rⁿ. Behavior depends on m versus the critical (stable) dimension d(T): for m ≳ d(T), additive Johnson–Lindenstrauss (§9.3.2) shows the projection approximately preserves the geometry of T; for m ≲ d(T), geometry saturates and the projected set is approximately a round ball.

<a id="pdf-681b6f3d947f-p281-b002"></a>
<!-- pdf-source: page=281; block=2; confidence=0.97 -->
**§11.1 — Deviations of random matrices with respect to general norms.** Generalizes the matrix deviation inequality of §9.1 by replacing the Euclidean norm with any positive-homogeneous, subadditive function.

<a id="pdf-681b6f3d947f-p281-b003"></a>
<!-- pdf-source: page=281; block=3; confidence=0.98 -->
**Definition 11.1.1.** For a vector space V, a function f : V → R is *positive-homogeneous* if f(αx) = αf(x) for all α ≥ 0 and x ∈ V, and *subadditive* if f(x + y) ≤ f(x) + f(y) for all x, y ∈ V. Despite the name, f may take negative values ("positive" refers to the multiplier α).

<a id="pdf-681b6f3d947f-p281-b004"></a>
<!-- pdf-source: page=281; block=4; confidence=0.96 -->
**Example 11.1.2.** (a) Any norm is positive-homogeneous and subadditive (subadditivity = triangle inequality). (b) Any linear functional is positive-homogeneous and subadditive; in particular, for fixed y ∈ Rᵐ, f(x) = ⟨x, y⟩ is such on Rᵐ. (c) For a bounded set S ⊂ Rᵐ, the support function f(x) := sup_{y∈S} ⟨x, y⟩, x ∈ Rᵐ (eq. 11.1).

<a id="pdf-681b6f3d947f-p282-b001"></a>
<!-- pdf-source: page=282; block=1; confidence=0.96 -->
**Example 11.1.2 (cont.).** The support function f(x) = sup_{y∈S}⟨x,y⟩ of a bounded S ⊂ Rᵐ is positive-homogeneous and subadditive on Rᵐ.

**Exercise 11.1.3.** Verify that the function f in Example 11.1.2(c) is positive-homogeneous and subadditive.

**Exercise 11.1.4.** Show that a subadditive f : V → R satisfies f(x) − f(y) ≤ f(x − y) for all x, y ∈ V (eq. 11.2).

<a id="pdf-681b6f3d947f-p282-b002"></a>
<!-- pdf-source: page=282; block=2; confidence=0.97 -->
**Theorem 11.1.5 (General matrix deviation inequality).** Let A be an m × n Gaussian matrix with i.i.d. N(0,1) entries, let f : Rᵐ → R be positive-homogeneous and subadditive, and let b ∈ R satisfy f(x) ≤ b‖x‖₂ for all x (eq. 11.3). Then for any T ⊂ Rⁿ,

E sup_{x∈T} | f(Ax) − E f(Ax) | ≤ C b γ(T),

where γ(T) is the Gaussian complexity (§7.6.2). This generalizes the matrix deviation inequality in the form of Exercise 9.1.2.

<a id="pdf-681b6f3d947f-p282-b003"></a>
<!-- pdf-source: page=282; block=3; confidence=0.97 -->
**Theorem 11.1.6 (Sub-gaussian increments).** Under the hypotheses of Theorem 11.1.5 (A an m × n Gaussian matrix with i.i.d. N(0,1) entries; f positive-homogeneous, subadditive, satisfying eq. 11.3), the process X_x := f(Ax) − E f(Ax) has sub-gaussian increments w.r.t. the Euclidean norm:

‖X_x − X_y‖_{ψ₂} ≤ C b ‖x − y‖₂  for all x, y ∈ Rⁿ (eq. 11.4).

As in §9.1, Theorem 11.1.5 follows from Talagrand's comparison inequality once these sub-gaussian increments are established.

<a id="pdf-681b6f3d947f-p282-b004"></a>
<!-- pdf-source: page=282; block=4; confidence=0.97 -->
**Exercise 11.1.7.** Deduce the general matrix deviation inequality (Theorem 11.1.5) from Talagrand's comparison inequality (in the form of Exercise 8.6.4) together with Theorem 11.1.6.

<a id="pdf-681b6f3d947f-p282-b005"></a>
<!-- pdf-source: page=282; block=5; confidence=0.95 -->
**Proof of Theorem 11.1.6.** WLOG assume b = 1. As in the proof of Theorem 9.1.3, first treat the case ‖x‖₂ = ‖y‖₂ = 1, in which the target inequality (11.4) reduces to ‖f(Ax) − f(Ay)‖_{ψ₂} ≤ C‖x − y‖₂ (eq. 11.5). [Proof continues beyond supplied pages.]

<a id="pdf-681b6f3d947f-p283-b001"></a>
<!-- pdf-source: page=283; block=1; confidence=0.95 -->
### 11.1 Deviations of random matrices with respect to general norms

<a id="pdf-681b6f3d947f-p283-b002"></a>
<!-- pdf-source: page=283; block=2; confidence=0.95 -->
**Proof, Step 1 (Creating independence).** Set $u := \tfrac{x+y}{2}$ and $v := \tfrac{x-y}{2}$, so that $x = u+v$, $y = u-v$, hence $Ax = Au+Av$ and $Ay = Au-Av$ (11.6). Since $u$ and $v$ are orthogonal, the Gaussian random vectors $Au$ and $Av$ are independent (cf. Exercise 3.3.6).

<a id="pdf-681b6f3d947f-p283-b003"></a>
<!-- pdf-source: page=283; block=3; confidence=0.90 -->
*Figure 11.1:* illustrates constructing the orthogonal pair $u,v$ from $x,y$.

<a id="pdf-681b6f3d947f-p283-b004"></a>
<!-- pdf-source: page=283; block=4; confidence=0.92 -->
**Proof, Step 2 (Using Gaussian concentration).** Condition on $a := Au$ and study the conditional distribution of $f(Ax) = f(a+Av)$. By rotation invariance, $a+Av = a + \lVert v\rVert_2\, g$ with $g \sim N(0, I_m)$ (Exercise 3.3.3). Claim: as a function of $g$, $f(a+\lVert v\rVert_2 g)$ is Lipschitz in the Euclidean norm on $\mathbb{R}^m$ with $\lVert f\rVert_{\mathrm{Lip}} \le \lVert v\rVert_2$ (11.7). Proof of claim: for $t,s \in \mathbb{R}^m$, $f(t)-f(s) = f(a+\lVert v\rVert_2 t) - f(a+\lVert v\rVert_2 s) \le f(\lVert v\rVert_2 t - \lVert v\rVert_2 s)$ by (11.2), $= \lVert v\rVert_2 f(t-s)$ by positive homogeneity, $\le \lVert v\rVert_2 \lVert t-s\rVert_2$ by (11.3) with $b=1$, giving (11.7).

<a id="pdf-681b6f3d947f-p284-b001"></a>
<!-- pdf-source: page=284; block=1; confidence=0.90 -->
### Dvoretzky–Milman's Theorem

<a id="pdf-681b6f3d947f-p284-b002"></a>
<!-- pdf-source: page=284; block=2; confidence=0.92 -->
**Proof (cont.).** Gaussian-space concentration (Theorem 5.2.2) gives $\lVert f(g) - \mathbb{E} f(g)\rVert_{\psi_2(a)} \le C\lVert v\rVert_2$, equivalently $\lVert f(a+Av) - \mathbb{E}_a f(a+Av)\rVert_{\psi_2(a)} \le C\lVert v\rVert_2$ (11.8), where the subscript $a$ marks the conditional distribution with $a = Au$ fixed.

<a id="pdf-681b6f3d947f-p284-b003"></a>
<!-- pdf-source: page=284; block=3; confidence=0.92 -->
**Proof, Step 3 (Removing the conditioning).** Since $a - Av$ has the same distribution as $a + Av$, it satisfies $\lVert f(a-Av) - \mathbb{E}_a f(a-Av)\rVert_{\psi_2(a)} \le C\lVert v\rVert_2$ (11.9). Subtracting (11.9) from (11.8), using the triangle inequality and equality of expectations, gives $\lVert f(a+Av) - f(a-Av)\rVert_{\psi_2(a)} \le 2C\lVert v\rVert_2$. Since this holds for every fixed $a = Au$, it holds unconditionally: $\lVert f(Au+Av) - f(Au-Av)\rVert_{\psi_2} \le 2C\lVert v\rVert_2$. Returning to $x,y$ via (11.6) yields the desired inequality (11.5). This proves the unit-vector case; Exercise 11.1.8 extends it to general vectors. $\blacksquare$

<a id="pdf-681b6f3d947f-p284-b004"></a>
<!-- pdf-source: page=284; block=4; confidence=0.95 -->
**Exercise 11.1.8 (Non-unit $x,y$).** Extend the proof to general (not necessarily unit) vectors $x,y$. Hint: follow Section 9.1.4.

<a id="pdf-681b6f3d947f-p284-b005"></a>
<!-- pdf-source: page=284; block=5; confidence=0.95 -->
**Remark 11.1.9.** Whether Theorem 11.1.5 holds for general subgaussian matrices $A$ is an open question.

<a id="pdf-681b6f3d947f-p284-b006"></a>
<!-- pdf-source: page=284; block=6; confidence=0.90 -->
**Exercise 11.1.10 (Anisotropic distributions).** Extend Theorem 11.1.5 to $m \times n$ matrices $A$ whose rows are independent $N(0,\Sigma)$ vectors, $\Sigma$ a general covariance matrix. Show $\bigl|\, \mathbb{E}\sup_{x\in T} f(Ax) - \mathbb{E} f(Ax) \,\bigr| \le C b\, \gamma(\Sigma^{1/2}T)$.

<a id="pdf-681b6f3d947f-p284-b007"></a>
<!-- pdf-source: page=284; block=7; confidence=0.95 -->
**Exercise 11.1.11 (Tail bounds).** Prove a high-probability version of Theorem 11.1.5. Hint: follow Exercise 9.1.8.

<a id="pdf-681b6f3d947f-p285-b001"></a>
<!-- pdf-source: page=285; block=1; confidence=0.95 -->
## 11.2 Johnson–Lindenstrauss embeddings and sharper Chevet inequality

The general matrix deviation inequality (Theorem 9.1.1) has several consequences developed below.

<a id="pdf-681b6f3d947f-p285-b002"></a>
<!-- pdf-source: page=285; block=2; confidence=0.92 -->
### 11.2.1 Johnson–Lindenstrauss Lemma for general norms

The general matrix deviation inequality (used as in Section 9.3) yields the following exercises.

<a id="pdf-681b6f3d947f-p285-b003"></a>
<!-- pdf-source: page=285; block=3; confidence=0.95 -->
**Exercise 11.2.1.** State and prove a Johnson–Lindenstrauss Lemma for a general norm on $\mathbb{R}^m$ (rather than the Euclidean norm).

<a id="pdf-681b6f3d947f-p285-b004"></a>
<!-- pdf-source: page=285; block=4; confidence=0.92 -->
**Exercise 11.2.2 (JL Lemma for $\ell_1$ norm).** Let $X$ be $N$ points in $\mathbb{R}^n$, $A$ an $m\times n$ Gaussian matrix with i.i.d. $N(0,1)$ entries, and $\varepsilon \in (0,1)$. If $m \ge C(\varepsilon)\log N$, then with high probability $Q := \sqrt{\pi/2}\, m^{-1} A$ satisfies $(1-\varepsilon)\lVert x-y\rVert_2 \le \lVert Qx-Qy\rVert_1 \le (1+\varepsilon)\lVert x-y\rVert_2$ for all $x,y \in X$. (Analogue of Theorem 5.3.1 with the projected distance in the $\ell_1$ norm.)

<a id="pdf-681b6f3d947f-p285-b005"></a>
<!-- pdf-source: page=285; block=5; confidence=0.92 -->
**Exercise 11.2.3 (JL embedding into $\ell_\infty$).** With the same notation, assume instead $m \ge N^{C(\varepsilon)}$. Show that with high probability $Q := C(\log m)^{-1/2} A$ (for an appropriate constant $C$) satisfies $(1-\varepsilon)\lVert x-y\rVert_2 \le \lVert Qx-Qy\rVert_\infty \le (1+\varepsilon)\lVert x-y\rVert_2$ for all $x,y \in X$. Here $m \ge N$, so $Q$ is an almost-isometric embedding of $X$ into $\ell_\infty$ (not a projection).

<a id="pdf-681b6f3d947f-p285-b006"></a>
<!-- pdf-source: page=285; block=6; confidence=0.92 -->
### 11.2.2 Two-sided Chevet's inequality

The general matrix deviation inequality sharpens Chevet's inequality (originally proved in Section 8.7).

<a id="pdf-681b6f3d947f-p285-b007"></a>
<!-- pdf-source: page=285; block=7; confidence=0.93 -->
**Theorem 11.2.4 (General Chevet's inequality).** Let $A$ be an $m\times n$ Gaussian matrix with i.i.d. $N(0,1)$ entries, and let $T \subset \mathbb{R}^n$, $S \subset \mathbb{R}^m$ be arbitrary bounded sets. Then $\;\mathbb{E}\, \sup_{x\in T} \bigl|\, \sup_{y\in S}\langle Ax, y\rangle - w(S)\lVert x\rVert_2 \,\bigr| \le C\,\gamma(T)\,\mathrm{rad}(S).$

<a id="pdf-681b6f3d947f-p286-b001"></a>
<!-- pdf-source: page=286; block=1; confidence=0.90 -->
By the triangle inequality, **Theorem 11.2.4** is a sharper two-sided form of Chevet's inequality (**Theorem 8.7.1**).

<a id="pdf-681b6f3d947f-p286-b002"></a>
<!-- pdf-source: page=286; block=2; confidence=0.95 -->
**Proof.** Apply the general matrix deviation inequality (**Theorem 11.1.5**) to $f(x):=\sup_{y\in S}\langle x,y\rangle$ from (11.1). Compute $b$ for which (11.3) holds: for fixed $x\in\mathbb R^m$, Cauchy–Schwarz gives $f(x)\le\sup_{y\in S}\|x\|_2\|y\|_2=\mathrm{rad}(S)\|x\|_2$, so (11.3) holds with $b=\mathrm{rad}(S)$. Compute $\mathbb E f(Ax)$: by rotation invariance of the Gaussian (Exercise 3.3.3), $Ax$ has the same distribution as $g\|x\|_2$ with $g\in N(0,I_m)$. Then $\mathbb E f(Ax)=\mathbb E f(g)\,\|x\|_2$ (positive homogeneity) $=\mathbb E\sup_{y\in S}\langle g,y\rangle\,\|x\|_2$ (definition of $f$) $=w(S)\|x\|_2$ (Gaussian width). Substituting into Theorem 11.1.5 completes the proof.

<a id="pdf-681b6f3d947f-p286-b003"></a>
<!-- pdf-source: page=286; block=3; confidence=0.90 -->
**11.3 Dvoretzky–Milman's Theorem.** A random projection of a general bounded set in $\mathbb R^n$ onto a suitably low dimension yields a convex hull that is approximately a round ball with high probability (Figures 11.2, 11.3).

<a id="pdf-681b6f3d947f-p286-b004"></a>
<!-- pdf-source: page=286; block=4; confidence=0.90 -->
**11.3.1 Gaussian images of sets.** It is convenient to use "Gaussian random projections" rather than ordinary projections; the following result compares the Gaussian projection of a general set to a Euclidean ball.

<a id="pdf-681b6f3d947f-p286-b005"></a>
<!-- pdf-source: page=286; block=5; confidence=0.95 -->
**Theorem 11.3.1 (Random projections of sets).** Let $A$ be an $m\times n$ Gaussian matrix with i.i.d. $N(0,1)$ entries and $T\subset\mathbb R^n$ bounded. Then with probability at least $0.99$,
$$r_-B_2^m\subset\mathrm{conv}(AT)\subset r_+B_2^m,$$
where $r_\pm:=w(T)\pm C\sqrt{m}\,\mathrm{rad}(T)$. Here $\mathrm{rad}(T)$ is the radius of $T$ defined in (8.47).

<a id="pdf-681b6f3d947f-p287-b001"></a>
<!-- pdf-source: page=287; block=1; confidence=0.88 -->
The left inclusion holds only when $r_-\ge 0$; the right inclusion always holds. Theorem 11.3.1 will be deduced from two-sided Chevet's inequality; Exercise 11.3.2 provides the link, characterizing when the support function (11.1) equals the $\ell_2$ norm (iff $S$ is the Euclidean ball), with a stability version.

<a id="pdf-681b6f3d947f-p287-b002"></a>
<!-- pdf-source: page=287; block=2; confidence=0.95 -->
**Exercise 11.3.2.** (a) For closed bounded $V\subset\mathbb R^m$: $\mathrm{conv}(V)=B_2^m$ iff $\sup_{x\in V}\langle x,y\rangle=\|y\|_2$ for all $y\in\mathbb R^m$. (b) For bounded $V\subset\mathbb R^m$ and $r_-,r_+\ge 0$: the inclusion $r_-B_2^m\subset\mathrm{conv}(V)\subset r_+B_2^m$ holds iff $r_-\|y\|_2\le\sup_{x\in V}\langle x,y\rangle\le r_+\|y\|_2$ for all $y\in\mathbb R^m$.

<a id="pdf-681b6f3d947f-p287-b003"></a>
<!-- pdf-source: page=287; block=3; confidence=0.95 -->
**Proof of Theorem 11.3.1.** Write two-sided Chevet's inequality as $\mathbb E\sup_{y\in S}\big|\sup_{x\in T}\langle Ax,y\rangle-w(T)\|y\|_2\big|\le C\gamma(S)\,\mathrm{rad}(T)$, with $T\subset\mathbb R^n$, $S\subset\mathbb R^m$ (obtained from Theorem 11.2.4 with $T,S$ swapped and $AT$ in place of $A$). Take $S=S^{m-1}$, whose Gaussian complexity $\gamma(S)\le\sqrt m$. By Markov's inequality, with probability $\ge 0.99$: $\big|\sup_{x\in T}\langle Ax,y\rangle-w(T)\|y\|_2\big|\le C\sqrt m\,\mathrm{rad}(T)$ for every $y\in S^{m-1}$. Triangle inequality and the definition of $r_\pm$ give $r_-\le\sup_{x\in T}\langle Ax,y\rangle\le r_+$ for $y\in S^{m-1}$; by homogeneity $r_-\|y\|_2\le\sup_{x\in T}\langle Ax,y\rangle\le r_+\|y\|_2$ for all $y\in\mathbb R^m$. Since $\sup_{x\in T}\langle Ax,y\rangle=\sup_{x\in AT}\langle x,y\rangle$, apply Exercise 11.3.2 with $V=AT$ to finish.

<a id="pdf-681b6f3d947f-p288-b001"></a>
<!-- pdf-source: page=288; block=1; confidence=0.90 -->
**11.3.2 Dvoretzky–Milman's Theorem.**

<a id="pdf-681b6f3d947f-p288-b002"></a>
<!-- pdf-source: page=288; block=2; confidence=0.95 -->
**Theorem 11.3.3 (Dvoretzky–Milman's theorem: Gaussian form).** Let $A$ be $m\times n$ Gaussian with i.i.d. $N(0,1)$ entries, $T\subset\mathbb R^n$ bounded, $\varepsilon\in(0,1)$. If $m\le c\varepsilon^2 d(T)$, where $d(T)$ is the stable dimension of $T$ (Section 7.6), then with probability at least $0.99$,
$$(1-\varepsilon)B\subset\mathrm{conv}(AT)\subset(1+\varepsilon)B,$$
where $B$ is a Euclidean ball of radius $w(T)$.

<a id="pdf-681b6f3d947f-p288-b003"></a>
<!-- pdf-source: page=288; block=3; confidence=0.95 -->
**Proof.** Translating $T$, assume $0\in T$. Apply Theorem 11.3.1; it remains to check $r_-\ge(1-\varepsilon)w(T)$ and $r_+\le(1+\varepsilon)w(T)$, which follow from
$$C\sqrt m\,\mathrm{rad}(T)\le\varepsilon w(T).\quad(11.10)$$
By assumption and Definition 7.6.2, $m\le c\varepsilon^2 d(T)\le \varepsilon^2 w(T)^2/\mathrm{diam}(T)^2$ for suitably small $c>0$. Since $0\in T$, $\mathrm{rad}(T)\le\mathrm{diam}(T)$, which yields (11.10).

<a id="pdf-681b6f3d947f-p288-b004"></a>
<!-- pdf-source: page=288; block=4; confidence=0.90 -->
**Remark 11.3.4.** If $0\in T$, the ball $B$ can be centered at the origin; otherwise $B$ may be centered at any fixed $x_0\in T$. **Exercise 11.3.5.** State and prove a high-probability version of Dvoretzky–Milman's theorem.

<a id="pdf-681b6f3d947f-p288-b005"></a>
<!-- pdf-source: page=288; block=5; confidence=0.92 -->
**Example 11.3.6 (Projections of the cube).** For $T=[-1,1]^n=B_\infty^n$: $w(T)=\sqrt{2/\pi}\cdot n$ (recall (7.17)), and since $\mathrm{diam}(T)=2\sqrt n$, the stable dimension is $d(T)\asymp w(T)^2/\mathrm{diam}(T)^2\asymp n$. By Theorem 11.3.3, if $m\le c\varepsilon^2 n$ then with high probability $(1-\varepsilon)B\subset\mathrm{conv}(AT)\subset(1+\varepsilon)B$, where $B$ is the Euclidean ball of radius $\sqrt{2/\pi}\cdot n$.

<a id="pdf-681b6f3d947f-p289-b001"></a>
<!-- pdf-source: page=289; block=1; confidence=0.95 -->
A random Gaussian projection of the cube onto a subspace of dimension $m \asymp n$ is close to a round ball (illustrated in Figure 11.2, a 7-dimensional cube projected onto the plane).

<a id="pdf-681b6f3d947f-p289-b002"></a>
<!-- pdf-source: page=289; block=2; confidence=0.97 -->
**Exercise 11.3.7 (Gaussian cloud).** Let $g_1,\dots,g_n \sim N(0, I_m)$ be i.i.d. random vectors in $\mathbb{R}^m$. Assuming $n \ge \exp(Cm)$ for a large enough absolute constant $C$, show that with high probability the convex hull of these $n$ points is approximately a Euclidean ball of radius $\sim \sqrt{\log n}$. Hint: take $T$ to be the canonical basis $\{e_1,\dots,e_n\}$ in $\mathbb{R}^n$, write $g_i = T e_i$, and apply Theorem 11.3.3. (Figure 11.3.)

<a id="pdf-681b6f3d947f-p290-b001"></a>
<!-- pdf-source: page=290; block=1; confidence=0.96 -->
**Exercise 11.3.8 (Projections of ellipsoids).** Let $E = S(B_2^n)$ be the ellipsoid in $\mathbb{R}^n$ that is the image of the unit Euclidean ball under an $n \times n$ matrix $S$, and let $A$ be an $m \times n$ Gaussian matrix with i.i.d. $N(0,1)$ entries. Assuming $m \lesssim r(S)$, the stable rank of $S$ (Definition 7.6.7), show that with high probability the Gaussian projection is almost a round ball of radius $\|S\|_F$:
$$A(E) \approx \|S\|_F\, B_2^n.$$
Hint: in Theorem 11.3.3 replace the Gaussian width $w(T)$ by $h(T) = \big(\mathbb{E}\sup_{t\in T}\langle g, t\rangle^2\big)^{1/2}$ from (7.19), which is easier to compute for ellipsoids.

<a id="pdf-681b6f3d947f-p290-b002"></a>
<!-- pdf-source: page=290; block=2; confidence=0.96 -->
**Exercise 11.3.9 (Random projection in the Grassmanian).** Prove a version of Dvoretzky-Milman's theorem for the projection $P$ onto a random $m$-dimensional subspace of $\mathbb{R}^n$: under the same assumptions,
$$(1-\varepsilon)B \subset \operatorname{conv}(PT) \subset (1+\varepsilon)B,$$
where $B$ is a Euclidean ball of radius $w_s(T)$, the spherical width of $T$ (Section 7.5.2).

<a id="pdf-681b6f3d947f-p290-b003"></a>
<!-- pdf-source: page=290; block=3; confidence=0.95 -->
**Summary of random projections of geometric sets.** Comparing Dvoretzky-Milman's theorem with the diameter estimates of Sections 7.7 and 9.2.2: a random projection $P$ of $T \subset \mathbb{R}^n$ onto an $m$-dimensional subspace exhibits a phase transition. High-dimensional regime ($m \gtrsim d(T)$): the diameter shrinks by a factor $\sim \sqrt{m/n}$,
$$\operatorname{diam}(PT) \lesssim \sqrt{\tfrac{m}{n}}\,\operatorname{diam}(T)\quad\text{if } m \ge d(T),$$
and the additive Johnson-Lindenstrauss result (Section 9.3.2) shows $P$ approximately preserves the geometry of $T$. Low-dimensional regime ($m \lesssim d(T)$): the projected set stops shrinking,
$$\operatorname{diam}(PT) \lesssim w_s(T) \asymp \tfrac{w(T)}{\sqrt{n}}\quad\text{if } m \le d(T)$$
(Section 7.7.1).

<a id="pdf-681b6f3d947f-p291-b001"></a>
<!-- pdf-source: page=291; block=1; confidence=0.95 -->
Dvoretzky-Milman's theorem explains why the size stops shrinking for $m \lesssim d(T)$: in this regime $PT$ is approximately a round ball of radius of order $w_s(T)$ (Exercise 11.3.9), independent of how small $m$ is. Summary: a random projection preserves the geometry of $T$ when $m \gtrsim d(T)$; for smaller $m$, $PT$ becomes approximately a round ball of diameter $\sim w_s(T)$ whose size does not shrink with $m$.

<a id="pdf-681b6f3d947f-p291-b002"></a>
<!-- pdf-source: page=291; block=2; confidence=0.90 -->
**11.4 Notes.** Attributions and history: the general matrix deviation inequality (Theorem 11.1.5) and its proof are due to G. Schechtman [181]. Chevet's inequality was proved by S. Chevet [54], with constants improved by Y. Gordon [84]; the version in Theorem 11.2.4 is reconstructed from Gordon [84, 86]. Dvoretzky-Milman's theorem: A. Dvoretzky [73, 74] proved Grothendieck's conjecture that every $n$-dimensional normed space has an $m$-dimensional almost-Euclidean subspace with $m = m(n) \to \infty$; V. Milman gave a probabilistic proof and studied the optimal $m(n)$. Theorem 11.3.3 is due to Milman [148]. The stable dimension $d(T)$ is critical: the conclusion fails for $m \gg d(T)$ by Milman-Schechtman [151]. Related: central limit theorems for $m$-dimensional random marginals of distributions in $\mathbb{R}^n$ — for log-concave distributions first proved by B. Klartag [116], for discrete sets see E. Meckes [142]. The phenomenon in the Section 7.7 summary is due to V. Milman [149].

<a id="pdf-681b6f3d947f-p292-b001"></a>
<!-- pdf-source: page=292; block=1; confidence=0.98 -->
**Bibliography.** Reference list (start).

<a id="pdf-681b6f3d947f-p292-b002"></a>
<!-- pdf-source: page=292; block=2; confidence=0.90 -->
Numbered reference entries [1]–[20]. Topics span probability, high-dimensional statistics, and geometric analysis, including: stochastic block model exact recovery (Abbe–Bandeira–Hall [1]), Chevet-type inequalities and submatrix norms [2], random fields and geometry [3], Ahlswede–Winter matrix concentration [4], Banach space theory [5], the Szarek–Talagrand theorem [6], cut-norm via Grothendieck's inequality [7], the probabilistic method [8], phase transitions in convex programs with random data [9], tensor decompositions for latent-variable models [10], asymptotic geometric analysis [11], Bakry–Ledoux Lévy–Gromov isoperimetry [12], modern convex geometry [13], mathematics of data science lecture notes [14], Bandeira–van Handel norm bounds for random matrices with independent entries [15], Gaussian isoperimetry [16–17], Rademacher/Gaussian complexities [18], polynomial learning of distribution families [19], and Foundations of Data Science [20].

<a id="pdf-681b6f3d947f-p293-b001"></a>
<!-- pdf-source: page=293; block=1; confidence=0.90 -->
Reference entries [21]–[43] (Bibliography continued). Topics: matrix analysis (Bhatia [21]), Lasso/Dantzig selector analysis [22], probability and measure [23], Bobkov isoperimetric inequality on the cube and Gauss space [24], combinatorics and random graphs (Bollobás [25–26]), non-backtracking spectrum for community detection [27], Borell's Brunn–Minkowski inequality in Gauss space [28], convex analysis/optimization [29,34], concentration inequalities (Boucheron–Lugosi–Massart [30]), sparse dimensionality reduction [31], Bourgain–Tzafriri invertibility of large submatrices [32], statistical learning theory [33], the Grothendieck constant below Krivine's bound [35], geometry of isotropic convex bodies [36], stochastic processes [37], Markov Chain Monte Carlo handbook [38], convex optimization complexity (Bubeck [39]), operator Khintchine inequalities [40–41], statistics for high-dimensional data [42], and optimal estimation of structured covariance/precision matrices [43].

<a id="pdf-681b6f3d947f-p294-b001"></a>
<!-- pdf-source: page=294; block=1; confidence=0.90 -->
Reference entries [44]–[67] (Bibliography continued). Topics: restricted isometry property and compressed sensing (Candès [44]), exact and near-optimal matrix completion via convex optimization [45,47], decoding by linear programming (Candès–Tao [46]), Glivenko–Cantelli (Cantelli [48]), Bernstein–Jackson inequalities and compactness of operators [49], Gelfand numbers (Carl–Pajor [50]), finite frame theory [51], convex geometry of linear inverse problems [52], masked sample covariance via matrix concentration [53], Chevet's Gaussian series in tensor products [54], spectral algorithms for sparse stochastic block models [55], introductions to and overviews of compressed sensing / low-rank matrix recovery [56,58], 1-bit matrix completion [57], local operator theory and random matrices (Davidson–Szarek [59]), Davis–Kahan eigenvector rotation theorem [60], decoupling inequalities for U-statistics and the decoupling monograph (de la Peña et al. [61–62]), tail bounds via generic chaining (Dirksen [63]), and phase transitions in compressed sensing / matrix recovery via minimax denoising and approximate message passing (Donoho et al. [64–67]).

<a id="pdf-681b6f3d947f-p295-b001"></a>
<!-- pdf-source: page=295; block=1; confidence=0.97 -->
# Bibliography — entries [68]–[92] (page 287)

<a id="pdf-681b6f3d947f-p295-b002"></a>
<!-- pdf-source: page=295; block=2; confidence=0.90 -->
Bibliography entries [68]–[92]. No mathematical statements; reference list covering: random-polytope face counting (Donoho–Tanner [68]); Gaussian process regularity, entropy/compact subsets of Hilbert space, and empirical CLTs (Dudley [69]–[71], Fernique [75]); probability texts (Durrett [72]); Dvoretzky's theorem on convex bodies/Banach spaces [73]–[74]; abstract harmonic analysis (Folland [76]); community detection survey [77]; compressive sensing (Foucart–Rauhut [78]); traces of finite sets (Frankl [79]); diameters of Euclidean sphere (Garnaev–Gluskin [80]); Euclidean structure in normed spaces [81]; Glivenko empirical-law determination [82]; Goemans–Williamson SDP for MAX-CUT/satisfiability [83]; Gordon's Gaussian-process inequalities, elliptically contoured distributions, spherical sections, escape-through-a-mesh, and majorization [84]–[88]; Fourier PCA / tensor decomposition [89]; Grothendieck's metric theory of tensor products [90]; Gromov's appendix on Lévy isoperimetric inequality [91]; low-rank matrix recovery (Gross [92]).

<a id="pdf-681b6f3d947f-p296-b001"></a>
<!-- pdf-source: page=296; block=1; confidence=0.90 -->
Bibliography entries [93]–[117] (page 288). No mathematical statements; reference list covering: high-dimensional-geometry concentration survey (Guédon [93]); community detection via Grothendieck's inequality [94]; best constants in the Khintchine inequality (Haagerup [95]); exact cluster recovery via SDP [96]; Hanson–Wright tail bound for quadratic forms [97]; isoperimetric problems / optimal numbering on graphs (Harper [98]); statistical-learning texts (Hastie–Tibshirani–Friedman [99], lasso/sparsity [100], James et al. [106]); generalization of Sauer's lemma (Haussler–Long [101]); kernel methods [102]; stochastic blockmodels [103]; learning mixtures of spherical Gaussians [104]; Slepian's inequality via CLT [105]; random graphs (Janson–Łuczak–Ruciński [107]); phase transitions in SDP relaxations [108]; sub-gaussian matrices on sets [109]; Johnson–Lindenstrauss lemma [110]; Slepian–Gordon-type Gaussian inequality (Kahane [111]); disentangling Gaussians [112]; matrix completion [113]; MAX-CUT inapproximability and Grothendieck-type combinatorial-optimization inequalities [114]–[115]; CLT for convex sets and empirical processes / random projections (Klartag, Klartag–Mendelson [116]–[117]).

<a id="pdf-681b6f3d947f-p297-b001"></a>
<!-- pdf-source: page=297; block=1; confidence=0.90 -->
Bibliography entries [118]–[143] (page 289). No mathematical statements; reference list covering: Khintchine constants for Steinhaus variables (König [118]); concentration/moment bounds for sample covariance operators [119]; absolute constants in Berry–Esseen inequalities (Shevtsova [120]); introduction to frames [121]; Grothendieck constant and positive-type functions on spheres (Krivine [122]); statistical-learning-theory texts [123]; optimality of the Johnson–Lindenstrauss lemma [124]; dimension-free structure of nonhomogeneous random matrices [125]; semidefinite optimization notes [126]; stochastic-process text [127]; concentration/regularization of random graphs [128]; Ledoux's concentration-of-measure monograph and Ledoux–Talagrand probability in Banach spaces [129]–[130]; partial covariance estimation [131]; matrix-deviation tool on geometric sets (Liaw–Mehrabian–Plan–Vershynin [132]); absolutely summing operators in Lp [133]; Khintchine inequalities in Cp and noncommutative Khintchine/Paley inequalities (Lust-Piquard, Pisier [134]–[135]); n-widths inequality [136]; geometric discrepancy and discrete geometry (Matoušek [137]–[138]); symmetric sequences (Maurey [139]); Steiner formulas / concentration of intrinsic volumes [140]; spectral partitioning of random graphs [141]; measure-theoretic Dvoretzky theorem (Meckes [142]); statistical-learning-theory notes (Mendelson [143]).

<a id="pdf-681b6f3d947f-p298-b001"></a>
<!-- pdf-source: page=298; block=1; confidence=0.90 -->
# Bibliography (continued, entries [144]–[168])

<a id="pdf-681b6f3d947f-p298-b002"></a>
<!-- pdf-source: page=298; block=2; confidence=0.90 -->
Condensed bibliography entries:
- [144] Mendelson, *A remark on the diameter of random sections of convex bodies*, GAFA Seminar Notes, LNM 2116, 2014.
- [145] Mendelson, Pajor, Tomczak-Jaegermann, *Reconstruction and subgaussian operators in asymptotic geometric analysis*, GAFA 17 (2007), 1248–1282.
- [146] Mendelson, Vershynin, *Entropy and the combinatorial dimension*, Invent. Math. 152 (2003), 37–55.
- [147] Mezzadri, *How to generate random matrices from the classical compact groups*, Notices AMS 54 (2007), 592–604.
- [148] Milman, *New proof of Dvoretzky's theorem on sections of convex bodies*, Funct. Anal. Appl. 5 (1971), 28–37.
- [149] Milman, *A note on a low M*-estimate*, in Geometry of Banach Spaces (Strobl 1989), LMS LNS 158, CUP 1990, 219–229.
- [150] Milman, Schechtman, *Asymptotic theory of finite-dimensional normed spaces* (appendix by Gromov), LNM 1200, Springer 1986.
- [151] Milman, Schechtman, *Global versus local asymptotic theories of finite-dimensional normed spaces*, Duke Math. J. 90 (1997), 73–93.
- [152] Mitzenmacher, Upfal, *Probability and Computing*, CUP 2005.
- [153] Moitra, *Algorithmic aspects of machine learning*, preprint, MIT 2014.
- [154] Moitra, Valiant, *Settling the polynomial learnability of mixtures of Gaussians*, FOCS 2010, 93–102.
- [155] Montgomery-Smith, *The distribution of Rademacher sums*, Proc. AMS 109 (1990), 517–522.
- [156] Mörters, Peres, *Brownian Motion*, CUP 2010.

<a id="pdf-681b6f3d947f-p298-b003"></a>
<!-- pdf-source: page=298; block=3; confidence=0.88 -->
- [157] Mossel, Neeman, Sly, *Belief propagation, robust reconstruction and optimal recovery of block models*, Ann. Appl. Probab. 26 (2016), 2211–2256.
- [158] Newman, *Networks: An Introduction*, Oxford UP 2010.
- [159] Oliveira, *Sums of random Hermitian matrices and an inequality by Rudelson*, Electron. Commun. Probab. 15 (2010), 203–212.
- [160] Oliveira, *Concentration of the adjacency matrix and of the Laplacian in random graphs with independent edges*, unpublished 2009, arXiv:0911.0600.
- [161] Oymak, Hassibi, *New null space results and recovery thresholds for matrix rank minimization*, ISIT 2011, arXiv:1011.6326.
- [162] Oymak, Thrampoulidis, Hassibi, *The squared-error of generalized LASSO: a precise analysis*, Allerton 2013, arXiv:1311.0830.
- [163] Oymak, Tropp, *Universality laws for randomized dimension reduction, with applications*, Inform. Inference (2017).
- [164] Pajor, *Sous-espaces ℓ₁ⁿ des espaces de Banach*, Hermann, Paris 1985.
- [165] Petz, *A survey of certain trace inequalities*, Banach Center Publ. 30 (1994), 287–298.
- [166] Pisier, *Remarques sur un résultat non publié de B. Maurey*, Séminaire d'Analyse Fonctionnelle 1980–81, Exp. V, École Polytech. 1981.
- [167] Pisier, *The Volume of Convex Bodies and Banach Space Geometry*, Cambridge Tracts in Math. 94, CUP 1989.
- [168] Pisier, *Grothendieck's theorem, past and present*, Bull. AMS 49 (2012), 237–323.

<a id="pdf-681b6f3d947f-p299-b001"></a>
<!-- pdf-source: page=299; block=1; confidence=0.88 -->
- [169] Plan, Vershynin, *Robust 1-bit compressed sensing and sparse logistic regression: a convex programming approach*, IEEE Trans. Inf. Theory 59 (2013), 482–494.
- [170] Plan, Vershynin, Yudovina, *High-dimensional estimation with geometric constraints*, Inform. Inference 0 (2016), 1–40.
- [171] Pollard, *Empirical Processes: Theory and Applications*, NSF-CBMS Regional Conf. Series 2, IMS 1990.
- [172] Rauhut, *Compressive sensing and structured random matrices*, in Theoretical Foundations and Numerical Methods for Sparse Recovery (ed. Fornasier), Radon Series 9, de Gruyter 2010, 1–92.
- [173] Recht, *A simpler approach to matrix completion*, J. Mach. Learn. Res. 12 (2011), 3413–3430.
- [174] Rigollet, *High-dimensional statistics*, MIT lecture notes 2015 (MIT OCW).
- [175] Rudelson, *Random vectors in the isotropic position*, J. Funct. Anal. 164 (1999), 60–72.
- [176] Rudelson, Vershynin, *Combinatorics of random processes and sections of convex bodies*, Ann. of Math. 164 (2006), 603–648.
- [177] Rudelson, Vershynin, *Sampling from large matrices: an approach through geometric functional analysis*, J. ACM (2007), Art. 21, 19 pp.
- [178] Rudelson, Vershynin, *On sparse reconstruction from Fourier and Gaussian measurements*, Comm. Pure Appl. Math. 61 (2008), 1025–1045.
- [179] Rudelson, Vershynin, *Hanson-Wright inequality and sub-gaussian concentration*, Electron. Commun. Probab. 18 (2013), 1–9.
- [180] Sauer, *On the density of families of sets*, J. Comb. Theory 13 (1972), 145–147.
- [181] Schechtman, *Two observations regarding embedding subsets of Euclidean spaces in normed spaces*, Adv. Math. 200 (2006), 125–135.

<a id="pdf-681b6f3d947f-p299-b002"></a>
<!-- pdf-source: page=299; block=2; confidence=0.80 -->
- [182] Schilling, Partzsch, *Brownian Motion: An Introduction to Stochastic Processes*, 2nd ed., De Gruyter 2014.
- [183] Seginer, *The expected norm of random matrices*, Combin. Probab. Comput. 9 (2000), 149–166.
- [184] Shelah, *A combinatorial problem: stability and order for models and theories in infinitary languages*, Pacific J. Math. 41 (1972), 247–261.
- [185] Simonovits, *How to compute the volume in high dimension?*, Math. Program. 97 (2003), no. 1-2, Ser. B, 337–374.
- [186] Slepian, *The one-sided barrier problem for Gaussian noise*, Bell System Tech. J. 41 (1962), 463–501.
- [187] Slepian, *On the zeroes of Gaussian noise*, in Time Series Analysis (ed. Rosenblatt), Wiley 1963, 104–115.
- [188] Stewart, Sun, *Matrix Perturbation Theory*, Academic Press 1990.
- [189] Stojnic, *Various thresholds for ℓ₁-optimization in compressed sensing*, unpublished 2009, arXiv:0907.3666.
- [190] Stojnic, *Regularly random duality*, unpublished 2013, arXiv:1303.7295.
- [191] Sudakov, *Gaussian random processes and measures of solid angles in Hilbert spaces*, Soviet Math. Dokl. 12 (1971), 412–415.
- [192] Sudakov, Cirelson, *Extremal properties of half-spaces for spherically invariant measures*, Zap. Nauchn. Sem. LOMI 41 (1974), 14–24.
- [193] Sudakov, *Gaussian random processes and measures of solid angles in Hilbert space*, Dokl. Akad. Nauk SSSR 197 (1971), 43–45; Engl. transl. Soviet Math. Dokl. 12 (1971), 412–415.

<a id="pdf-681b6f3d947f-p300-b001"></a>
<!-- pdf-source: page=300; block=1; confidence=0.85 -->
- [194] Sudakov, *Geometric problems in the theory of infinite-dimensional probability distributions*, Trudy Mat. Inst. Steklov 141 (1976); Engl. transl. Proc. Steklov Inst. Math. 2, AMS.
- [195] Szarek, *On the best constants in the Khinchin inequality*, Studia Math. 58 (1976), 197–208.
- [196] Szarek, Talagrand, *An "isomorphic" version of the Sauer-Shelah lemma and the Banach-Mazur distance to the cube*, GAFA 1987–88, LNM 1376, Springer 1989, 105–112.
- [197] Szarek, Talagrand, *On the convexified Sauer-Shelah theorem*, J. Combin. Theory Ser. B 69 (1997), 183–192.
- [198] Talagrand, *A new look at independence*, Ann. Probab. 24 (1996), 1–34.
- [199] Talagrand, *The Generic Chaining: Upper and Lower Bounds of Stochastic Processes*, Springer Monogr. Math., Springer 2005.
- [200] Thrampoulidis, Abbasi, Hassibi, *Precise error analysis of regularized M-estimators in high dimensions*, preprint, arXiv:1601.06233.
- [201] Thrampoulidis, Hassibi, *Isotropically random orthogonal matrices: performance of LASSO and minimum conic singular values*, ISIT 2015, arXiv:503.07236.
- [202] Thrampoulidis, Oymak, Hassibi, *The Gaussian min-max theorem in the presence of convexity*, arXiv:1408.4837.
- [203] Thrampoulidis, Oymak, Hassibi, *Simple error bounds for regularized noisy linear inverse problems*, ISIT 2014, arXiv:1401.6578.
- [204] Tibshirani, *Regression shrinkage and selection via the lasso*, J. Roy. Statist. Soc. Ser. B 58 (1996), 267–288.
- [205] Tomczak-Jaegermann, *Banach-Mazur Distances and Finite-Dimensional Operator Ideals*, Pitman Monogr. 38, Longman/Wiley 1989.

<a id="pdf-681b6f3d947f-p300-b002"></a>
<!-- pdf-source: page=300; block=2; confidence=0.85 -->
- [206] Tropp, *User-friendly tail bounds for sums of random matrices*, Found. Comput. Math. 12 (2012), 389–434.
- [207] Tropp, *An introduction to matrix concentration inequalities*, Found. Trends Mach. Learning 8, no. 1-2 (2015), 1–230.
- [208] Tropp, *Convex recovery of a structured signal from independent random linear measurements*, in Sampling Theory, a Renaissance (ed. Pfander), ANHA, Birkhäuser 2015.
- [209] Tropp, *The expected norm of a sum of independent random matrices: an elementary approach*, High-Dimensional Probability VII (Cargèse Volume), Progress in Probability 71, Birkhäuser 2016.
- [210] van de Geer, *Applications of Empirical Process Theory*, Cambridge Series in Stat. and Prob. Math. 6, CUP 2000.
- [211] van der Vaart, Wellner, *Weak Convergence and Empirical Processes*, Springer Series in Statistics, Springer 1996.
- [212] van Handel, *Probability in high dimension*, lecture notes (online).
- [213] van Handel, *Structured random matrices*, IMA Volume "Discrete Structures: Analysis and Applications", Springer.
- [214] van Handel, *Chaining, interpolation, and convexity*, J. Eur. Math. Soc. (2016).
- [215] van Handel, *Chaining, interpolation, and convexity II: the contraction principle*, preprint 2017.
- [216] van Lint, *Introduction to Coding Theory*, 3rd ed., GTM 86, Springer 1999.
- [217] Vapnik, Chervonenkis, *The uniform convergence of frequencies of the appearance of events to their probabilities*, Teor. Veroyatnost. i Primenen. 16 (1971), 264–279.

<a id="pdf-681b6f3d947f-p301-b001"></a>
<!-- pdf-source: page=301; block=1; confidence=0.95 -->
**Bibliography** (page 293 in source numbering) — reference entries [218]–[230].

<a id="pdf-681b6f3d947f-p301-b002"></a>
<!-- pdf-source: page=301; block=2; confidence=0.95 -->
Condensed citation list:

- **[218]** Vempala, *Geometric random walks: a survey*, MSRI Publ. 52, Cambridge Univ. Press, 2005, pp. 577–616.
- **[219]** Vershynin, *Integer cells in convex sets*, Adv. Math. **197** (2005), 248–273.
- **[220]** Vershynin, *A note on sums of independent random matrices after Ahlswede-Winter*, unpublished manuscript, 2009.
- **[221]** Vershynin, *Golden-Thompson inequality*, unpublished manuscript, 2009.
- **[222]** Vershynin, *Introduction to the non-asymptotic analysis of random matrices*, in Compressed Sensing, Cambridge Univ. Press, 2012, pp. 210–268.
- **[223]** Vershynin, *Estimation in high dimensions: a geometric perspective*, in Sampling Theory, a Renaissance, Birkhäuser, 2015, pp. 3–66.
- **[224]** Villani, *Topics in optimal transportation*, GSM 58, AMS, 2003.
- **[225]** Vu, *Singular vectors under random perturbation*, Random Struct. Algorithms **39** (2011), 526–538.
- **[226]** Wedin, *Perturbation bounds in connection with singular value decomposition*, BIT **12** (1972), 99–111.
- **[227]** Wigderson & Xiao, *Derandomizing the Ahlswede-Winter matrix-valued Chernoff bound using pessimistic estimators*, Theory of Computing **4** (2008), 53–76.
- **[228]** Wright, *A bound on tail probabilities for quadratic forms in independent random variables whose distributions are not necessarily symmetric*, Ann. Probab. **1** (1973), 1068–1070.
- **[229]** Yu, Wang & Samworth, *A useful variant of the Davis-Kahan theorem for statisticians*, Biometrika **102** (2015), 315–323.
- **[230]** Zhou & Zhang, *Minimax Rates of Community Detection in Stochastic Block Models*, Ann. Statist., to appear.
