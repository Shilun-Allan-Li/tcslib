<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: b53c1a5aa27d0b526ee170ef1dd81e525a7c661ce586b811f68ddc6b60525352 -->

<a id="pdf-b53c1a5aa27d-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=1.00 -->
# Robust Optimality of Gaussian Noise Stability

<a id="pdf-b53c1a5aa27d-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=1.00 -->
The paper establishes that Gaussian half-spaces uniquely maximize noise stability among sets of fixed Gaussian measure, and proves a quantitative stability result: near-maximizers are close to half-spaces. The approach gives a direct semigroup proof of Borell’s theorem and applications.

<a id="pdf-b53c1a5aa27d-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=1.00 -->
# 1 Introduction

<a id="pdf-b53c1a5aa27d-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.98 -->
Gaussian stability connects isoperimetry, probability, geometry, and theoretical computer science. Borell’s theorem says parallel half-spaces maximize the probability that positively correlated Gaussian vectors both lie in sets of prescribed Gaussian measures.

<a id="pdf-b53c1a5aa27d-p001-b005"></a>
<!-- pdf-source: page=1; block=5; confidence=0.98 -->
Earlier proofs of Borell’s inequality used symmetrization methods. This paper presents a semigroup-based proof motivated by Ledoux’s question and strengthens the result with uniqueness and quantitative closeness to half-spaces.

<a id="pdf-b53c1a5aa27d-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.99 -->
The paper claims uniqueness of the maximizing half-spaces up to almost-sure equality and a robust version: sets whose stability is nearly optimal for their measure must be close to half-spaces.

<a id="pdf-b53c1a5aa27d-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=1.00 -->
## 1.1 Discrete applications

<a id="pdf-b53c1a5aa27d-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.99 -->
The “majority is stablest” theorem concerns subsets \(A\) of the discrete cube \(\{-1,1\}^n\) for which each coordinate \(x_i\) has only a small influence on whether \(x\in A\). It says that among all such sets, those with the most noise stability have the form \(\{x:\sum_i a_i x_i\le b\}\). A robust version says that any set with small coordinate influences and almost optimal noise sensitivity must be close to a set of this form.

<a id="pdf-b53c1a5aa27d-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.97 -->
The robust majority-is-stablest result implies that, among low-influence election rules, weighted majority-based methods are essentially the only ones minimizing the probability of a cyclic (non-rational) outcome.

<a id="pdf-b53c1a5aa27d-p002-b005"></a>
<!-- pdf-source: page=2; block=5; confidence=0.96 -->
For the sphere-embedding approach to Max-Cut, random hyperplane cuts are optimal; the robust stability theorem implies that any nearly optimal cutting procedure is close to using a random hyperplane. The argument uses a high-dimensional spherical isoperimetric result for pairs of points with prescribed inner product \(\rho\).

<a id="pdf-b53c1a5aa27d-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=1.00 -->
## 1.2 Borell’s theorem and a functional variant

<a id="pdf-b53c1a5aa27d-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.99 -->
**Definition.** Let \(\gamma_n\) be standard Gaussian measure on \(\mathbb R^n\). For \(-1<\rho<1\), let \((X,Y)\) be jointly Gaussian standard vectors with \(\mathbb E[X_iY_j]=\delta_{ij}\rho\), and denote their joint law by \(\Pr_\rho\). Write \(\varphi\) for the standard one-dimensional Gaussian density and \(\Phi\) for its distribution function.

<a id="pdf-b53c1a5aa27d-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.99 -->
**Theorem 1.1 (Borell).** For \(0<\rho<1\) and measurable \(A_1,A_2\subseteq\mathbb R^n\),
\[
\Pr_\rho[X\in A_1,\ Y\in A_2]\le \Pr_\rho[X\in B_1,\ Y\in B_2], \tag{1.1}
\]
where
\[
B_i=\{x\in\mathbb R^n:x_1\le \Phi^{-1}(\gamma_n(A_i))\},\qquad i=1,2,
\]
are parallel half-spaces with the respective Gaussian measures of \(A_i\). For \(-1<\rho<0\), inequality (1.1) is reversed.

<a id="pdf-b53c1a5aa27d-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.99 -->
We define
\[
J(x,y;\rho)=\Pr_\rho(X_1\le \Phi^{-1}(x),Y_1\le \Phi^{-1}(y)).
\]

<a id="pdf-b53c1a5aa27d-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.99 -->
**Theorem 1.2.** For measurable \(f,g:\mathbb R^n\to[0,1]\) and \(0<\rho<1\),
\[
\mathbb E_\rho[J(f(X),g(Y);\rho)]\le J(\mathbb E f,\mathbb E g;\rho). \tag{1.2}
\]
For \(-1<\rho<0\), inequality (1.2) is reversed.

<a id="pdf-b53c1a5aa27d-p003-b006"></a>
<!-- pdf-source: page=3; block=6; confidence=0.87 -->
**Proof step.** Taking \(f=\mathbf 1_{A_1}\) and \(g=\mathbf 1_{A_2}\) recovers Theorem 1.1: \(J(1,1;\rho)=1\), \(J(1,0;\rho)=J(0,1;\rho)=0\), and the expected value on the left reduces to \(\Pr_\rho[X\in A_1,Y\in A_2]\).

<a id="pdf-b53c1a5aa27d-p003-b007"></a>
<!-- pdf-source: page=3; block=7; confidence=0.98 -->
In fact, we can also go in the other direction and prove Theorem 1.2 from Theorem 1.1: given \(f,g:\mathbb R^n\to[0,1]\), define \(A_1,A_2\subseteq\mathbb R^{n+1}\) to be the epigraphs of \(\Phi^{-1}\circ f\) and \(\Phi^{-1}\circ g\), respectively. It can be easily checked that
\[
\mathbb E_\rho J(f(X),g(Y);\rho)=\Pr_\rho(\widetilde X\in A_1,\widetilde Y\in A_2),
\]
where \(\widetilde X,\widetilde Y\) are standard Gaussian vectors on \(\mathbb R^{n+1}\) with \(\mathbb E\widetilde X_i\widetilde Y_j=\delta_{ij}\rho\). Also, \(\mathbb Ef=\gamma_{n+1}(A_1)\) and \(\mathbb Eg=\gamma_{n+1}(A_2)\). Thus the definition of \(J\) implies that \(J(\mathbb Ef,\mathbb Eg;\rho)=\Pr_\rho(\widetilde X\in B_1,\widetilde Y\in B_2)\), where \(B_1,B_2\) are parallel half-spaces with the same volumes as \(A_1,A_2\).

<a id="pdf-b53c1a5aa27d-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.96 -->
The text says the one-dimensional result implies the corresponding result in dimension $n$, then explains that the paper proves Theorem 1.2 independently to support its equality and stability analyses.

<a id="pdf-b53c1a5aa27d-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.99 -->
Introduces a characterization of equality cases in Theorem 1.2.

<a id="pdf-b53c1a5aa27d-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.99 -->
**Theorem 1.3.** For any measurable functions \(f,g:\mathbb R^n\to[0,1]\) and any \(-1<\rho<1\) with \(\rho\ne0\), if equality is attained in (1.2), then there exist \(a,b,d\in\mathbb R^n\) such that either
\[
f(x)=\Phi(\langle a,x-b\rangle)\quad\text{a.s.},\qquad g(x)=\Phi(\langle a,x-d\rangle)\quad\text{a.s.},
\]
or
\[
f(x)=1_{\{\langle a,x-b\rangle\ge0\}}\quad\text{a.s.},\qquad g(x)=1_{\{\langle a,x-d\rangle\ge0\}}\quad\text{a.s.}
\]

<a id="pdf-b53c1a5aa27d-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.91 -->
The second equality case implies that equality for the set inequality (Theorem 1.1) requires the sets to agree almost surely with parallel half-spaces.

<a id="pdf-b53c1a5aa27d-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.94 -->
Asks whether near equality in (1.2) forces $f,g$ to be close to the equality cases; states the aim of a dimension-free bound with polynomial dependence on the deficit.

<a id="pdf-b53c1a5aa27d-p004-b006"></a>
<!-- pdf-source: page=4; block=6; confidence=0.99 -->
**Theorem 1.4.** For measurable functions \(f,g:\mathbb R^n\to[0,1]\), define
\[
\delta=\delta(f,g)=J(\mathbb Ef,\mathbb Eg;\rho)-\mathbb E_\rho J(f(X),g(Y);\rho)
\]
and let
\[
m=m(f,g)=\mathbb Ef(1-\mathbb Ef)\,\mathbb Eg(1-\mathbb Eg).
\]

<a id="pdf-b53c1a5aa27d-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.99 -->
For any \(0<\rho<1\), there exist \(0<c(\rho),C(\rho)<\infty\) such that for any \(f,g:\mathbb R^n\to[0,1]\) there exist \(a,b,d\in\mathbb R^n\) such that
\[
\mathbb E|f(X)-\Phi(\langle a,X-b\rangle)|\le C(\rho)m^{c(\rho)}\delta^{\frac14\frac{(1-\rho)(1-\rho^2)}{1+3\rho}},
\]
\[
\mathbb E|g(X)-\Phi(\langle a,X-d\rangle)|\le C(\rho)m^{c(\rho)}\delta^{\frac14\frac{(1-\rho)(1-\rho^2)}{1+3\rho}}.
\]

<a id="pdf-b53c1a5aa27d-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.93 -->
The authors note that sharper constant tracking slightly improves the deficit exponent, but not past $1/4$ or its degeneration as $\rho\to1$.

<a id="pdf-b53c1a5aa27d-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.85 -->
Symmetry extends Theorem 1.4 to negative correlations: replacing $g$ by $\widetilde g=1-g$ converts correlation $\rho<0$ to $-\rho>0$, so the positive-correlation result applies and transfers back to $f,g$.

<a id="pdf-b53c1a5aa27d-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.98 -->
Examines the deterioration in Theorem 1.4 as $\rho\to1$ and motivates a sharper result when the two functions coincide.

<a id="pdf-b53c1a5aa27d-p005-b005"></a>
<!-- pdf-source: page=5; block=5; confidence=0.99 -->
For example, let
\[
f(x)=1_{\{x_1<0\}},\qquad g(x)=1_{\{x_1<2,x_2<0\ \text{or}\ x_1<1,x_2\ge0\}}.
\]
Then
\[
\Pr_\rho(f(X)=1,g(X)=0)\le\Pr_\rho(X_1<0,Y_1\ge1)\le\exp\!\left(-\frac{1}{2(1-\rho^2)}\right),
\]
which tends to zero very quickly as \(\rho\to1\). Thus \(\delta(f,g)\) tends to zero exponentially fast even though \(g\) is a constant distance away from a half-space.

<a id="pdf-b53c1a5aa27d-p005-b006"></a>
<!-- pdf-source: page=5; block=6; confidence=0.72 -->
The text says that under the restriction $f=g$, the deficit grows only on the order of $1-\rho$ as $\rho\to1$, the rate needed to recover Gaussian isoperimetric stability.

<a id="pdf-b53c1a5aa27d-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.99 -->
**Theorem 1.5.** For every \(\varepsilon>0\), there are \(\rho_0<1\) and \(C(\varepsilon)\) such that for any \(\rho_0<\rho<1\) and any \(f:\mathbb R^n\to[0,1]\) with \(\mathbb Ef=1/2\), there exists \(a\in\mathbb R^n\) such that
\[
\mathbb E|f(X)-\Phi(\langle a,X\rangle)|\le C(\varepsilon)\left(\frac{\delta(f,f)}{\sqrt{1-\rho}}\right)^{1/4-\varepsilon}.
\]

<a id="pdf-b53c1a5aa27d-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.91 -->
Using Ledoux's link between Borell's inequality and Gaussian isoperimetry, Theorem 1.5 yields the following set-stability statement.

<a id="pdf-b53c1a5aa27d-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.77 -->
**Corollary 1.6.** For each $\varepsilon>0$, there is $C_\varepsilon<\infty$ such that if $A\subseteq\mathbb R^n$ has Gaussian surface area below $1/\sqrt{2\pi}+\delta$, then some half-space $B$ satisfies $\Pr(A\triangle B)\le C_\varepsilon\delta^{1/4-\varepsilon}$.

<a id="pdf-b53c1a5aa27d-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.99 -->
**Theorem 1.7.** For every \(n\) and every \(a\in(0,1)\), there is a constant \(C(n,a)\) such that for every set \(A\subseteq\mathbb R^n\) with \(\Pr(A)=a\) and Gaussian surface area less than \(\phi(\Phi^{-1}(a))+\delta\), there is a half-space \(B\) such that
\[
\Pr(A\triangle B)\le C(n,a)\delta^{1/2}.
\]

<a id="pdf-b53c1a5aa27d-p006-b005"></a>
<!-- pdf-source: page=6; block=5; confidence=0.96 -->
Theorem 1.7 applies at all volumes and has the optimal $\delta^{1/2}$ rate, but its constant depends on dimension; Corollary 1.6 is dimension-free. The authors conjecture both advantages can hold together.

<a id="pdf-b53c1a5aa27d-p006-b006"></a>
<!-- pdf-source: page=6; block=6; confidence=0.99 -->
**Conjecture 1.8.** There are constants \(0<c,C<\infty\) such that for every \(A\subseteq\mathbb R^n\) with Gaussian surface area less than \(\phi(\Phi^{-1}(\Pr(A)))+\delta\), there is a half-space \(B\) such that
\[
\Pr(A\triangle B)\le C\Pr(A)^c\delta^{1/2}.
\]

<a id="pdf-b53c1a5aa27d-p006-b007"></a>
<!-- pdf-source: page=6; block=7; confidence=0.94 -->
Introduces a variant using $\mathbb E_\rho[f(X)f(Y)]$ in place of the indicator-set correlation probability.

<a id="pdf-b53c1a5aa27d-p006-b008"></a>
<!-- pdf-source: page=6; block=8; confidence=0.86 -->
For $0<\rho<1$, the inequality follows from Theorem 1.2, but equality occurs only when $f$ is the indicator of a half-space. A stability result for this variant follows from Theorems 1.4 and 1.5.

<a id="pdf-b53c1a5aa27d-p006-b009"></a>
<!-- pdf-source: page=6; block=9; confidence=0.99 -->
Since \(xy\le J(x,y)\) for \(0<\rho<1\), Theorem 1.2 holds when its left-hand side is replaced by \(\mathbb E_\rho f(X)f(Y)\). Equality in
\[
\mathbb E_\rho f(X)f(Y)\le J(\mathbb Ef,\mathbb Ef;\rho)
\tag{1.4}
\]
holds only when \(f\) is the indicator of a half-space.

<a id="pdf-b53c1a5aa27d-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.99 -->
**Corollary 1.9.** For any \(0<\rho<1\), there is a constant \(C(\rho)<\infty\) such that if \(f:\mathbb R^n\to[0,1]\) satisfies \(\mathbb Ef=1/2\) and
\[
\mathbb E_\rho f(X)f(Y)\ge \frac14+\frac{1}{2\pi}\arcsin(\rho)-\delta,
\]
then there is a half-space \(B\) such that
\[
\mathbb E|f(X)-1_B(X)|\le C(\rho)\delta^c,
\]
where \(c>0\) is a universal constant.

<a id="pdf-b53c1a5aa27d-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=1.00 -->
## 1.7 Discrete applications

<a id="pdf-b53c1a5aa27d-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.99 -->
For \(f:\{-1,1\}^n\to\{-1,1\}\), define the influence of coordinate \(i\) by
\[
\operatorname{Inf}_i(f)=\Pr\bigl(f(x_1,\ldots,x_n)\ne f(x_1,\ldots,x_{i-1},-x_i,x_{i+1},\ldots,x_n)\bigr),
\]
and define its noise stability by
\[
S_\rho(f)=\mathbb E_\rho f(\xi)f(\sigma),
\]
where \((\xi,\sigma)\) is chosen so that the pairs \((\xi_i,\sigma_i)\) are independent random variables with \(\mathbb E\xi_i=\mathbb E\sigma_i=0\) and \(\mathbb E_\rho\xi_i\sigma_i=\rho\).

<a id="pdf-b53c1a5aa27d-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.97 -->
The theorem is described as bounding stability of balanced low-influence functions by that of majority; the authors motivate a robust form based on their Gaussian results and the earlier proof.

<a id="pdf-b53c1a5aa27d-p007-b005"></a>
<!-- pdf-source: page=7; block=5; confidence=0.77 -->
**Theorem 1.10.** For every \(\delta>0\), there is \(\tau>0\) such that if \(f:\{−1,1\}^n\to\{−1,1\}\) satisfies \(\mathrm{Inf}_i f\le\tau\) for every \(i\), then for every \(0<\rho<1\), \(S_\rho f\le J(\mathbb Ef,\mathbb Ef;\rho)+\delta\). Moreover, if for some \(0<\rho<1\), \(S_\rho f\ge J(\mathbb Ef,\mathbb Ef;\rho)-\delta\), then there exist \(a\in\mathbb R^n\) and \(b\in\mathbb R\) such that \(\mathbb E|f(\xi)-1_{\{\langle a,\xi-b\rangle\ge0\}}|\le C_\rho\delta^c\), with universal positive \(c,C_\rho\). Equation references (1.5) and (1.6) label the stability bound and robustness conclusion, respectively.

<a id="pdf-b53c1a5aa27d-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.96 -->
The central limit theorem recovers ordinary majority as a limiting case of (1.5); (1.6) asserts that near-extremal low-influence functions are close to weighted majorities. Other variants are noted but omitted.

<a id="pdf-b53c1a5aa27d-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=1.00 -->
## 1.8 Spherical noise stability and the Max-Cut problem

<a id="pdf-b53c1a5aa27d-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.98 -->
The section introduces a spherical analogue of Gaussian noise stability for uniformly distributed pairs on the sphere with prescribed inner product \(\rho\), with applications to semidefinite rounding and Max-Cut.

<a id="pdf-b53c1a5aa27d-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.97 -->
Normalized correlated Gaussian vectors approach uniform sphere vectors as dimension grows, while their inner product concentrates near \(\rho\) rather than equaling it. Spherical harmonic methods address this discrepancy and yield Theorem 1.11.

<a id="pdf-b53c1a5aa27d-p008-b005"></a>
<!-- pdf-source: page=8; block=5; confidence=0.99 -->
For measurable \(A_1,A_2\subseteq S^{n-1}\), define
\[
\delta=\delta(A_1,A_2)=Q_\rho(X\in B_1,Y\in B_2)-Q_\rho(X\in A_1,Y\in A_2),
\]
where \(B_1,B_2\) are parallel spherical caps with the same volumes as \(A_1,A_2\), respectively. Define also
\[
m(A_1,A_2)=p(1-p)q(1-q),
\]
where \(p=\Pr(X\in A_1)\) and \(q=\Pr(Y\in A_2)\).

<a id="pdf-b53c1a5aa27d-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.99 -->
**Theorem 1.11.** Let \(0<\rho<1\), and let \(Q_\rho\) be the measure on pairs \((X,Y)\) on the sphere \(S^{n-1}\) where \(\langle X,Y\rangle=\rho\). For measurable \(A_1,A_2\subseteq S^{n-1}\), define \(\delta=Q_\rho(X\in B_1,Y\in B_2)-Q_\rho(X\in A_1,Y\in A_2)\), where \(B_1,B_2\) are parallel spherical caps with the same volumes as \(A_1,A_2\). Let \(m(A_1,A_2)=p(1-p)q(1-q)\) and \(\delta_*=\max(\delta,n^{-1/2}\log n)\). Then there exist parallel spherical caps \(B_1,B_2\) such that
\[
Q(A_1\triangle B_1),\ Q(A_2\triangle B_2)\le C(\rho)m^{c(\rho)}\delta_*^{\frac14\frac{(1-\rho)(1-\rho^2)}{1+3\rho}}.
\]

<a id="pdf-b53c1a5aa27d-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.76 -->
At \(\rho=0\), the cited result bounds the difference between joint and product probabilities by \(C/n\) for an orthogonal uniform pair. The present result concerns positively correlated pairs and gives Gaussian-like behavior; OCR does not clearly preserve all compared expressions.

<a id="pdf-b53c1a5aa27d-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.90 -->
Earlier results of Baernstein–Taylor and Beckner establish cap extremality for related noise quantities; the dimension dependence in Theorem 1.11 prevents deriving those results here.

<a id="pdf-b53c1a5aa27d-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=1.00 -->
## 1.8.1 Rounding the Goemans–Williamson algorithm

<a id="pdf-b53c1a5aa27d-p009-b005"></a>
<!-- pdf-source: page=9; block=5; confidence=0.69 -->
For a graph \(G=(V,E)\), Max-Cut seeks \(A\subset V\) maximizing the number of edges crossing \(A,V\setminus A\). A spherical embedding is a map \(f:V\to S^{n-1}\); it is optimal when \(\sum_{(u,v)\in E}\|f(u)-f(v)\|^2\) is maximal. An oblivious rounding rule is a possibly random map \(R:S^{n-1}\to\{−1,1\}\) that does not depend on \(G\).

<a id="pdf-b53c1a5aa27d-p009-b006"></a>
<!-- pdf-source: page=9; block=6; confidence=0.98 -->
We denote by \(\operatorname{Cut}(G,R)\) the expected value of the cut produced by rounding the worst possible optimal spherical embedding of \(G\):
\[
\operatorname{Cut}(G,R)=\frac12\min_f\mathbb E\sum_{(u,v)\in E}|R(f(u))-R(f(v))|,
\]
where the minimum is over all optimal embeddings \(f\).

<a id="pdf-b53c1a5aa27d-p009-b007"></a>
<!-- pdf-source: page=9; block=7; confidence=0.99 -->
If \(\operatorname{MaxCut}(G)\) denotes the maximum cut in \(G\), Goemans and Williamson showed that for \(R(x)=\operatorname{sgn}\langle X,x\rangle\), where \(X\) is a standard Gaussian vector, every graph \(G\) satisfies
\[
\operatorname{Cut}(G,R)\ge \operatorname{MaxCut}(G)\min_\theta\alpha_\theta,
\qquad \alpha_\theta=\frac{2}{\pi}\frac{\theta}{1-\cos\theta}.
\]

<a id="pdf-b53c1a5aa27d-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.99 -->
Feige and Schechtman showed that for every oblivious rounding scheme \(R\) and every \(\varepsilon>0\), there is a graph \(G\) such that
\[
\operatorname{Cut}(G,R)\le \operatorname{MaxCut}(G)\left(\varepsilon+\min_\theta\alpha_\theta\right).
\]

<a id="pdf-b53c1a5aa27d-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.99 -->
**Theorem 1.12.** Suppose \(R\) is a rounding scheme on \(S^{n-1}\) such that for every graph \(G\) with \(n\) vertices,
\[
\operatorname{Cut}(G,R)\ge \operatorname{MaxCut}(G)\left(\min_\theta\alpha_\theta-\varepsilon\right).
\]
Then there is a hyperplane rounding scheme \(\widetilde R\) such that
\[
\mathbb E|R(Y)-\widetilde R(Y)|\le C\varepsilon_*^c,
\]
where \(Y\) is a uniform random vector on \(S^{n-1}\), independent of \(R\) and \(\widetilde R\), \(C,c\) are absolute constants, and \(\varepsilon_* = \max\{\varepsilon,n^{-1/2}\log n\}.\)

<a id="pdf-b53c1a5aa27d-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.99 -->
## 1.9 Testing half-spaces

<a id="pdf-b53c1a5aa27d-p010-b004"></a>
<!-- pdf-source: page=10; block=4; confidence=0.98 -->
Suppose we have oracle access to a set \(A\subseteq\mathbb R^n\), and want an algorithm that answers “yes” with high probability if \(A\) is a half-space and answers “no” with high probability if \(\Pr(A\triangle B)>\varepsilon\) for every half-space \(B\). Theorem 1.5 gives a direct test: sample \(\varepsilon^{-4-\epsilon}\) pairs \((X_i,Y_i)\), and count the number of times \(X_i\in A\) and the number of times \(1_A(X_i)=1_A(Y_i)\). These estimate \(\Pr(A)\) and \(\Pr(X\in A,Y\in A)\), which determine whether \(A\) is close to a half-space.

<a id="pdf-b53c1a5aa27d-p010-b005"></a>
<!-- pdf-source: page=10; block=5; confidence=0.99 -->
## 1.10 Proof Techniques

<a id="pdf-b53c1a5aa27d-p010-b006"></a>
<!-- pdf-source: page=10; block=6; confidence=0.99 -->
### 1.10.1 Borell’s theorem

<a id="pdf-b53c1a5aa27d-p010-b007"></a>
<!-- pdf-source: page=10; block=7; confidence=0.95 -->
For \(t\ge 0\), the Ornstein–Uhlenbeck operator is
\[
P_t f(x)=\int_{\mathbb R^n} f\!\left(e^{-t}x+\sqrt{1-e^{-2t}}\,y\right)\,d\gamma_n(y). \tag{1.7}
\]

<a id="pdf-b53c1a5aa27d-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.86 -->
The semigroup satisfies \(P_t f\to f\) as \(t\to0\) pointwise and in \(L^p\), and \(P_t f\to\mathbb Ef\) as \(t\to\infty\). Set \(f_t=P_t f\), \(g_t=P_t g\), and \(R_t=\mathbb E_\rho J(f_t(X),g_t(Y))\) (1.8). Its endpoint limits are the two sides of (1.2); proving \(dR_t/dt\ge0\) for \(t>0\) gives Theorem 1.2.

<a id="pdf-b53c1a5aa27d-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.99 -->
### 1.10.2 The equality case

<a id="pdf-b53c1a5aa27d-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.87 -->
The derivative formula in Lemma 2.2 expresses \(dR_t/dt\) as an expectation of a strictly positive factor times
\[
\left|\nabla\Phi^{-1}(f_t)(X)-\nabla\Phi^{-1}(g_t)(Y)\right|^2,
\]
where \(|\cdot|\) is Euclidean norm. Equality in Theorem 1.2 forces this squared difference to vanish almost surely for every \(t\); the gradients are therefore almost surely a common constant. Thus \(f_t\) and \(g_t\) are \(\Phi\) composed with linear functions, and injectivity of \(P_t\) transfers the conclusion to \(f,g\).

<a id="pdf-b53c1a5aa27d-p011-b004"></a>
<!-- pdf-source: page=11; block=4; confidence=0.99 -->
### 1.10.3 Robustness

<a id="pdf-b53c1a5aa27d-p011-b005"></a>
<!-- pdf-source: page=11; block=5; confidence=0.98 -->
If \(\delta(f,g)\) is small, then \(dR_t/dt\) must also be small for most \(t>0\). Looking at the expression in Lemma 2.2, first concentrate on the main term \(|\nabla v_t(X)-\nabla w_t(Y)|^2\), where \(v_t=\Phi^{-1}\circ f_t\) and \(w_t=\Phi^{-1}\circ g_t\). Using an analogue of Poincaré’s inequality, we argue that if the expected value of this term is small, then \(v_t,w_t\) are close to linear functions. Considerable effort goes into controlling the secondary terms, using smoothness of \(P_t\), concentration of Gaussian vectors, and \(L^p\) interpolation inequalities. In the end, we show that if \(\delta=\delta(f,g)\) is small then for every \(t>0\), \(v_t\) is \(\epsilon(\delta,t)\)-close to a linear function. Since \(\Phi\) is a contraction, this implies that \(f_t\) is close to a function of the form \(\Phi(\langle x,a\rangle-b)\).

<a id="pdf-b53c1a5aa27d-p011-b006"></a>
<!-- pdf-source: page=11; block=6; confidence=0.98 -->
We would like to conclude by applying \(P_t^{-1}\), but \(P_t^{-1}\) is not a bounded operator. We work around this by arguing that it acts boundedly on the functions we care about. If \(h=1_A-1_B\), where \(B\) is a half-space, then \(\mathbb E|h|\) can be bounded in terms of \(\mathbb E|P_t h|\). This is essentially why the rates in Theorem 1.4 are polynomial, while the rates in [35] were logarithmic.

<a id="pdf-b53c1a5aa27d-p011-b007"></a>
<!-- pdf-source: page=11; block=7; confidence=0.99 -->
## 1.11 Subsequent work

<a id="pdf-b53c1a5aa27d-p011-b008"></a>
<!-- pdf-source: page=11; block=8; confidence=0.90 -->
A later proof with De establishes a four-point inequality for \(J\), tensorizes it to the discrete cube, and uses the central limit theorem to recover Borell’s inequality; this also yields cube inequalities, including a direct proof of “majority is stablest.”

<a id="pdf-b53c1a5aa27d-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.90 -->
The tensorization method gives useful cube inequalities, while the semigroup proof provides deficit control; the authors say they do not know how to derive Theorem 1.4 by the tensorization approach.

<a id="pdf-b53c1a5aa27d-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.99 -->
## 2 Proof of Borell’s theorem

<a id="pdf-b53c1a5aa27d-p012-b003"></a>
<!-- pdf-source: page=12; block=3; confidence=0.99 -->
First, define \(v_t=\Phi^{-1}\circ f_t\), \(w_t=\Phi^{-1}\circ g_t\), and \(K(x,y;\rho)=\Pr_\rho(X\le x,Y\le y)\). Then
\[
J(f_t(X),g_t(Y);\rho)=K(v_t(X),w_t(Y);\rho).
\]

<a id="pdf-b53c1a5aa27d-p012-b004"></a>
<!-- pdf-source: page=12; block=4; confidence=0.96 -->
**Lemma 2.1.** For the bivariate standard Gaussian lower-tail function \(K(x,y;\rho)\),
\[
\frac{\partial K}{\partial x}(x,y)=\phi(x)\,\Phi\!\left(\frac{y-\rho x}{\sqrt{1-\rho^2}}\right),\qquad
\frac{\partial K}{\partial y}(x,y)=\phi(y)\,\Phi\!\left(\frac{x-\rho y}{\sqrt{1-\rho^2}}\right).
\]

<a id="pdf-b53c1a5aa27d-p012-b005"></a>
<!-- pdf-source: page=12; block=5; confidence=0.89 -->
**Proof.** Write \(Y=\rho X+\sqrt{1-\rho^2}Z\), where \(X,Z\) are independent standard Gaussian vectors (in the scalar coordinates defining \(K\)). Then
\[
K(x,y)=\int_{-\infty}^{x}\phi(s)\,\Phi\!\left(\frac{y-\rho s}{\sqrt{1-\rho^2}}\right)ds.
\]
Differentiating in \(x\) gives the first formula; symmetry of \(K(x,y)\) in \(x,y\) gives the second.

<a id="pdf-b53c1a5aa27d-p012-b006"></a>
<!-- pdf-source: page=12; block=6; confidence=0.99 -->
**Lemma 2.2.**
\[
\frac{dR_t}{dt}=\frac{\rho}{2\pi\sqrt{1-\rho^2}}\,\mathbb E_\rho\!\left[\exp\!\left(-\frac{v_t^2+w_t^2-2\rho v_tw_t}{2(1-\rho^2)}\right)|\nabla v_t-\nabla w_t|^2\right].
\]

<a id="pdf-b53c1a5aa27d-p012-b007"></a>
<!-- pdf-source: page=12; block=7; confidence=0.88 -->
Lemma 2.2 implies Theorem 1.2 because its displayed derivative expression is nonnegative.

<a id="pdf-b53c1a5aa27d-p012-b008"></a>
<!-- pdf-source: page=12; block=8; confidence=0.81 -->
**Proof.** Let \(L=\Delta-\langle x,\nabla\rangle\); then \(df_t/dt=Lf_t\) for \(t\ge0\). The Gaussian integration-by-parts identity used is
\[
\mathbb E[f(X)Lg(X)]=-\mathbb E\langle\nabla f(X),\nabla g(X)\rangle. \tag{2.1}
\]

<a id="pdf-b53c1a5aa27d-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.99 -->
The first term of (2.2) is
\[
\mathbb E_\rho\!\left(\frac{K_x(v_t(X),w_t(Y))}{\phi(v_t(X))}L f_t(X)\right)=\mathbb E_\rho\!\left(\Phi\!\left(\frac{w_t(Y)-\rho v_t(X)}{\sqrt{1-\rho^2}}\right)Lf_t(X)\right).
\]
Conditioning on \(Z\) in \(Y=\rho X+\sqrt{1-\rho^2}Z\) and integrating by parts gives (2.4), while symmetry of \(K\) gives (2.5). Since
\[
\phi\!\left(\frac{w_t-\rho v_t}{\sqrt{1-\rho^2}}\right)\phi(v_t)=\frac1{2\pi}\exp\!\left(-\frac{v_t^2+w_t^2-2\rho v_tw_t}{2(1-\rho^2)}\right),
\]
substitution into (2.2) yields
\[
\frac{dR_t}{dt}=\frac{\rho}{2\pi\sqrt{1-\rho^2}}\mathbb E\exp\!\left(-\frac{v_t^2+w_t^2-2\rho v_tw_t}{2(1-\rho^2)}\right)|\nabla v_t-\nabla w_t|^2.
\]

<a id="pdf-b53c1a5aa27d-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.99 -->
Section heading: equality characterization for Theorem 1.2.

<a id="pdf-b53c1a5aa27d-p013-b003"></a>
<!-- pdf-source: page=13; block=3; confidence=0.99 -->
Lemma 2.2 gives equality when $v_t,w_t$ are linear with a common slope for every $t$. The section proves the converse and then passes to $t\to0$ to characterize $f,g$.

<a id="pdf-b53c1a5aa27d-p013-b004"></a>
<!-- pdf-source: page=13; block=4; confidence=0.99 -->
If \(f(x)=1_{\{\langle a,x-b\rangle\ge0\}}\), then a direct computation gives
\[
f_t(x)=\Phi\!\left(k_t\frac{\langle a,x-e^t b\rangle}{|a|}\right),
\qquad k_t=(e^{2t}-1)^{-1/2}.
\]

<a id="pdf-b53c1a5aa27d-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.99 -->
**Lemma 3.1.** If \(f_t(x)=\Phi(\langle a,x-b'\rangle)\) for some \(a,b'\in\mathbb R^n\) with \(|a|\le k_t\), then there exists \(b\in\mathbb R^n\) such that if \(\widetilde f(x)=1_{\{\langle a,x-b\rangle\ge0\}}\), then \(f=P_s\widetilde f\), where \(s\) solves \(|a|=k_{s+t}\).

<a id="pdf-b53c1a5aa27d-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.90 -->
To apply Lemma 3.1, the text uses a sharp pointwise gradient estimate for $\nabla v_t$, with equality for half-space indicators by (3.1).

<a id="pdf-b53c1a5aa27d-p014-b003"></a>
<!-- pdf-source: page=14; block=3; confidence=0.98 -->
**Lemma 3.2.** For $f:\mathbb R^n\to[0,1]$, $t>0$, and $x\in\mathbb R^n$, $|\nabla v_t(x)|\le 1/k_t$.

<a id="pdf-b53c1a5aa27d-p014-b004"></a>
<!-- pdf-source: page=14; block=4; confidence=0.74 -->
**Proof.** If equality holds in (1.2), nonnegativity of $dR_t/dt$ implies it vanishes for almost every $t>0$. In Lemma 2.2 all factors except $|\nabla v_t-\nabla w_t|^2$ are strictly positive; since the conditional law of $Y$ given $X$ has full support, the gradients must agree almost surely with a constant vector $a'$. Smoothness then implies $v_t(x)=\langle a,x-d'\rangle$ and $w_t(x)=\langle a,x-b'\rangle$ for some shifts. Choose $t$ with $\nabla v_t$ bounded as in Lemma 3.2. The half-space profile relation (3.1) and Lemma 3.1 imply that $f$ is one of the two forms in Theorem 1.3; the same reasoning applies to $g$. Details of the extracted parameter relations are too corrupted to recover confidently.

<a id="pdf-b53c1a5aa27d-p014-b005"></a>
<!-- pdf-source: page=14; block=5; confidence=0.99 -->
Section heading: robustness via approximation at large $t$.

<a id="pdf-b53c1a5aa27d-p014-b006"></a>
<!-- pdf-source: page=14; block=6; confidence=0.94 -->
Near equality in (1.2) makes $dR_t/dt$ small for most $t$. Lemma 2.2 is then used to show $v_t$ is nearly linear, infer that $f_t$ is near an equality profile, and use time reversal in Section 5 to transfer closeness to $f$.

<a id="pdf-b53c1a5aa27d-p014-b007"></a>
<!-- pdf-source: page=14; block=7; confidence=0.97 -->
**Proposition 4.1.** For any \(0<\rho<1\), any \(t>0\), and any \(0<\alpha<1\), there exists \(C(t,\rho)\) such that for any \(f,g\), there exist \(b,d\in\mathbb R\) and \(a\in\mathbb R^n\) with \(|a|\le k_t\) such that
\[
\mathbb E\bigl(f_t(X)-\Phi(\langle a,X-b\rangle)\bigr)^2+\mathbb E\bigl(g_t(X)-\Phi(\langle a,X-d\rangle)\bigr)^2
\le C(t,\rho)m(f,g)^{\frac{(1-\rho)^2}{8k_t^2(1+k_t)^2(1+\alpha)}}\left(\frac{\delta}{\alpha}\right)^{\frac{1}{1+4k_t^2/(1-\rho)}\frac{1}{1+\alpha}}.
\]

<a id="pdf-b53c1a5aa27d-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.81 -->
When $k_t>0$, profiles of the form $\Phi(\langle a,\cdot-b\rangle)$ can be represented as $P_t\mathbf 1_B$ for a half-space $B$. The proof of Proposition 4.1 is organized as follows: a Poincaré-type estimate gives closeness of $v_t,w_t$ to linear functions with a common slope; reverse Hölder and concentration estimates make the gradient difference small for some $p<1$; the gradient bound of Lemma 3.2 then enables the Poincaré estimate.

<a id="pdf-b53c1a5aa27d-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.99 -->
Subsection heading: a Poincaré-like inequality.

<a id="pdf-b53c1a5aa27d-p015-b003"></a>
<!-- pdf-source: page=15; block=3; confidence=0.95 -->
The equality proof used vanishing gradient difference to obtain common-slope linear functions; this subsection establishes an approximate version when the gradient difference is small.

<a id="pdf-b53c1a5aa27d-p015-b004"></a>
<!-- pdf-source: page=15; block=4; confidence=0.78 -->
**Lemma 4.2.** For smooth $v,w:\mathbb R^n\to\mathbb R$, $0<\rho<1$, and $a\in\mathbb R^n$, $$\mathbb E\bigl(v(X)-\langle X,a\rangle-\mathbb Ev\bigr)^2+\mathbb E\bigl(w(X)-\langle X,a\rangle-\mathbb Ew\bigr)^2\le \frac{1}{1-\rho}\,\mathbb E_\rho\bigl|\nabla v(X)-\nabla w(Y)\bigr|^2.$$ Equality holds when $v,w$ are quadratic polynomials differing only by a constant.

<a id="pdf-b53c1a5aa27d-p015-b005"></a>
<!-- pdf-source: page=15; block=5; confidence=0.99 -->
For a multi-index \(\alpha\in\mathbb N^n\), let \(|\alpha|=\sum_i\alpha_i\); note that \(H_\alpha\) is linear if and only if \(|\alpha|=1\). If \(\alpha_i>0\), define \(S_i\alpha\) by \((S_i\alpha)_j=\alpha_i-1\) when \(j=i\) and \((S_i\alpha)_j=\alpha_j\) when \(j\ne i\). Then
\[
\frac{\partial}{\partial x_i}H_\alpha=\begin{cases}\sqrt{\alpha_i}H_{S_i\alpha}&\text{if }\alpha_i>0,\\0&\text{if }\alpha_i=0.\end{cases}
\]

<a id="pdf-b53c1a5aa27d-p015-b006"></a>
<!-- pdf-source: page=15; block=6; confidence=0.96 -->
For $\alpha_i>0$, $\partial_{x_i}H_\alpha=\sqrt{\alpha_i}\,H_{S_i\alpha}$, and for $\alpha_i=0$ the derivative is zero. Equivalently, the displayed coefficient in (4.1) is $\sqrt{\alpha_i}$.

<a id="pdf-b53c1a5aa27d-p015-b007"></a>
<!-- pdf-source: page=15; block=7; confidence=0.99 -->
It will be convenient to reparameterize the Ornstein–Uhlenbeck semigroup \(P_t\): for \(0<\rho<1\), let \(T_\rho=P_{\log(1/\rho)}\). It is then easily checked that for any \(v\in L^1(\mathbb R^n,\gamma_n)\), \(\mathbb E_\rho(v(Y)\mid X)=(T_\rho v)(X)\).

<a id="pdf-b53c1a5aa27d-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.99 -->
The noise operator acts diagonally on the Hermite basis: \(T_\rho H_\alpha=\rho^{|\alpha|}H_\alpha\) (4.2).

<a id="pdf-b53c1a5aa27d-p016-b002"></a>
<!-- pdf-source: page=16; block=2; confidence=0.99 -->
For \(b=\sum_\alpha b_\alpha H_\alpha\) and \(c=\sum_\alpha c_\alpha H_\alpha\),
\[
\mathbb E_\rho(b(X)-c(Y))^2=\sum_\alpha\left(b_\alpha^2+c_\alpha^2-2\rho^{|\alpha|}b_\alpha c_\alpha\right).
\]
Since \(2b_\alpha c_\alpha\le b_\alpha^2+c_\alpha^2\), this is at least
\[
(b_0-c_0)^2+\sum_{|\alpha|\ge1}(b_\alpha^2+c_\alpha^2)(1-\rho^{|\alpha|})
\ge(b_0-c_0)^2+(1-\rho)\sum_{|\alpha|\ge1}(b_\alpha^2+c_\alpha^2).
\]
Applying this to the derivatives of \(v,w\), summing over \(i\), and setting \(a=\tfrac12(\mathbb E\nabla v+\mathbb E\nabla w)\) gives Lemma 4.2:
\[
\mathbb E(v(X)-\langle X,a\rangle-\mathbb Ev)^2+\mathbb E(w(X)-\langle X,a\rangle-\mathbb Ew)^2\le\frac{\mathbb E_\rho|\nabla v(X)-\nabla w(Y)|^2}{2(1-\rho)}.
\]

<a id="pdf-b53c1a5aa27d-p017-b001"></a>
<!-- pdf-source: page=17; block=1; confidence=0.98 -->
Section 4.2 derives a lower bound on \(dR_t/dt\) from Lemma 2.2 using reverse Hölder and estimates for the smoothed functions.

<a id="pdf-b53c1a5aa27d-p017-b002"></a>
<!-- pdf-source: page=17; block=2; confidence=0.99 -->
**Proposition 4.3.** For any \(0<\rho<1\) and any \(t>0\), there is a \(c(t,\rho)>0\) such that for any
\[
r\le\frac{1}{1+4k_t^2/(1-\rho)}
\]
and any \(f,g\),
\[
\frac{dR_t}{dt}\ge c(t,\rho)m^{\frac{2k_t^2(1+k_t)^2}{1-\rho}}\left(\mathbb E_\rho|\nabla v_t(X)-\nabla w_t(Y)|^{2r}\right)^{1/r}.
\]

<a id="pdf-b53c1a5aa27d-p017-b003"></a>
<!-- pdf-source: page=17; block=3; confidence=0.99 -->
The proof uses reverse Hölder, Gaussian concentration, and a comparison between the mean and median of the smoothed functions.

<a id="pdf-b53c1a5aa27d-p017-b004"></a>
<!-- pdf-source: page=17; block=4; confidence=0.99 -->
The reverse Hölder inequality states that for \(f>0\), \(g\ge0\), \(\beta>0\), and \(0<r<1\) with \(1/r-1/\beta=1\),
\[
\mathbb E fg\ge (\mathbb E f^{-\beta})^{-1/\beta}(\mathbb E g^r)^{1/r}.
\tag{4.6}
\]

<a id="pdf-b53c1a5aa27d-p017-b005"></a>
<!-- pdf-source: page=17; block=5; confidence=0.99 -->
**Lemma 4.4.** If \(f:\mathbb R^n\to\mathbb R\) is 1-Lipschitz with median \(M\), then for any \(\lambda<1\),
\[
\mathbb E\exp(\lambda f^2(X)/2)\le\frac{2}{\sqrt{1-\lambda}}\exp\!\left(\frac{\lambda}{2(1-\lambda)}M^2\right).
\]

<a id="pdf-b53c1a5aa27d-p017-b006"></a>
<!-- pdf-source: page=17; block=6; confidence=0.99 -->
**Lemma 4.5.** If \(N_t\) is a median of \(v_t\), then
\[
m(f)=\mathbb Ef(1-\mathbb Ef)\le2\exp\!\left(-\frac{N_t^2}{2(1+k_t)^2}\right).
\]

<a id="pdf-b53c1a5aa27d-p018-b001"></a>
<!-- pdf-source: page=18; block=1; confidence=0.99 -->
Recall that \(f_t=\Phi\circ v_t\), and so \(M_t=\Phi(N_t)\). If \(N_t\le0\), then \(M_t\le e^{-N_t^2/2}\) and
\[
\mathbb Ef\le2\exp\!\left(-\frac{N_t^2}{2(1+k_t)^2}\right).
\]
If \(N_t>0\), apply the preceding argument to \(1-f\) to obtain the same bound for \(\mathbb E(1-f)\). Combining these bounds proves Lemma 4.5.

<a id="pdf-b53c1a5aa27d-p018-b002"></a>
<!-- pdf-source: page=18; block=2; confidence=0.96 -->
Applying the reverse Hölder inequality (4.6) to the formula in Lemma 2.2 gives
\[
\frac{dR_t}{dt}\ge \frac{\rho}{2\pi\sqrt{1-\rho^2}}\left(\mathbb E_\rho\exp\!\left(\beta\frac{v_t^2+w_t^2-2\rho v_tw_t}{2(1-\rho^2)}\right)\right)^{-1/\beta}\left(\mathbb E_\rho|\nabla v_t-\nabla w_t|^{2r}\right)^{1/r}.
\]
Using \(2|v_tw_t|\le v_t^2+w_t^2\), Cauchy–Schwarz, and Lemma 4.4, the exponential term is bounded in terms of the medians \(M_t,N_t\). Choosing \(\beta\) with \(1/r-1/\beta=1\) and using Lemma 4.5 gives Proposition 4.3.

<a id="pdf-b53c1a5aa27d-p019-b001"></a>
<!-- pdf-source: page=19; block=1; confidence=1.00 -->
Section heading introducing the proof.

<a id="pdf-b53c1a5aa27d-p019-b002"></a>
<!-- pdf-source: page=19; block=2; confidence=0.94 -->
The proof combines Propositions 4.3 and Lemma 4.2 with Lemma 3.2. Since derivative control is known only at selected times, it first finds a nearby time where the interpolants are nearly linear, then transfers that estimate to the target time.

<a id="pdf-b53c1a5aa27d-p019-b003"></a>
<!-- pdf-source: page=19; block=3; confidence=0.97 -->
For any \(0<r<1\), Lemma 3.2 implies
\[
\left(\mathbb E_\rho|\nabla v_t-\nabla w_t|^{2r}\right)^{1/r}\ge\frac{(\mathbb E|\nabla v_t-\nabla w_t|^2)^{1/r}}{2k_t^{2(1-r)/r}}.
\]
By Lemma 4.2 applied to \(v_t,w_t\), and then Proposition 4.3, the proof bounds the linear approximation errors by an expression involving \(C(t,\rho)\), \(m(f,g)\), \(\delta\), and the auxiliary parameter \(\alpha\). Since \(\delta(f,g)=\int_0^\infty(dR_s/ds)\,ds\), it chooses \(s\in[t,t(1+\alpha)]\) with small derivative and obtains (4.12)–(4.13). Lipschitz continuity of \(\Phi\) transfers this to \(f_s,g_s\). Lemma 4.6 then transfers the estimate back to \(f_t,g_t\), completing Proposition 4.1.

<a id="pdf-b53c1a5aa27d-p019-b004"></a>
<!-- pdf-source: page=19; block=4; confidence=0.98 -->
**Lemma 4.6.** For $0<s<t$ and $h\in L^2(\mathbb R^n,\gamma_n)$,
\[
\mathbb E (P_t h)^2\le \bigl(\mathbb E(P_s h)^2\bigr)^{s/t}(\mathbb E h^2)^{1-s/t}.
\]

<a id="pdf-b53c1a5aa27d-p020-b001"></a>
<!-- pdf-source: page=20; block=1; confidence=0.99 -->
Expand \(P_s h=\sum_\alpha b_\alpha H_\alpha\). Then
\[
\mathbb E(P_s h)^2=\sum_\alpha b_\alpha^2,\quad \mathbb E(P_t h)^2=\sum_\alpha b_\alpha^2e^{2(s-t)|\alpha|},\quad \mathbb E h^2=\sum_\alpha b_\alpha^2e^{2s|\alpha|}.
\]
By Hölder’s inequality with exponents \(s/t\) and \(s/(s-t)\),
\[
\mathbb E(P_t h)^2\le(\mathbb E(P_s h)^2)^{t/s}(\mathbb E h^2)^{1-t/s}.
\]

<a id="pdf-b53c1a5aa27d-p020-b002"></a>
<!-- pdf-source: page=20; block=2; confidence=1.00 -->
Section heading introducing the time-reversal argument.

<a id="pdf-b53c1a5aa27d-p020-b003"></a>
<!-- pdf-source: page=20; block=3; confidence=0.95 -->
The section aims to show that Proposition 4.1 forces $f,g$ close to equality cases. It first handles indicator functions of sets, then extends to functions through the set/function equivalence for Borell's theorem. The time-reversal estimate relies on the geometric support separation of $1_A-1_B$ when $B$ is a half-space, which limits cancellation under $P_t$.

<a id="pdf-b53c1a5aa27d-p021-b001"></a>
<!-- pdf-source: page=21; block=1; confidence=0.99 -->
**Proposition 5.1.** Let \(B\) be a half-space and \(A\) any other set. There is an absolute constant \(C\) such that for any \(t>0\),
\[
\gamma(A\triangle B)\le C\max\left\{\mathbb E|P_t1_A-P_t1_B|,\ (e^{2t}-1)^{1/4}\sqrt{\mathbb E|P_t1_A-P_t1_B|}\right\}.
\]

<a id="pdf-b53c1a5aa27d-p021-b002"></a>
<!-- pdf-source: page=21; block=2; confidence=0.96 -->
The key lemma bounds how much of a nonnegative function supported on a half-space can be transported by $P_t$ into the complementary half-space.

<a id="pdf-b53c1a5aa27d-p021-b003"></a>
<!-- pdf-source: page=21; block=3; confidence=0.99 -->
**Lemma 5.2.** There is a constant \(c>0\) such that for any \(b\in\mathbb R\), if \(f:\mathbb R^n\to[0,1]\) is supported on \(\{x_1\le b\}\), then for any \(t>0\),
\[
\mathbb E(P_tf)1_{\{X_1\ge e^{-t}b\}}\le\max\left\{\frac12\mathbb Ef-c\frac{(\mathbb Ef)^2}{\sqrt{e^{2t}-1}},\frac38\mathbb Ef\right\}.
\]

<a id="pdf-b53c1a5aa27d-p021-b004"></a>
<!-- pdf-source: page=21; block=4; confidence=0.99 -->
Because \(P_t\) is self-adjoint,
\[
\mathbb E(P_tf)1_{\{X_1\ge e^{-t}b\}}=\mathbb E fP_t1_{\{X_1\ge e^{-t}b\}}=\mathbb E f\Phi\!\left(\frac{X_1-b}{\sqrt{e^{2t}-1}}\right).
\]
Let \(A=\{x_1\le b-\mathbb Ef\}\) and \(B=\{b-\mathbb Ef\le x_1\le b\}\). Since \(f\) is supported on \(\{x_1\le b\}\), it is supported on \(A\cup B\), and \(\mathbb E1_Bf\le\tfrac12\mathbb Ef\). Using \(\Phi(-x)\le\max\{\tfrac12-cx,\tfrac14\}\) for \(x\ge0\) gives the claimed bound.

<a id="pdf-b53c1a5aa27d-p021-b005"></a>
<!-- pdf-source: page=21; block=5; confidence=0.95 -->
**Proof.** By symmetry take $B=\{x_1\le b\}$. Let $f$ and $g$ be the positive and negative parts of $1_A-1_B$, respectively. Then $f$ is supported on $B^c$, $g$ on $B$, and $\gamma(A\triangle B)=\mathbb E f+\mathbb E g$. The proof continues beyond the supplied page.

<a id="pdf-b53c1a5aa27d-p022-b001"></a>
<!-- pdf-source: page=22; block=1; confidence=0.98 -->
Without loss of generality, \(\mathbb Ef\ge\mathbb Eg\). Lemma 5.2 implies that if \(\mathbb Ef\le C\sqrt{e^{2t}-1}\), then
\[
2\mathbb E(1_B P_tf+1_{B^c}P_tg)\le\mathbb Ef+\mathbb Eg-c\frac{(\mathbb Ef+\mathbb Eg)^2}{\sqrt{e^{2t}-1}},
\tag{5.2}
\]
while if \(\mathbb Ef\ge C\sqrt{e^{2t}-1}\), then
\[
2\mathbb E(1_B P_tf+1_{B^c}P_tg)\le\frac34\mathbb Ef+\mathbb Eg\le\frac78(\mathbb Ef+\mathbb Eg).
\tag{5.3}
\]
Consequently
\[
\mathbb E|P_tf-P_tg|\ge\min\left\{c\frac{(\mathbb Ef+\mathbb Eg)^2}{\sqrt{e^{2t}-1}},\frac18(\mathbb Ef+\mathbb Eg)\right\}.
\]
Splitting according to which term is smaller proves Proposition 5.1.

<a id="pdf-b53c1a5aa27d-p022-b002"></a>
<!-- pdf-source: page=22; block=2; confidence=0.99 -->
Section 5.1: Synchronizing the time-reversal.

<a id="pdf-b53c1a5aa27d-p022-b003"></a>
<!-- pdf-source: page=22; block=3; confidence=0.80 -->
Proposition 5.1 reduces robustness to controlling \(\mathbb E|P_t1_A-P_t1_B|^2\), but the needed estimate does not hold for arbitrary sets and times. Near-optimal noise stability of \(A\), together with Proposition 4.1 and Lemma 3.1, constrains the time parameter \(s\); explicit half-space estimates then bound the relevant differences, allowing a triangle-inequality argument and Proposition 5.1.

<a id="pdf-b53c1a5aa27d-p023-b001"></a>
<!-- pdf-source: page=23; block=1; confidence=0.99 -->
**Proposition 5.3.** For every \(t\), there is a \(C(t)\) such that the following holds. For sets \(A,A'\subseteq\mathbb R^n\), suppose \(B,B'\) are parallel half-spaces with \(\gamma(A)=\gamma(B)\), \(\gamma(A')=\gamma(B')\). If there are \(s,\epsilon_1,\epsilon_2>0\) such that
\[
\mathbb E(P_t1_A-P_{t+s}1_B)^2\le\epsilon_1^2,
\qquad \mathbb E1_A P_t1_{A'}\ge\mathbb E1_B P_t1_{B'}-\epsilon_2,
\]
then
\[
\bigl(\mathbb E(P_t1_A-P_t1_B)^2\bigr)^{1/2}\le C(t)\frac{\epsilon_1+\epsilon_2}{\bigl(I(\gamma(A))I(\gamma(A'))\bigr)^{C(t)}},
\]
where \(I(x)=\phi(\Phi^{-1}(x))\).

<a id="pdf-b53c1a5aa27d-p023-b002"></a>
<!-- pdf-source: page=23; block=2; confidence=0.95 -->
The proof separates out the estimate relating the time-shifted half-space quantities.

<a id="pdf-b53c1a5aa27d-p023-b003"></a>
<!-- pdf-source: page=23; block=3; confidence=0.99 -->
**Lemma 5.4.** For every \(t\), there is a \(C(t)\) such that for any parallel half-spaces \(B,B'\) and every \(s>0\),
\[
\bigl(\mathbb E(P_t1_B-P_{t+s}1_B)^2\bigr)^{1/2}\le C(t)\frac{\mathbb E1_B(P_t1_{B'}-P_{t+s}1_{B'})}{\bigl(I(\gamma(B))I(\gamma(B'))\bigr)^{C(t)}}.
\]

<a id="pdf-b53c1a5aa27d-p023-b004"></a>
<!-- pdf-source: page=23; block=4; confidence=0.98 -->
For a smooth function \(f:\mathbb R\to\mathbb R\), integration by parts gives
\[
\int_b^\infty\phi(x)(Lf)(x)\,dx=-f'(b)\phi(b).
\tag{5.4}
\]
Rotate coordinates so that \(B=\{x_1\le a\}\), \(B'=\{x_1\le b\}\), and let
\[
F_{ab}(t)=\mathbb E1_B P_t1_{B'}=\int_a^\infty\phi(x)\Phi\!\left(\frac{e^{-t}x-b}{\sqrt{1-e^{-2t}}}\right)dx.
\]
The subsequent derivative calculation is visible on the page and yields (5.5)–(5.6).

<a id="pdf-b53c1a5aa27d-p024-b001"></a>
<!-- pdf-source: page=24; block=1; confidence=0.99 -->
The proof rewrites
\[
\mathbb E(P_t1_B-P_{t+s}1_B)^2=(F_{aa}(2t)-F_{aa}(2t+s))-(F_{aa}(2t+s)-F_{aa}(2t+2s))
\le s(F'_{aa}(2t)-F'_{aa}(2t+2s)).
\tag{5.7}
\]
The second derivative \(F''_{aa}(t)\) is decreasing in \(t\), so
\[
\mathbb E(P_t1_B-P_{t+s}1_B)^2\le 2s^2F''_{aa}(2t).
\tag{5.8}
\]

<a id="pdf-b53c1a5aa27d-p024-b002"></a>
<!-- pdf-source: page=24; block=2; confidence=0.58 -->
Combining the upper bound with lower bounds from (5.5) and (5.6), split into \(s\le1\) and \(s>1\). For \(s\le1\), the second-derivative estimate gives the claimed inequality with a constant depending on \(t\). For \(s>1\), (5.6) supplies the needed lower bound; since \(\mathbb E|P_t1_B-P_{t+s}1_B|^2\le1\), the lemma follows after choosing \(C_t\) sufficiently large.

<a id="pdf-b53c1a5aa27d-p024-b003"></a>
<!-- pdf-source: page=24; block=3; confidence=0.99 -->
By Cauchy–Schwarz,
\[
\mathbb E1_A P_t1_A\le\mathbb E1_A P_{t+s}1_B+\epsilon_1.
\]
Since \(B\) is a super-level set of \(P_{t+s}1_B\) with the same measure as \(A\), \(\mathbb E1_A P_{t+s}1_B\le\mathbb E1_B P_{t+s}1_B\). Thus
\[
\mathbb E1_B P_t1_B-\epsilon_2\le\mathbb E1_A P_t1_A\le\mathbb E1_B P_{t+s}1_B+\epsilon_1.
\]

<a id="pdf-b53c1a5aa27d-p025-b001"></a>
<!-- pdf-source: page=25; block=1; confidence=0.99 -->
By Lemma 5.4,
\[
\bigl(\mathbb E(P_t1_B-P_{t+s}1_B)^2\bigr)^{1/2}\le C(t)(\epsilon_1+\epsilon_2).
\]
The triangle inequality then gives
\[
\bigl(\mathbb E(P_t1_A-P_t1_B)^2\bigr)^{1/2}\le\epsilon_1+C(t)(\epsilon_1+\epsilon_2).
\]

<a id="pdf-b53c1a5aa27d-p025-b002"></a>
<!-- pdf-source: page=25; block=2; confidence=0.99 -->
Section 5.2 proves Theorem 1.4.

<a id="pdf-b53c1a5aa27d-p025-b003"></a>
<!-- pdf-source: page=25; block=3; confidence=0.97 -->
Choose \(t\) by \(e^{-t}=\rho\), so \(k_t^2=\rho^2/(1-\rho^2)\). The exponent in Proposition 4.1 becomes
\[
\frac{1}{1+4\frac{\rho^2}{(1-\rho^2)(1-\rho)}}\cdot\frac{1}{1+\alpha}
=\frac{(1-\rho^2)(1-\rho)}{1-\rho+3\rho^2+\rho^3}\cdot\frac{1}{1+\alpha}.
\]
Choose \(\alpha>0\) so this equals \(\eta=(1-\rho^2)(1-\rho)/(1+3\rho)\). Proposition 4.1 and Lemma 3.1 give (5.10), with error bounded by \(C(\rho)m^{c(\rho)}\delta^\eta\). Translating the approximating half-space to match the measure and applying Proposition 5.3 with \(\epsilon_1^2=C(\rho)m^{c(\rho)}\delta^\eta\), \(\epsilon_2=\delta\), yields a bound on the smoothed indicators. Proposition 5.1 then gives \(\Pr(A\triangle B)\le C(\rho)m^{c(\rho)}\delta^{\eta/4}\).

<a id="pdf-b53c1a5aa27d-p026-b001"></a>
<!-- pdf-source: page=26; block=1; confidence=0.99 -->
For general \(f,g\), lift them to threshold sets in dimension \(n+1\):
\[
A=\{(x,x_{n+1}):x_{n+1}\ge\Phi^{-1}(f(x))\},\qquad A'=\{(x,x_{n+1}):x_{n+1}\ge\Phi^{-1}(g(x))\}.
\]
Then \(\mathbb Ef=\gamma_{n+1}(A)\), \(\mathbb Eg=\gamma_{n+1}(A')\), and the joint expectation equals the correlated probability of the lifted sets. Applying the indicator result gives a half-space \(B\) close to \(A\). We may write
\[
B=\{(x,x_{n+1})\in\mathbb R^{n+1}:x_{n+1}\ge\langle a,x\rangle-b\}
\]
for some \(a\in\mathbb R^n,b\in\mathbb R\).

<a id="pdf-b53c1a5aa27d-p026-b002"></a>
<!-- pdf-source: page=26; block=2; confidence=0.99 -->
Section 6 proves Theorem 1.5 by improving the dependence on \(\rho\) in Theorem 1.4.

<a id="pdf-b53c1a5aa27d-p026-b003"></a>
<!-- pdf-source: page=26; block=3; confidence=0.94 -->
The text identifies three improvements: control the auxiliary exponential term without a diverging \((1-\rho^2)^{-1}\) factor when the relevant differences vanish as \(\rho\to1\); replace an \(L^\infty\) gradient bound in Proposition 4.1 with an \(L^p\) bound to sharpen the \(\rho\)-rate; and use subadditivity to select larger \(t\) while keeping \(e^{-t}\) below \(\rho\).

<a id="pdf-b53c1a5aa27d-p027-b001"></a>
<!-- pdf-source: page=27; block=1; confidence=0.96 -->
**Proposition 6.1.** For any \(\alpha,t>0\), there is a constant \(C(t,\alpha)\) such that for any \(f:\mathbb R^n\to[0,1]\), there exist \(a\in\mathbb R^n,b\in\mathbb R\), with \(|a|\le k_t\), such that
\[
\mathbb E(f_t(X)-\Phi(\langle X,a\rangle-b))^2\le C(t,\alpha)m(f)^{\frac{(1+k_t)^2}{1+8k_t^2}-\alpha}\left(\frac{\delta}{\rho\sqrt{1-\rho}}\right)^{\frac{1}{1+8k_t^2}-\alpha},
\]
where \(k_t=(e^{2t}-1)^{-1/2}\), \(\delta(f)=\mathbb E_\rho J(f(X),f(Y))-J(\mathbb Ef,\mathbb Ef;\rho)\), and \(m(f)=\mathbb Ef(1-\mathbb Ef)\).

<a id="pdf-b53c1a5aa27d-p027-b002"></a>
<!-- pdf-source: page=27; block=2; confidence=0.96 -->
Section 6.1 develops an improved auxiliary-term estimate, yielding a version of Proposition 4.3 with sharper \(\rho\)-dependence.

<a id="pdf-b53c1a5aa27d-p027-b003"></a>
<!-- pdf-source: page=27; block=3; confidence=0.98 -->
**Proposition 6.2.** Let \(k_t=(e^{2t}-1)^{-1/2}\). There are constants \(0<c,C<\infty\) such that for any \(t>0\), if \(r\le1/(1+8k_t^2)\), then
\[
\frac{dR_t}{dt}\ge\frac{\rho}{\sqrt{1-\rho^2}}(c\,m(f))^{(1+k_t)^2}\left(\mathbb E_\rho|\nabla v_t(X)-\nabla v_t(Y)|^{2r}\right)^{1/r},
\]
where \(m(f)=\mathbb Ef(1-\mathbb Ef)\).

<a id="pdf-b53c1a5aa27d-p027-b004"></a>
<!-- pdf-source: page=27; block=4; confidence=0.99 -->
**Lemma 6.3.** If \(v:\mathbb R^n\to\mathbb R\) is \(L\)-Lipschitz, then
\[
\Pr_\rho\bigl(v(X)-v(Y)\ge Ls\sqrt{2(1-\rho)}\bigr)\le1-\Phi(s).
\]
In particular, if \(4\beta L^2<1\), then
\[
\mathbb E_\rho\exp\!\left(\beta\frac{(v(X)-v(Y))^2}{1-\rho}\right)\le\frac1{\sqrt{1-4\beta L^2}}.
\]

<a id="pdf-b53c1a5aa27d-p027-b005"></a>
<!-- pdf-source: page=27; block=5; confidence=0.40 -->
**Proof.** Represent \(X=(Z_1+Z_2)/\sqrt2\), \(Y=(Z_1-Z_2)/\sqrt2\), with independent standard Gaussian vectors and scaling of \(Z_2\) by the correlation parameter. Conditional on \(Z_1\), the difference as a function of \(Z_2\) is \(2L\)-Lipschitz and has median zero by oddness. This gives the tail estimate after integrating over \(Z_1\); the exponential-moment inequality follows by a standard calculation.

<a id="pdf-b53c1a5aa27d-p028-b001"></a>
<!-- pdf-source: page=28; block=1; confidence=0.98 -->
The estimate in Lemma 6.3 is used to improve the exponential bound previously used in Proposition 4.3.

<a id="pdf-b53c1a5aa27d-p028-b002"></a>
<!-- pdf-source: page=28; block=2; confidence=0.99 -->
**Lemma 6.4.** There is a constant \(C\) such that for any \(t>0\) and \(\beta>0\) with \(6\beta k_t^2\le1\),
\[
\mathbb E_\rho\exp\!\left(\beta\frac{v_t(X)^2+v_t(Y)^2-2\rho v_t(X)v_t(Y)}{2(1-\rho^2)}\right)\le C e^{M_t^2/2},
\]
where \(M_t\) is a median of \(v_t\).

<a id="pdf-b53c1a5aa27d-p028-b003"></a>
<!-- pdf-source: page=28; block=3; confidence=0.99 -->
By Cauchy–Schwarz, the expectation in Lemma 6.4 splits into the product of the two expectations displayed in (6.1). Lemma 6.3 bounds the first factor by \(\sqrt2\) when \(8\beta k_t^2\le1\), and Lemma 4.4 bounds the second by \(C e^{M_t^2/2}\).

<a id="pdf-b53c1a5aa27d-p028-b004"></a>
<!-- pdf-source: page=28; block=4; confidence=0.99 -->
Applying Lemma 6.4 in the proof of Proposition 4.3 gives
\[
\frac{dR_t}{dt}\ge c\frac{\rho}{\sqrt{1-\rho^2}}e^{M_t^2/2}\left(\mathbb E_\rho|\nabla v_t(X)-\nabla v_t(Y)|^{2r}\right)^{1/r}.
\]
Lemma 4.5 gives \(e^{M_t^2/2}\ge(c\,m(f))^{(1+k_t)^2}\), yielding the claimed bound.

<a id="pdf-b53c1a5aa27d-p028-b005"></a>
<!-- pdf-source: page=28; block=5; confidence=0.99 -->
## 6.2 Higher moments of $\lvert\nabla v_t(X)-\nabla v_t(Y)\rvert$

<a id="pdf-b53c1a5aa27d-p028-b006"></a>
<!-- pdf-source: page=28; block=6; confidence=0.96 -->
This section develops an upper bound for arbitrary moments of the gradient difference, using a Hessian moment estimate and a Gaussian comparison result.

<a id="pdf-b53c1a5aa27d-p028-b007"></a>
<!-- pdf-source: page=28; block=7; confidence=0.99 -->
**Proposition 6.5.** There is a constant \(C\) such that for any \(t>0\) and any \(1\le q<\infty\),
\[
\left(\mathbb E_\rho|\nabla v_t(X)-\nabla v_t(Y)|^q\right)^{1/q}\le Ck_t^2\sqrt{q(1-\rho)}\left((1+k_t)\sqrt{\log(1/m(f))}+\sqrt{qk_t}\right).
\]

<a id="pdf-b53c1a5aa27d-p028-b008"></a>
<!-- pdf-source: page=28; block=8; confidence=0.90 -->
For fixed $q,t$, the proposition is intended to give the appropriate dependence on $\rho$ as $\rho\to1$, unlike a uniform bound. Its proof uses a Hessian moment estimate from [35] and Pinelis’s result [38]; $\lVert\cdot\rVert_F$ denotes the Frobenius norm.

<a id="pdf-b53c1a5aa27d-p029-b001"></a>
<!-- pdf-source: page=29; block=1; confidence=0.99 -->
**Proposition 6.6.** Let \(Hv_t\) denote the Hessian matrix of \(v_t\). There is a constant \(C\) such that for all \(t>0\) and \(1\le q<\infty\),
\[
\left(\mathbb E\|Hv_t\|_F^q\right)^{1/q}\le Ck_t^2\left((1+k_t)\sqrt{\log\frac1{m(f)}}+\sqrt q\,k_t\right).
\]

<a id="pdf-b53c1a5aa27d-p029-b002"></a>
<!-- pdf-source: page=29; block=2; confidence=0.86 -->
**Proposition 6.7.** Let $h:\mathbb R^n\to\mathbb R^k$ be $C^1$, with derivative matrix $Dh$. For independent standard Gaussian vectors $Z_1,Z_2\in\mathbb R^n$ and every $1\le q<\infty$, $$\left(\mathbb E\lVert h(Z_1)-h(Z_2)\rVert^q\right)^{1/q}\le C\left(\mathbb E\lVert Dh\rVert_F^q\right)^{1/q},$$ where $C$ is universal.

<a id="pdf-b53c1a5aa27d-p029-b003"></a>
<!-- pdf-source: page=29; block=3; confidence=0.72 -->
**Proof.** Define $f:\mathbb R^{2n}\to\mathbb R^k$ by $f(Z_1,Z_2)=h(Z_1)-h(Z_2)$, so $\mathbb Ef=0$. Pinelis’s inequality for convex $\Psi$ bounds $\mathbb E\Psi(f(Z))$ by a constant times $\mathbb E\Psi(Df(Z)\cdot\widetilde Z)$, where $\widetilde Z$ is an independent copy. Choose $\Psi(x)=\lVert x\rVert^q$. Conditional on $Z_1$, the Gaussian linear-map moment bound controls the latter by $C^q\mathbb E\lVert Dh(Z_1)\rVert_F^q$, yielding the claim.

<a id="pdf-b53c1a5aa27d-p029-b004"></a>
<!-- pdf-source: page=29; block=4; confidence=0.90 -->
**Proof of Proposition 6.5.** Let $Z,Z_1,Z_2$ be independent standard Gaussians and set $X=\sqrt\rho Z+\sqrt{1-\rho}Z_1$, $Y=\sqrt\rho Z+\sqrt{1-\rho}Z_2$. Conditional on $Z$, apply Proposition 6.7 to $h(x)=\nabla v_t(\sqrt\rho Z+\sqrt{1-\rho}x)$. Its derivative is $Dh(x)=\sqrt{1-\rho}\,H_{v_t}(\sqrt\rho Z+\sqrt{1-\rho}x)$. Integrate over $Z$, take the $q$th root, and use Proposition 6.6 to bound the Hessian moment.

<a id="pdf-b53c1a5aa27d-p029-b005"></a>
<!-- pdf-source: page=29; block=5; confidence=0.94 -->
With Propositions 6.2 and 6.5 established, the proof of Proposition 6.1 follows the strategy of Proposition 4.1.

<a id="pdf-b53c1a5aa27d-p030-b001"></a>
<!-- pdf-source: page=30; block=1; confidence=0.95 -->
For a nonnegative random variable \(Z\), Hölder’s inequality gives
\[
\mathbb EZ^2\le(\mathbb EZ^{2r})^{\gamma/(2r)}(\mathbb EZ^{2r(2-\gamma)/(2r-\gamma)})^{(2r-\gamma)/(2r)}.
\tag{6.2}
\]
Set \(Z=|\nabla v_t(X)-\nabla v_t(Y)|\). Lemma 4.2 and Proposition 6.5 bound the right side in terms of the approximation error. Choosing \(\eta=8k_t^2/(1+8k_t^2)\), \(r=1-\eta\), and \(\gamma=2r-\alpha\eta\) for \(0<\alpha<1\), then combining with Proposition 6.2, gives (6.3).

<a id="pdf-b53c1a5aa27d-p031-b001"></a>
<!-- pdf-source: page=31; block=1; confidence=0.98 -->
Since \(\delta=\int_0^\infty dR_s/ds\,ds\), for any \(\alpha,t>0\) there is \(s\in[t,t(1+\alpha)]\) such that \((dR_s/ds)\le\delta/(\alpha t)\). Applying (6.3) at \(s\), and then Lemma 4.6 and the contraction property of \(\Phi\), yields the claimed estimate. Finally, Lemma 3.2 gives \(|\mathbb E\nabla v_s|\le k_s\), so the approximating profile has the form \(\Phi(\langle X,a\rangle-b)\) with \(|a|\le k_t\).

<a id="pdf-b53c1a5aa27d-p031-b002"></a>
<!-- pdf-source: page=31; block=2; confidence=0.99 -->
Section 6.3 develops a comparison across correlation parameters to improve the use of Lemma 5.4 in proving Theorem 1.5.

<a id="pdf-b53c1a5aa27d-p031-b003"></a>
<!-- pdf-source: page=31; block=3; confidence=0.94 -->
For an indicator \(f=1_A\), Theorem 1.5 assumes that the noise correlation at \(\rho\) is near its half-space maximum. Applying Lemma 5.4 directly at that parameter gives poor dependence on \(\rho\); the section seeks to transfer near-optimality to larger correlations.

<a id="pdf-b53c1a5aa27d-p031-b004"></a>
<!-- pdf-source: page=31; block=4; confidence=0.86 -->
**Proposition 6.8.** Suppose \(A\subseteq\mathbb R^n\), \(\Pr(A)=1/2\), and \(\theta=\cos(k^{-1}\cos^{-1}\rho)\) for some \(k\in\mathbb N\). If \(J(1/2,1/2;\rho)-\mathbb E[J(1_A(X),1_A(Y);\rho)]\le\delta\), where \((X,Y)\) are standard Gaussians with correlation \(\rho\), then \(J(1/2,1/2;\theta)-\mathbb E[J(1_A(X),1_A(Y);\theta)]\le k\delta\).

<a id="pdf-b53c1a5aa27d-p031-b005"></a>
<!-- pdf-source: page=31; block=5; confidence=0.98 -->
Let \(Z_1,Z_2\) be independent standard Gaussian vectors and define \(Z(\gamma)=Z_1\cos\gamma+Z_2\sin\gamma\). For any \(\gamma\) and integer \(j\), \(Z((j+1)\gamma)\) and \(Z(j\gamma)\) have correlation \(\cos\gamma\). If \(\gamma=\cos^{-1}(\rho)\), the union bound gives
\[
\Pr_\theta(X\in A,Y\notin A)\le\sum_{j=0}^{k-1}\Pr_\rho(X\in A,Y\notin A)=k\Pr_\rho(X\in A,Y\notin A),
\tag{6.4}
\]
where \(\theta=\cos(k\cos^{-1}\rho)\).

<a id="pdf-b53c1a5aa27d-p032-b001"></a>
<!-- pdf-source: page=32; block=1; confidence=0.83 -->
The hypothesis can be rewritten as a bound on the difference between \(\Pr_\rho(X\in A,Y\in A)\) and the corresponding half-space probability. Combining this with (6.4) gives the same deficit at correlation \(\theta\) bounded by \(k\delta\), proving the proposition.

<a id="pdf-b53c1a5aa27d-p032-b002"></a>
<!-- pdf-source: page=32; block=2; confidence=0.96 -->
The proposition requires \(\Pr(A)=1/2\) and integer \(k\). These restrictions arise from the subadditivity argument (6.4), which is stated to be sharp for half-spaces of measure \(1/2\).

<a id="pdf-b53c1a5aa27d-p032-b003"></a>
<!-- pdf-source: page=32; block=3; confidence=0.99 -->
**Conjecture 6.9.** There is a function \(k(\rho,a)\) such that for fixed \(a\in(0,1)\), \(k(\rho,a)\sim\sqrt{1-\rho}\) as \(\rho\to1\), and \(k(\rho,a)\sim\rho\) as \(\rho\to0\); and for any \(a\in(0,1)\) and any \(A\subseteq\mathbb R^n\),
\[
\frac{J(a,a;\rho)-\mathbb E_\rho J(1_A(X),1_A(Y);\rho)}{k(\rho,a)}
\]
is increasing in \(\rho\).

<a id="pdf-b53c1a5aa27d-p032-b004"></a>
<!-- pdf-source: page=32; block=4; confidence=0.94 -->
If true, the conjecture would transfer approximate optimality at a given correlation to smaller correlations, with \(k(\rho,a)\) controlling the deficit.

<a id="pdf-b53c1a5aa27d-p032-b005"></a>
<!-- pdf-source: page=32; block=5; confidence=0.99 -->
Fix \(\varepsilon>0\). If \(\rho_0\) is close enough to 1, then for every \(\rho_0<\rho<1\), there is a \(k\in\mathbb N\) such that
\[
k\cos^{-1}(\rho)\in[\pi/2-\varepsilon,\pi/2+\varepsilon].
\]
In particular, \(\cos(k\cos^{-1}(\rho))\in[c_1(\varepsilon),c_2(\varepsilon)]\), where \(c_1(\varepsilon),c_2(\varepsilon)\to0\) as \(\varepsilon\to0\), and \(k\le C(\varepsilon)/\sqrt{1-\rho}\).

<a id="pdf-b53c1a5aa27d-p033-b001"></a>
<!-- pdf-source: page=33; block=1; confidence=0.99 -->
Let \(\theta=\cos(k\cos^{-1}(\rho))\). Proposition 6.8 gives
\[
J(1/2,1/2;\theta)-\mathbb E_\theta J(1_A(X),1_A(Y);\theta)\le k\delta\le C(\varepsilon)\frac{\delta}{\sqrt{1-\rho}}.
\]
Applying Proposition 6.1 with correlation \(\theta\) and \(t=\log(1/\theta)\) yields an affine Gaussian profile and the estimate (6.5).

<a id="pdf-b53c1a5aa27d-p033-b002"></a>
<!-- pdf-source: page=33; block=2; confidence=0.98 -->
The time-reversal argument and Lemma 3.1 give \(s>0\) and a half-space \(B\) such that
\[
\mathbb E(P_t1_A-P_{t+s}1_B)^2\le C(\varepsilon)\left(\frac{\delta}{\sqrt{1-\rho}}\right)^{1-c_4(\varepsilon)}.
\]
Adjust \(B\) so that \(\Pr(B)=\Pr(A)\). Proposition 5.3 and then Proposition 5.1 give
\[
\Pr(A\triangle B)\le C(\varepsilon)\left(\frac{\delta}{\sqrt{1-\rho}}\right)^{(1/4-c_4(\varepsilon))/4}.
\]

<a id="pdf-b53c1a5aa27d-p033-b003"></a>
<!-- pdf-source: page=33; block=3; confidence=0.99 -->
**Proof of Corollary 1.9.** Since \(xy\le J(x,y)\), the hypothesis implies
\[
\mathbb E J(f(X),f(Y))\ge\frac14+\frac{1}{2\pi}\arcsin(\rho)-\delta.
\]
Apply Theorem 1.5 when \(\rho>\rho_0\), and otherwise Theorem 1.4. In either case, there is \(a\in\mathbb R^n\) such that
\[
\mathbb E|f(X)-\Phi(\langle X,a\rangle)|\le C(\rho)\delta^c.
\]

<a id="pdf-b53c1a5aa27d-p033-b004"></a>
<!-- pdf-source: page=33; block=4; confidence=0.78 -->
Let \(g(x)=\Phi(\langle x,a\rangle)\). Hölder's inequality and the approximation bound compare \(\mathbb E[g(X)g(Y)]\) with \(\mathbb E[f(X)f(Y)]\), leading to inequality (6.6): \(\mathbb E[g(X)g(Y)]+1/(2\pi)\ge \tfrac14+(1/(2\pi))\arcsin\rho-\delta-C_\rho\delta^c\).

<a id="pdf-b53c1a5aa27d-p034-b001"></a>
<!-- pdf-source: page=34; block=1; confidence=0.99 -->
If \(|a|=(e^{2t}-1)^{-1/2}\) and \(A=\{x\in\mathbb R^n:x_1\le0\}\), then
\[
\mathbb Eg(X)g(Y)=\mathbb EP_t1_A(X)P_t1_A(Y)=\mathbb E1_A(X)P_{2t-\log(\rho)}1_A(X)=\frac14+\frac{1}{2\pi}\arcsin(e^{-2t}\rho)
\le\frac14+\frac{1}{2\pi}\arcsin(\rho)-\frac{1}{2\pi}\rho(1-e^{-2t}).
\]
Combining this with (6.6) gives \(1-e^{-2t}\le C(\rho)\delta^c\).

<a id="pdf-b53c1a5aa27d-p034-b002"></a>
<!-- pdf-source: page=34; block=2; confidence=0.99 -->
On the other hand,
\[
\mathbb E|g-1_A|=2\left(\frac12-\mathbb Eg1_A\right)=\frac12-\frac1\pi\arcsin(e^{-t})\le\sqrt{1-e^{-2t}}.
\]
Together with the preceding bound and the triangle inequality, this gives \(\mathbb E|f-1_A|\le C(\rho)\delta^c\).

<a id="pdf-b53c1a5aa27d-p034-b003"></a>
<!-- pdf-source: page=34; block=3; confidence=0.99 -->
Section heading introducing the proof of Theorem 1.10.

<a id="pdf-b53c1a5aa27d-p034-b004"></a>
<!-- pdf-source: page=34; block=4; confidence=0.99 -->
For \(S\subseteq[n]\), define \(\chi_S:\{-1,1\}^n\to\{-1,1\}\) by \(\chi_S(x)=\prod_{i\in S}x_i\). The functions \(\{\chi_S:S\subseteq[n]\}\) form an orthonormal basis of \(L_2(\{-1,1\}^n)\). We write \(\widehat f_S\) for the coefficients of \(f\):
\[
f(x)=\sum_{S\subseteq[n]}\widehat f_S\chi_S(x).
\tag{7.1}
\]
The Bonami–Beckner semigroup is defined by \((Q_tf)(\xi)=\mathbb E_{e^{-t}}(f(\sigma)\mid\xi)\).

<a id="pdf-b53c1a5aa27d-p034-b005"></a>
<!-- pdf-source: page=34; block=5; confidence=0.98 -->
Subsection introducing the invariance principle.

<a id="pdf-b53c1a5aa27d-p034-b006"></a>
<!-- pdf-source: page=34; block=6; confidence=0.82 -->
Extend a function on \(\{-1,1\}^n\) to \(\mathbb R^n\) by its Fourier polynomial \(g(x)=\sum_{S\subseteq[n]}\widehat f_S\chi_S(x)\). This multilinear extension agrees with \(f\) on the cube.

<a id="pdf-b53c1a5aa27d-p035-b001"></a>
<!-- pdf-source: page=35; block=1; confidence=0.68 -->
For multilinear polynomials, expectations under the correlated cube pair \((\xi,\sigma)\) agree with those under the corresponding correlated Gaussian pair \((X,Y)\). Also, the discrete and Gaussian noise operators agree on multilinear polynomials, so either notation \(f_t\) can be used.

<a id="pdf-b53c1a5aa27d-p035-b002"></a>
<!-- pdf-source: page=35; block=2; confidence=0.58 -->
Although the multilinear extension and the cube function may have different distributions, the invariance principle of [36] compares them for low-influence functions. The text introduces truncation \(\bar f\) of a real-valued function to \([0,1]\), with values clipped below 0 and above 1.

<a id="pdf-b53c1a5aa27d-p035-b003"></a>
<!-- pdf-source: page=35; block=3; confidence=0.98 -->
**Theorem 7.1.** Suppose \(f\) is a multilinear polynomial such that \(f(\xi)\in[0,1]\) for all \(\xi\in\{-1,1\}^n\). If \(f\) satisfies \(\max_i\operatorname{Inf}_i(f)\le\tau\), then for any \(\eta>0\),
\[
\mathbb E(f_\eta(X)-\overline{f_\eta}(X))^2\le C\tau^{c\eta},
\tag{7.2}
\]
where \(\overline f\) is the truncation of \(f\) to \([0,1]\).

<a id="pdf-b53c1a5aa27d-p035-b004"></a>
<!-- pdf-source: page=35; block=4; confidence=0.99 -->
Using (7.2) and the triangle inequality, for any \(0<\rho'<1\),
\[
\mathbb E_{\rho'}f_\eta(X)f_\eta(Y)\le\mathbb E_{\rho'}\overline{f_\eta}(X)\overline{f_\eta}(Y)+C\tau^{c\eta}.
\tag{7.3}
\]
Also,
\[
\mathbb E_{\rho'}f_\eta(X)f_\eta(Y)=\mathbb E_{e^{-2\eta}\rho'}f(\xi)f(\sigma).
\tag{7.4}
\]

<a id="pdf-b53c1a5aa27d-p035-b005"></a>
<!-- pdf-source: page=35; block=5; confidence=0.99 -->
Applying Corollary 1.9 to \(\overline{f_\eta}\) gives \(a,b\in\mathbb R^n\) such that
\[
\mathbb E\left(\overline{f_\eta}(X)-1_{\{\langle a,X-b\rangle\ge0\}}\right)^2\le C(\rho)(\eta+\tau^{c\eta}+\delta)^c.
\]
By (7.2) and the triangle inequality, we may replace \(\overline{f_\eta}\) by \(f_\eta\):
\[
\mathbb E\left(f_\eta(X)-1_{\{\langle a,X-b\rangle\ge0\}}\right)^2\le C(\rho)(\eta+\tau^{c\eta}+\delta)^c.
\tag{7.5}
\]

<a id="pdf-b53c1a5aa27d-p035-b006"></a>
<!-- pdf-source: page=35; block=6; confidence=0.77 -->
Equation (7.5) is the Gaussian approximation by a half-space that the next page transfers to the discrete cube.

<a id="pdf-b53c1a5aa27d-p036-b001"></a>
<!-- pdf-source: page=36; block=1; confidence=0.94 -->
The proof next transfers (7.5) from Gaussian input to cube input using Theorem 7.1; it first establishes that the half-space normal can be chosen with small maximum coordinate.

<a id="pdf-b53c1a5aa27d-p036-b002"></a>
<!-- pdf-source: page=36; block=2; confidence=0.99 -->
**Lemma 7.2.** There is an \(a\in\mathbb R^n\) satisfying (7.5) with \(\sum_i a_i^2=1\) and \(\max_i|a_i|\le C\tau^c\).

<a id="pdf-b53c1a5aa27d-p036-b003"></a>
<!-- pdf-source: page=36; block=3; confidence=0.99 -->
**Lemma 7.3.** Let \(g^{a,b}\) be the multilinear extension of the function \(x\mapsto1_{\{\langle a,x-b\rangle\ge0\}}\). If \(\sum_i a_i^2=1\) and \(\max_i|a_i|\le\tau\), then for any \(\eta>0\),
\[
\mathbb E(g^{a,b}_\eta(X)-1_{\{\langle a,X-b\rangle\ge0\}})^2\le C(\eta+\tau^{c\eta}).
\]

<a id="pdf-b53c1a5aa27d-p036-b004"></a>
<!-- pdf-source: page=36; block=4; confidence=0.97 -->
From Lemma 7.3 and the triangle inequality,
\[
\mathbb E(f_\eta(X)-g^{a,b}_\eta(X))^2\le C(\rho)(\eta+\tau^{c\eta}+\delta)^c.
\]
Since \(f_\eta-g^{a,b}_\eta\) is multilinear, its second moment is unchanged when \(X\) is replaced by \(\xi\). The half-space indicator extension also satisfies \(\mathbb E(g^{a,b}_\eta(\xi)-g^{a,b}(\xi))^2\le C(\eta+\tau^{c\eta})\). Thus \(\mathbb E(f_\eta(\xi)-g^{a,b}(\xi))^2\le C(\rho)(\eta+\tau^{c\eta}+\delta)^c\).

<a id="pdf-b53c1a5aa27d-p036-b005"></a>
<!-- pdf-source: page=36; block=5; confidence=0.94 -->
A final lemma relates closeness of a smoothed function to an indicator to closeness of the original function to that indicator.

<a id="pdf-b53c1a5aa27d-p036-b006"></a>
<!-- pdf-source: page=36; block=6; confidence=0.76 -->
**Lemma 7.4.** For \(f,g:\{-1,1\}^n\to[0,1]\) and \(\eta>0\), \(\mathbb E_\xi[(f(\xi)-g(\xi))^2]\le C\,\mathbb E_\xi[(f_\eta(\xi)-g(\xi))^2]\).

<a id="pdf-b53c1a5aa27d-p036-b007"></a>
<!-- pdf-source: page=36; block=7; confidence=0.65 -->
Applying Lemma 7.4 to the preceding cube estimate yields \(\mathbb E_\xi[(f(\xi)-g_{a,b}(\xi))^2]\le C_\rho(\eta+\tau c_\eta+\delta)^c\). Choosing \(\tau\) and \(\eta\) sufficiently small relative to \(\delta\) completes Theorem 1.10, pending Lemmas 7.2–7.4.

<a id="pdf-b53c1a5aa27d-p036-b008"></a>
<!-- pdf-source: page=36; block=8; confidence=0.98 -->
Subsection where the lemmas from the preceding section are proved.

<a id="pdf-b53c1a5aa27d-p036-b009"></a>
<!-- pdf-source: page=36; block=9; confidence=0.94 -->
For a Gaussian half-space, the expectation of coordinate \(X_i\) times its indicator is proportional to \(a_i\); this observation is attributed to [34].

<a id="pdf-b53c1a5aa27d-p036-b010"></a>
<!-- pdf-source: page=36; block=10; confidence=0.99 -->
**Lemma 7.5.**
\[
\mathbb E X_i1_{\{\langle a,X-b\rangle\ge0\}}=a_i\phi(\langle a,b\rangle).
\]

<a id="pdf-b53c1a5aa27d-p037-b001"></a>
<!-- pdf-source: page=37; block=1; confidence=0.99 -->
Write \(e_i=a_i a+a_i^\perp\), where \(a_i^\perp\perp a\). Since \(\langle X,a_i^\perp\rangle\) is independent of \(\langle X,a\rangle\),
\[
\mathbb EX_i1_{\{\langle a,X-b\rangle\ge0\}}=a_i\mathbb E\langle a,X\rangle1_{\{\langle a,X\rangle\ge\langle a,b\rangle\}}=a_i\phi(\langle a,b\rangle),
\]
by rotational invariance and one-dimensional integration by parts.

<a id="pdf-b53c1a5aa27d-p037-b002"></a>
<!-- pdf-source: page=37; block=2; confidence=0.97 -->
A half-space close to a low-influence function must itself have small coordinate influences; perturbing its normal vector can reduce them while keeping the approximation error small.

<a id="pdf-b53c1a5aa27d-p037-b003"></a>
<!-- pdf-source: page=37; block=3; confidence=0.98 -->
Suppose \(f\) has influences bounded by \(\tau\), and
\[
\mathbb E(f(X)-1_{\{\langle a,X-b\rangle\ge0\}})^2\le\gamma.
\tag{7.7}
\]
The proof shows there is \(\bar a\) with \(\sum_i\bar a_i^2=1\), \(\max_i|\bar a_i|\le C\tau^{1/3}\), and
\[
\mathbb E(f(X)-1_{\{\langle\bar a,X-b\rangle\ge0\}})^2\le\gamma^c.
\tag{7.8}
\]

<a id="pdf-b53c1a5aa27d-p037-b004"></a>
<!-- pdf-source: page=37; block=4; confidence=0.99 -->
By orthonormality of the coordinates and Lemma 7.5,
\[
\mathbb E(f(X)-1_{\{\langle a,X-b\rangle\ge0\}})^2\ge\sum_i\left(\mathbb EX_if(X)-\mathbb EX_i1_{\{\langle a,X-b\rangle\ge0\}}\right)^2
=\sum_i(\widehat f_{\{i\}}-a_i\kappa_{a,b})^2,
\tag{7.9}
\]
where \(\kappa_{a,b}=\phi(\langle a,b\rangle)\). For indices with \(|a_i|\kappa_{a,b}\ge C\tau\), this gives
\[
\gamma\ge c\kappa_{a,b}^2\sum_{i:\,|a_i|\kappa_{a,b}\ge C\tau}a_i^2.
\tag{7.10}
\]

<a id="pdf-b53c1a5aa27d-p037-b005"></a>
<!-- pdf-source: page=37; block=5; confidence=0.52 -->
For small $\kappa_{a,b}$, the half-space measure is bounded in terms of $\gamma$ and $\kappa_{a,b}$, which establishes (7.8). For large $\kappa_{a,b}$, (7.10) bounds the squared norm on coordinates above a threshold; truncating $a$ outside those coordinates and renormalizing yields the desired nearby normal vector.

<a id="pdf-b53c1a5aa27d-p037-b006"></a>
<!-- pdf-source: page=37; block=6; confidence=0.98 -->
The next claim is that the linear extension of a low-influence half-space is close to a half-space; this need not hold for arbitrary half-spaces, as the linear extension of $\mathbf 1_{\{x_1\ge0\}}$ is $x_1$.

<a id="pdf-b53c1a5aa27d-p038-b001"></a>
<!-- pdf-source: page=38; block=1; confidence=0.98 -->
Let \(g\) be the multilinear extension of \(1_{\{\langle a,x-b\rangle\ge0\}}\), and let \(h(x)=\langle a,x-b\rangle\). The Berry–Esseen theorem gives, for any \(M>0\),
\[
\mathbb Eg(\xi)h(\xi)=\int_{\langle a,b\rangle}^\infty\Pr(\langle a,x\rangle\ge t)\,dt-CM\tau-Ce^{-M^2/2}.
\]
Choosing \(M=\sqrt{\log(1/\tau)}\) gives (7.11).

<a id="pdf-b53c1a5aa27d-p038-b002"></a>
<!-- pdf-source: page=38; block=2; confidence=0.98 -->
Let \(m(X)=1_{\{\langle a,X-b\rangle\ge0\}}-\overline g_\eta(X)\), and take \(\epsilon=\mathbb E|m|\). When \(m\ne0\), \(m\) and \(h\) have the same sign. Let \(A=\{x:|\langle a,x-b\rangle|\in[-\epsilon/2,\epsilon/2]\}\). Then \(\Pr(A)\le\epsilon/2\), so \(\mathbb E|m|1_{A^c}\ge\epsilon/2\). On \(A^c\), \(|h(x)|\ge\epsilon/2\), and hence \(\mathbb Em(X)h(X)\ge\epsilon^2/4\). This, combined with (7.12), bounds \(\epsilon\).

<a id="pdf-b53c1a5aa27d-p039-b001"></a>
<!-- pdf-source: page=39; block=1; confidence=0.97 -->
Applying this to (7.12) yields \(\epsilon\le C(\eta+\tau^{c\eta})^c\). Thus
\[
\mathbb E|1_{\{\langle a,X-b\rangle\ge0\}}-\overline g_\eta(X)|\le C(\eta+\tau^{c\eta})^c.
\]
Changing the first moment to a second-moment bound and using (7.2) to replace \(\overline g_\eta\) by \(g_\eta\) completes the proof. The statement also holds with \(g\) in place of \(g_\eta\).

<a id="pdf-b53c1a5aa27d-p039-b002"></a>
<!-- pdf-source: page=39; block=2; confidence=0.98 -->
Suppose \(f,g:\{-1,1\}^n\to[-1,1]\). Let \(\epsilon=\mathbb E(f_\eta(\xi)-g(\xi))^2\). Since \(g\) takes values in \(\{-1,1\}\), \(\mathbb Eg^2=1\), so the triangle inequality gives \(\mathbb Ef_\eta^2\ge1-2\epsilon\). Also, \(\mathbb Ef^2\le1\), and Parseval gives
\[
\mathbb E(f-f_\eta)^2=\sum_{S\subseteq[n]}\widehat f_S^2(1-e^{-\eta|S|})^2\le\sum_{S\subseteq[n]}\widehat f_S^2(1-e^{-\eta|S|})=\mathbb Ef^2-\mathbb Ef_\eta^2\le2\epsilon.
\]
The triangle inequality then gives \(\mathbb E(f-g)^2\le C\epsilon\).

<a id="pdf-b53c1a5aa27d-p039-b003"></a>
<!-- pdf-source: page=39; block=3; confidence=1.00 -->
## 8 Spherical noise stability

<a id="pdf-b53c1a5aa27d-p039-b004"></a>
<!-- pdf-source: page=39; block=4; confidence=0.82 -->
For $A\subseteq S^{n-1}$, its radial extension is $\bar A=\{x\in\mathbb R^n:x\ne0,\ x/\|x\|\in A\}$. Gaussian spherical symmetry gives $\Pr[Q_\rho(A_1,A_2)]=\Pr_\rho(\bar A_1,\bar A_2)$.

<a id="pdf-b53c1a5aa27d-p039-b005"></a>
<!-- pdf-source: page=39; block=5; confidence=0.99 -->
**Lemma 8.1.** For any half-space \(H=\{x\in\mathbb R^n:\langle a,x\rangle\le b\}\), there is a spherical cap \(B=\{x\in S^{n-1}:\langle a,x\rangle\le b'\}\) such that \(\Pr(\bar B)=\Pr(H)\) and
\[
\Pr(\bar B\triangle H)\le Cn^{-1/2}\log n.
\]

<a id="pdf-b53c1a5aa27d-p039-b006"></a>
<!-- pdf-source: page=39; block=6; confidence=0.99 -->
**Lemma 8.2.** For any two sets \(A_1,A_2\subseteq S^{n-1}\) and any \(\rho\in[-1+\epsilon,1-\epsilon]\),
\[
|Q_\rho(A_1,A_2)-\Pr_\rho(\bar A_1,\bar A_2)|\le C(\epsilon)n^{-1/2}\log n.
\]

<a id="pdf-b53c1a5aa27d-p039-b007"></a>
<!-- pdf-source: page=39; block=7; confidence=0.94 -->
Lemmas 8.1 and 8.2 reduce Theorem 1.11 to Theorem 1.4.

<a id="pdf-b53c1a5aa27d-p040-b001"></a>
<!-- pdf-source: page=40; block=1; confidence=0.97 -->
Let \(\delta_*=\delta(A_1,A_2)\). If \(H_1,H_2\) are parallel half-spaces with \(\Pr(H_i)=\Pr(\bar A_i)\), then the preceding comparison gives
\[
\delta_*\le\Pr_\rho(X\in\bar H_1,Y\in\bar H_2)-\Pr_\rho(X\in\bar A_1,Y\in\bar A_2)+O(n^{-1/2}\log n)
\le Q_\rho(X\in B_1,Y\in B_2)-Q_\rho(X\in A_1,Y\in A_2)+O(n^{-1/2}\log n).
\]
Thus Theorem 1.4 applied to the radial extensions gives parallel half-spaces approximating them, and Lemma 8.1 gives parallel caps approximating \(A_1,A_2\).

<a id="pdf-b53c1a5aa27d-p040-b002"></a>
<!-- pdf-source: page=40; block=2; confidence=0.99 -->
Let \(H=\{x\in\mathbb R^n:\langle a,x\rangle\le b\}\), and suppose without loss of generality that \(b\ge0\). For \(\epsilon>0\), define
\[
H_\epsilon^+=\{x:\langle a,x\rangle\le b(1+\epsilon)\},\qquad H_\epsilon^-=\{x:\langle a,x\rangle\le b(1-\epsilon)\}.
\]
Take \(B=\{x\in S^{n-1}:\langle x,a\rangle\le b/\sqrt n\}\). Concentration inequalities give \(\Pr(\bar B\triangle H)\le C\epsilon+Ce^{-c\epsilon^2n}\). Choosing \(\epsilon=Cn^{-1/2}\log n\) proves (8.1), and then the cap threshold can be adjusted to match the measure.

<a id="pdf-b53c1a5aa27d-p041-b001"></a>
<!-- pdf-source: page=41; block=1; confidence=0.77 -->
Choose the unique threshold defining a cap \(B'\) with \(\Pr(\bar B')=\Pr(H)\), using continuity and strict monotonicity of cap measure in the threshold. The sets \(B'\) and \(\bar B\) are nested, so their symmetric-difference measure equals the difference of their measures; (8.1) bounds this difference. The triangle inequality therefore gives \(\Pr(H\triangle\bar B')\le Cn^{-1/2}\log n\).

<a id="pdf-b53c1a5aa27d-p041-b002"></a>
<!-- pdf-source: page=41; block=2; confidence=0.92 -->
The proof of Lemma 8.2 is deferred until after a brief introduction to spherical harmonics.

<a id="pdf-b53c1a5aa27d-p041-b003"></a>
<!-- pdf-source: page=41; block=3; confidence=0.99 -->
## 8.1 Spherical harmonics and Lemma 8.2

<a id="pdf-b53c1a5aa27d-p041-b004"></a>
<!-- pdf-source: page=41; block=4; confidence=0.85 -->
Let \(S_k^n\) be the space of homogeneous harmonic polynomials of degree \(k\), viewed as a subspace of \(L^2(S^{n-1},Q)\). These spaces are rotation-invariant and irreducible representations of \(SO(n)\); together they span this \(L^2\) space.

<a id="pdf-b53c1a5aa27d-p041-b005"></a>
<!-- pdf-source: page=41; block=5; confidence=0.92 -->
**Lemma 8.3.** If \(T:L^2(S^{n-1},Q)\to L^2(S^{n-1},Q)\) commutes with rotations, then the spaces \(S_k^n\), \(k\ge0\), are eigenspaces of \(T\).

<a id="pdf-b53c1a5aa27d-p041-b006"></a>
<!-- pdf-source: page=41; block=6; confidence=0.99 -->
Apply Lemma 8.3 to the operator \(T_\rho\) defined by \((T_\rho f)(X)=\mathbb E(f(Y)\mid X)\), where \((X,Y)\sim Q_\rho\). Since \(T_\rho\) commutes with rotations, each \(S_k\) is an eigenspace. There are values \(\mu_k(\rho)\) such that \(T_\rho f=\mu_k(\rho)f\) for \(f\in S_k\).

<a id="pdf-b53c1a5aa27d-p041-b007"></a>
<!-- pdf-source: page=41; block=7; confidence=0.99 -->
Define \(G_k(t)=\mathbb E(t+iW_1\sqrt{1-t^2})^k\), where \(W\) is uniform on \(S^{n-2}\), and let \(f_k(x)=G_k(x_1)\). Then \(f_k\in S_k\), \(f_k(e_1)=1\), and \((T_\rho f_k)(e_1)=G_k(\rho)\). Hence
\[
\mu_k(\rho)=\mathbb E(\rho+iW_1\sqrt{1-\rho^2})^k.
\]

<a id="pdf-b53c1a5aa27d-p041-b008"></a>
<!-- pdf-source: page=41; block=8; confidence=0.99 -->
**Lemma 8.4.** For any \(\epsilon>0\), there exists \(C(\epsilon)\) such that if \(\rho,\eta\in[-1+\epsilon,1-\epsilon]\), then
\[
|\mu_k(\rho)-\mu_k(\eta)|\le C(\epsilon)(|\rho-\eta|+n^{-1/2}).
\]

<a id="pdf-b53c1a5aa27d-p041-b009"></a>
<!-- pdf-source: page=41; block=9; confidence=0.98 -->
**Lemma 8.5.** For any \(\epsilon>0\), there exists \(C(\epsilon)\) such that if \(\rho,\eta\in[-1+\epsilon,1-\epsilon]\), then
\[
|Q_\rho(X\in A_1,Y\in A_2)-Q_\eta(X\in A_1,Y\in A_2)|\le C(\epsilon)Q^{1/2}(A_1)Q^{1/2}(A_2)(|\rho-\eta|+n^{-1/2}).
\]

<a id="pdf-b53c1a5aa27d-p042-b001"></a>
<!-- pdf-source: page=42; block=1; confidence=0.88 -->
**Proof.** Expand \(f=\sum_{k\ge0}f_k\), with \(f_k\in S_k^n\). Then \(T_\rho f-T_\eta f=\sum_k(\mu_k(\rho)-\mu_k(\eta))f_k\), and orthogonality gives
\[
\|T_\rho f-T_\eta f\|_2^2=\sum_k(\mu_k(\rho)-\mu_k(\eta))^2\|f_k\|_2^2.
\]
Lemma 8.4 bounds this by \(C_\varepsilon(|\rho-\eta|+n^{-1/2})^2\|f\|_2^2\). Cauchy–Schwarz then bounds \(|\mathbb E[gT_\rho f]-\mathbb E[gT_\eta f]|\) by \(C_\varepsilon(|\rho-\eta|+n^{-1/2})\|f\|_2\|g\|_2\). Taking \(f=1_{A_1}\), \(g=1_{A_2}\) gives the claimed probability comparison and the factors from their marginal measures.

<a id="pdf-b53c1a5aa27d-p042-b002"></a>
<!-- pdf-source: page=42; block=2; confidence=0.92 -->
Normalized Gaussian vectors have inner products concentrated near \(\rho\), whereas spherical correlated pairs have inner product exactly \(\rho\). Lemma 8.5 controls the effect of this small parameter change on the joint event probability.

<a id="pdf-b53c1a5aa27d-p042-b003"></a>
<!-- pdf-source: page=42; block=3; confidence=0.80 -->
**Proof of Lemma 8.2.** For \((X,Y)\sim\Pr_\rho\), the complemented-set event reduces to the corresponding event for \(A_1,A_2\). Conditional on the normalized vectors \(X/\|X\|,Y/\|Y\|\), they are distributed according to \(Q_r\), where \(r=\langle X,Y\rangle/(\|X\|\|Y\|)\). With probability at least \(1-n^{-2}\), \(r\) lies within \(Cn^{-1/2}\log n\) of \(\rho\). Apply Lemma 8.5 on this event and bound the exceptional event; a symmetric comparison gives the reverse inequality. Some conditioning notation and the precise error expression are garbled.

<a id="pdf-b53c1a5aa27d-p042-b004"></a>
<!-- pdf-source: page=42; block=4; confidence=0.99 -->
Define \(Z_\rho=\rho+iW_1\sqrt{1-\rho^2}\), where \(W\) is uniformly distributed on \(S^{n-2}\); then \(\mu_k(\rho)=\mathbb EZ_\rho^k\). With probability at least \(1-\exp(-cn)\), \(|W_1|\le1/2\). On this event,
\[
|Z_\rho|=\sqrt{\rho^2+W_1^2(1-\rho^2)}\le\sqrt{\frac{1+\rho^2}{2}}\le1-\frac\epsilon2\le e^{-c\epsilon}.
\]

<a id="pdf-b53c1a5aa27d-p043-b001"></a>
<!-- pdf-source: page=43; block=1; confidence=0.99 -->
From (8.2),
\[
\mu_k(\rho)-\mu_k(\eta)=\mathbb E(Z_\rho^k-Z_\eta^k)=\mathbb E\left((Z_\rho-Z_\eta)\sum_{j=1}^{k-1}Z_\rho^jZ_\eta^{k-1-j}\right).
\]
When \(|W_1|\le1/2\), the geometric sum is bounded by \(C(\epsilon)\). The complementary event contributes at most \(e^{-cn}\). Since \(\mathbb E|Z_\rho-Z_\eta|\le C(\epsilon)|\rho-\eta|\), the result follows.

<a id="pdf-b53c1a5aa27d-p043-b002"></a>
<!-- pdf-source: page=43; block=2; confidence=0.99 -->
## 8.2 Spherical noise and Max-Cut

<a id="pdf-b53c1a5aa27d-p043-b003"></a>
<!-- pdf-source: page=43; block=3; confidence=0.98 -->
This section derives robust optimality of half-space rounding (Theorem 1.12) from robust noise sensitivity on the sphere (Theorem 1.11), using Karloff’s family of graphs.

<a id="pdf-b53c1a5aa27d-p043-b004"></a>
<!-- pdf-source: page=43; block=4; confidence=0.99 -->
For any \(n,d\in\mathbb N\), let \(G_{n,d}=(V_{n,d},E_{n,d})\) be the graph whose vertices are the \(\binom n{n/2}\) balanced elements of \(\{-n^{-1/2},n^{-1/2}\}^n\), with an edge between \(u\) and \(v\) if \(\langle u,v\rangle=d/n\).

<a id="pdf-b53c1a5aa27d-p043-b005"></a>
<!-- pdf-source: page=43; block=5; confidence=0.87 -->
**Lemma 8.6.** If X,Y are distributed according to Q_{d/n}, then every rounding scheme R satisfies
\[
\operatorname{Cut}(G_{n,d},R)\le \frac{|E_{n,d}|}{2}\,\mathbb{E}_{X,Y,R}\bigl[|R(X)-R(Y)|\bigr].
\]

<a id="pdf-b53c1a5aa27d-p043-b006"></a>
<!-- pdf-source: page=43; block=6; confidence=0.99 -->
By definition,
\[
\operatorname{Cut}(G,R)=\frac12\min_f\mathbb E_R\sum_{(u,v)\in E}|R(f(u))-R(f(v))|.
\]
Averaging over rotations bounds the minimum by the average over uniformly random rotations. For each edge, \((f(u),f(v))\) then has distribution \((X,Y)\sim Q_{d/n}\), giving the claimed inequality.

<a id="pdf-b53c1a5aa27d-p044-b001"></a>
<!-- pdf-source: page=44; block=1; confidence=0.98 -->
Choose \(n,d\) so that \(|d/n-\cos^{-1}\theta^*|\le n^{-1}\), where \(\theta^*\approx2.33\) minimizes \(\alpha_\theta\). Suppose a rounding scheme \(R\) satisfies \(\operatorname{Cut}(G_{n,d},R)\ge\operatorname{MaxCut}(G_{n,d})(\alpha_{\theta^*}-\epsilon)\). Taking \(\theta=\cos^{-1}(d/n)\), continuity of \(\alpha_\theta\) gives the corresponding half-space benchmark up to \(C\epsilon_*\), where \(\epsilon_*=\max\{\epsilon,n^{-1/2}\log n\}\).

<a id="pdf-b53c1a5aa27d-p044-b002"></a>
<!-- pdf-source: page=44; block=2; confidence=0.99 -->
Let \(A_R=\{x:R(x)=1\}\subseteq S^{n-1}\) and set \(\rho=\cos\theta\). Then
\[
\mathbb E(\Pr(A_R)-S_\rho(A_R))=\frac12\mathbb E|R(X)-R(Y)|\ge\frac2\pi\arccos\rho-C\epsilon_*.
\tag{8.3}
\]

<a id="pdf-b53c1a5aa27d-p044-b003"></a>
<!-- pdf-source: page=44; block=3; confidence=0.98 -->
Let \(\delta_R=\frac2\pi\arccos\rho-(\Pr(A_R)-S_\rho(A_R))\), and let \(\eta_R\) be the distance from \(A_R\) to the nearest hemisphere \(B_R\). Since \(\theta\approx\theta^*\approx2.33\), \(\rho=\cos\theta<0\). Theorem 1.11, with its deficit inequality reversed, gives \(\eta_R\le C\max\{\delta_R,n^{-1/2}\log n\}^c\). Taking expectations yields \(\mathbb E\eta_R\le C\epsilon_*^c\).

<a id="pdf-b53c1a5aa27d-p044-b004"></a>
<!-- pdf-source: page=44; block=4; confidence=0.99 -->
Let \(\widetilde R\) be the rounding scheme equal to \(1\) on \(B_R\) and \(-1\) elsewhere. Then \(\mathbb E(|R(Y)-\widetilde R(Y)|\mid R)=2\eta_R\), and consequently \(\mathbb E|R(Y)-\widetilde R(Y)|\le C\epsilon_*^c\). Since \(\widetilde R\) is a hyperplane rounding scheme, this proves Theorem 1.12.

<a id="pdf-b53c1a5aa27d-p044-b005"></a>
<!-- pdf-source: page=44; block=5; confidence=0.96 -->
The authors acknowledge hospitality and discussions during a visit to Université Paul Sabatier.

<a id="pdf-b53c1a5aa27d-p046-b001"></a>
<!-- pdf-source: page=46; block=1; confidence=0.99 -->
Bibliographic entries [17]–[34] cite work on Gaussian Brunn–Minkowski inequalities and partitions, MAX-CUT and CSP approximation, social choice, polynomial threshold functions, Gaussian surface area and noise sensitivity, isoperimetry, and halfspace testing.

<a id="pdf-b53c1a5aa27d-p047-b001"></a>
<!-- pdf-source: page=47; block=1; confidence=0.99 -->
Bibliographic entries [35]–[40] cite work on Gaussian isoperimetry and noise stability, spherical harmonics, moment-based tail comparison, CSP algorithms, and extremal halfspaces for spherically invariant measures.
