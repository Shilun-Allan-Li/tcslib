<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: d5b902970e6158d5f4b3fd1c6dd3d6a5e461a2b47427860662ce85739e106ab3 -->

<a id="pdf-d5b902970e61-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=1.00 -->
# A Chernoff Bound for Random Walks on Expander Graphs

<a id="pdf-d5b902970e61-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=1.00 -->
For a finite weighted-graph walk, the fraction of time spent in a vertex set concentrates exponentially around its stationary probability, with an exponent depending on walk length, squared deviation, and graph expansion. Sampling along one trajectory can improve approximation algorithms and supports efficient entropy estimation.

<a id="pdf-d5b902970e61-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=1.00 -->
## 1. Introduction

<a id="pdf-d5b902970e61-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.94 -->
Let $G$ be a connected undirected graph with positive edge weights. At each step, the walk chooses an incident edge with probability proportional to its weight; it has limiting distribution $\pi$ and is a finite reversible Markov chain. For a vertex set $A$, let $t_n$ be the number of the first $n$ steps spent in $A$. For almost every trajectory, $t_n/n\to\pi(A)$. The paper studies the probability that this fraction deviates from $\pi(A)$; Theorem 2.1 gives an exponential bound in the walk length and the square of the deviation.

<a id="pdf-d5b902970e61-p001-b005"></a>
<!-- pdf-source: page=1; block=5; confidence=0.97 -->
Theorem 2.1’s exponent is proportional to the transition matrix’s eigenvalue gap, which is related to graph expansion. Dependence on the starting distribution can introduce a factor of $|G|$; in that case, $O(\log |G|)$ walk steps suffice for a good estimate of $\pi(A)$. Starting near stationarity removes this size dependence.

<a id="pdf-d5b902970e61-p001-b006"></a>
<!-- pdf-source: page=1; block=6; confidence=1.00 -->
**Definition.** If $P^{(k)}$ is the walk’s distribution after $k$ steps, convergence is meant in the Cesàro sense: $\frac1n\sum_{k=1}^n P^{(k)}\to\pi$, including when $G$ is bipartite.

<a id="pdf-d5b902970e61-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.96 -->
Theorem 2.1 gives an exponential deviation bound in a computable parameter, the eigenvalue gap; it implies bounds on higher moments and convergence rates in each $L^p$, $1\le p<\infty$. It strengthens earlier exponential bounds for constant deviations and variance-based quadratic bounds, and differs from bounds on the probability of not hitting $A$.

<a id="pdf-d5b902970e61-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=1.00 -->
The result extends from the indicator $\chi_A$ to estimating $\mathbb E_\pi f$ for any nonnegative vertex function $f$; the bound also depends on $\max_x |f(x)|$.

<a id="pdf-d5b902970e61-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=1.00 -->
## Approximation algorithms

<a id="pdf-d5b902970e61-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.99 -->
To estimate $\pi(A)$, the standard procedure (SP) obtains independent near-stationary samples, typically using repeated walks. Aldous’s procedure (AP) first obtains a near-stationary point and then samples subsequent vertices along the continuing walk. The paper analyzes AP, a method used in applications without a rigorous reliability analysis.

<a id="pdf-d5b902970e61-p002-b005"></a>
<!-- pdf-source: page=2; block=5; confidence=0.99 -->
For relaxation time $\tau$, SP obtains $l$ samples in $\tau l$ steps. Along the same trajectory, AP averages the next $\tau(l-1)$ vertices; this can be viewed as averaging $\tau$ dependent SP estimates, each using $l-1$ samples, suggesting a potential efficiency gain.

<a id="pdf-d5b902970e61-p002-b006"></a>
<!-- pdf-source: page=2; block=6; confidence=1.00 -->
The paper analyzes these algorithms in the $(\beta,\delta)$ framework: with probability at least $1-\delta$, output a relative-error-$\beta$ approximation to $\pi(A)$. The discussion continues on the next page.

<a id="pdf-d5b902970e61-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=1.00 -->
Assume a starting point $s\in G$ can be found efficiently. Theorem 2.1 yields an AP walk length $O(\log(1/\pi(s))+\log(1/\delta)/\beta^2)$; SP requires $O(\log(1/\pi(s))\log(1/\delta)/\beta^2)$. Constants depend on the eigenvalue gap and $\pi(A)$.

<a id="pdf-d5b902970e61-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.99 -->
Because the bound’s dependence on $\pi(A)$ can favor SP when $\pi(A)$ is small, use AP with constant failure probability (for example, $1/4$), repeat it $\log(1/\delta)$ times, and take the median. This modified analysis uses an extension of Aldous’s variance bound.

<a id="pdf-d5b902970e61-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.99 -->
A modified Jerrum–Sinclair algorithm reduces the stated running time from $O(|E|^3m^7)$ to $O(|E|^2m^6)$, where $m$ is the number of vertices. It calls $(\beta,\delta)$ approximation routines for different functions; the improvement uses AP and the partial cancellation of independent errors across calls.

<a id="pdf-d5b902970e61-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.98 -->
For a graph $H=(V,E)$ with $2m$ vertices, the modified algorithm reduces running time from $O(q^3m^6|E|\log^2 m)$ to $O(q^2m^5|E|\log m)$, where $q$ bounds the ratio of the number of $(m-1)$-edge matchings to the number of perfect matchings. AP contributes to the improvement; the method also selects sets $A$ with $\pi(A)$ not too small because routine cost grows inversely with $\pi(A)$. Polynomial bounds such as $q(m)=m^2$ are known for dense bipartite graphs and regular periodic lattices.

<a id="pdf-d5b902970e61-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=1.00 -->
## Entropy estimation

<a id="pdf-d5b902970e61-p003-b006"></a>
<!-- pdf-source: page=3; block=6; confidence=0.98 -->
For an unweighted graph, Theorem 2.1 implies that walk entropy can be estimated accurately from a short trajectory. The formulation treats the walk as an information source over vertices and also applies to vertex labelings making the chain unifilar (each state has positive transition probability to at most one state of each label). With constant eigenvalue gap and bounded degree, a good estimate needs $O(\log |G|)$ steps.

<a id="pdf-d5b902970e61-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.98 -->
The paper quantifies the convergence rate in the Shannon–McMillan property and develops an error-exponent bound for fixed-length noiseless source coding using computable Markov-chain properties.

<a id="pdf-d5b902970e61-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.98 -->
The proof of Theorem 2.1 uses a moment-generating-function bound due to Höglund, then controls the top eigenvalue of a perturbed transition matrix via its second derivative, analyticity, and Cauchy’s estimate before optimizing over the perturbation parameter.

<a id="pdf-d5b902970e61-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.99 -->
The paper presents the main theorem, compares related results, extends a variance bound for sampling, discusses algorithms for Ising partition functions and perfect matchings, and applies random walks to entropy estimation.

<a id="pdf-d5b902970e61-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=1.00 -->
## 2. The main theorem

<a id="pdf-d5b902970e61-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.99 -->
Let $G=(V,E)$ be a connected undirected graph with positive edge weights $w_{xy}$. Define the vertex weight $w_x=\sum_{\{x,y\}\in E}w_{xy}$. The associated time-reversible Markov chain has transition probabilities $p_{xy}=w_{xy}/w_x$ when $\{x,y\}\in E$, and $p_{xy}=0$ otherwise. Its transition matrix is $P=(p_{xy})$.

<a id="pdf-d5b902970e61-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.98 -->
The eigenvalues satisfy $1=\lambda_1>\lambda_2\ge\cdots\ge\lambda_{|V|}\ge-1$, with $\lambda_{|V|}=-1$ exactly when $G$ is bipartite. The stationary distribution is $\pi(x)=w_x/\sum_{y\in V}w_y$. From any initial distribution, Cesàro averages converge to $\pi$; if $G$ is not bipartite, the distributions $P^n d$ themselves converge to $\pi$. Define the eigenvalue gap $\epsilon=1-\lambda_2$.

<a id="pdf-d5b902970e61-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.99 -->
For a walk $(x_0,x_1,\ldots)$ with $x_0\sim q$ and a set $A\subseteq V$, let $\chi_A$ be its indicator and $t_n=\chi_A(x_1)+\cdots+\chi_A(x_n)$. Define the vector $q/\sqrt{\pi}$ entrywise by $(q/\sqrt{\pi})(x)=q(x)/\sqrt{\pi(x)}$, and let $N_q=\|q/\sqrt{\pi}\|_2$. Let $\mathbf 1=(1,\ldots,1)$ be the all-ones vector. Logarithms are base $e$ unless otherwise specified.

<a id="pdf-d5b902970e61-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.99 -->
**Theorem 2.1.** For the weighted-graph walk started from $q$, any $A\subseteq V$, and $\gamma\ge0$,
\[
\Pr[t_n-n\pi(A)\ge\gamma]\le \left(1+\frac{\gamma\epsilon}{10n}\right)N_q\exp\!\left(-\frac{\gamma^2\epsilon}{20n}\right). \tag{2.1}
\]

<a id="pdf-d5b902970e61-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.96 -->
The bound extends to a nonnegative vertex function $f$ by replacing $t_n$ with $\sum_{i=1}^n f(x_i)$ and $\pi(A)$ with $E_\pi f$:
\[
\Pr[t_n-nE_\pi f\ge\gamma]\le\left(1+\frac{\gamma\epsilon}{10n}\right)N_q\exp\!\left(-\frac{(\gamma/\|f\|_\infty)^2\epsilon}{20n}\right). \tag{2.2}
\]
Applying Theorem 2.1 to $G\setminus A$ yields the corresponding lower-tail bound. The proof first establishes Theorem 2.2, reducing deviation estimation to analysis of a perturbed transition matrix.

<a id="pdf-d5b902970e61-p005-b005"></a>
<!-- pdf-source: page=5; block=5; confidence=0.97 -->
Let $P(r)=PE_r$, where $E_r=\operatorname{diag}(e^{r\chi_A})$ and $r$ is any complex number. Thus $P(r)$ is equal to $P$ except that each column indexed by $j\in A$ is multiplied by $e^r$. Let $M$ be the weighted adjacency matrix of $G$, and let $D=\operatorname{diag}(1/w_i)$. Then
\[
P=\sqrt D\,S\,\sqrt{D^{-1}},\qquad P(r)=\sqrt{D E_r^{-1}}\,S(r)\,\sqrt{E_rD^{-1}}, \tag{2.3}
\]
where $S:=\sqrt D M\sqrt D$ and $S(r):=\sqrt{D E_r}\,M\sqrt{D E_r}$ are symmetric. By (2.3), for $r\ge0$ the eigenvalues of $P(r)$ are real and equal to those of $S(r)$.

<a id="pdf-d5b902970e61-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.98 -->
Write $\lambda(r)$ and $\lambda_2(r)$ for the largest and second-largest eigenvalues of $P(r)$, and $\epsilon_r=\lambda(r)-\lambda_2(r)$. At $r=0$, $P(0)=P$, $\lambda(0)=1$ with left eigenvector $\pi^T$ and right eigenvector $\mathbf1$, and $\lambda_2(0)=\lambda_2$.

<a id="pdf-d5b902970e61-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=1.00 -->
**Theorem 2.2.** Consider the random walk on a weighted graph $G=(V,E)$ with initial distribution $q$. Let $A\subseteq V$, and let $t_n$ be the number of visits to $A$ in $n$ steps. For any $\gamma\ge0$ and $r\ge0$,
\[
\Pr[t_n-n\pi(A)\ge\gamma]\le e^{-r(n\pi(A)+\gamma)+n\log\lambda(r)}\,\frac{qP(r)^n\mathbf1}{\lambda(r)^n}. \tag{2.4}
\]

<a id="pdf-d5b902970e61-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=1.00 -->
**Proof.** By Markov’s inequality,
\[
\Pr[t_n\ge n\pi(A)+\gamma]=\Pr[e^{rt_n}\ge e^{r(n\pi(A)+\gamma)}]\le e^{-r(n\pi(A)+\gamma)}E_q e^{rt_n}. \tag{2.5}
\]
Summing over trajectories gives
\[
E_q e^{rt_n}=\sum_{x_0,\ldots,x_n}e^{rt_n}q(x_0)\prod_{i=1}^n p_{x_{i-1}x_i}=qP(r)^n\mathbf1. \tag{2.6}
\]
Combining (2.5) and (2.6),
\[
\Pr[t_n\ge n\pi(A)+\gamma]\le e^{-r(n\pi(A)+\gamma)+n\log\lambda(r)}\,\frac{qP(r)^n\mathbf1}{\lambda(r)^n}. \tag{2.7}
\]

<a id="pdf-d5b902970e61-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.94 -->
The proof uses two estimates: the normalized matrix factor is bounded by Lemma 2.3, while the exponent is controlled by Lemma 2.4 using $\left.\frac{d}{dr}\log\lambda(r)\right|_{r=0}=\pi(A)$ and $\log\lambda(0)=0$.

<a id="pdf-d5b902970e61-p006-b005"></a>
<!-- pdf-source: page=6; block=5; confidence=0.99 -->
**Lemma 2.3.** For $0\le r\le1$,
\[
\frac{qP(r)^n\mathbf1}{\lambda(r)^n}\le (1+r)N_q.
\]

<a id="pdf-d5b902970e61-p006-b006"></a>
<!-- pdf-source: page=6; block=6; confidence=0.99 -->
**Lemma 2.4.** For real $r$ satisfying $0\le e^r-1\le\epsilon/4$,
\[
\log\lambda(r)\le r\pi(A)+\frac{5r^2}{\epsilon}.
\]

<a id="pdf-d5b902970e61-p006-b007"></a>
<!-- pdf-source: page=6; block=7; confidence=0.96 -->
**Proof.** Combining (2.4) and Lemmas 2.3–2.4 gives
\[
\Pr[t_n-n\pi(A)\ge\gamma]\le(1+r)N_q\exp\left[-n\left(\frac{r\gamma}{n}-\frac{5r^2}{\epsilon}\right)\right]. \tag{2.8}
\]
The quadratic is maximized at $r=\gamma\epsilon/(10n)$, with value $\gamma^2\epsilon/(20n^2)$. For $\gamma<n$, this choice meets the condition of Lemma 2.4; for $\gamma\ge n$ the claimed bound is trivial. Substitution gives (2.1).

<a id="pdf-d5b902970e61-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=1.00 -->
The preceding proof concludes.

<a id="pdf-d5b902970e61-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.94 -->
**Proof of Lemma 2.3.** Since $S(r)$ from (2.3) is symmetric, $\|S(r)\|_2=\lambda(r)$. We have
\[
\frac{qP(r)^n\mathbf1}{\lambda(r)^n}
=\frac{q\sqrt{D E_r^{-1}}\,S(r)^n\sqrt{E_rD^{-1}}\mathbf1}{\lambda(r)^n}
\le e^{r/2}\frac{\|q/\sqrt\pi\|_2\,\|S(r)^n\|_2\,\|\sqrt\pi\|_2}{\lambda(r)^n}
<e^{r/2}N_q\le(1+r)N_q.
\]

<a id="pdf-d5b902970e61-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.97 -->
For $r\ge0$, define $B(r)=e^{-1}(S(r+1)-S(r))$. Entrywise, $B(r)\le S(r)$; its entries equal those of $S(r)$ on $A\times A$, and vanish on $A^c\times A^c$. Fix $r$ with $0\le e^r-1\le\epsilon/4$.

<a id="pdf-d5b902970e61-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.97 -->
The Taylor expansion about $y=r$ is
\[
\log\lambda(y)=\log\lambda(r)+m_r(y-r)+(y-r)^2\int_0^1(1-t)V_{r+(y-r)t}\,dt. \tag{2.9}
\]
Here $m_z$ and $V_z$ are the first and second derivatives, respectively, of $\log\lambda(y)$ at $y=z$. Also, $m_0=\sqrt\pi B(0)\sqrt\pi=\pi(A)$, the limit of the mean of $t_n/n$ as $n\to\infty$, and $V_0$ is the limit of the variance of $t_n/n$ as $n\to\infty$.

<a id="pdf-d5b902970e61-p007-b005"></a>
<!-- pdf-source: page=7; block=5; confidence=0.97 -->
**Claim 1.** If $0\le e^r-1\le\epsilon/4$, then (i) $\epsilon_r\ge3\epsilon/4$ and (ii) $V_r\le10/\epsilon$. The text says Lemma 2.4 follows from (2.9) and part (ii).

<a id="pdf-d5b902970e61-p007-b006"></a>
<!-- pdf-source: page=7; block=6; confidence=0.89 -->
**Proof of Claim 1(i).** It is enough to show that $\epsilon_r\ge\epsilon-(e^r-1)$. For $r\ge0$, $P(r)$ and $S(r)$ have the same eigenvalues, $S(r)$ is nonnegative, and $S(r)\ge S$ entrywise. By the Perron–Frobenius theorem, $\lambda(r)\ge1$. Let $\mu<\lambda(r)$ be any other eigenvalue of $S(r)$. It suffices to show $\mu\le\lambda_2+e^r-1$. The matrix $S$ is diagonalizable; there are a unitary matrix $U$ and diagonal matrices $D'$ and $D_A$ such that
\[
B(0)=\tfrac12(SD_A+D_AS),\qquad D'=U^*SU,\qquad \|D'\|_2=\|D_A\|_2=1.
\]
If $\mu>\lambda_2$, then the matrix
\[
U^T\bigl(S+(e^r-1)B(0)-\mu I\bigr)U
\]
is singular. Consequently,
\[
1\le\tfrac12\|(D'-\mu I)^{-1}(e^r-1)D'U^TD_AU\|_2
+\tfrac12\|(D'-\mu I)^{-1}(e^r-1)U^TD_AUD'\|_2
\le\frac{e^r-1}{\mu-\lambda_2}.
\]
(The first inequality uses continuity of $\lambda_2(\cdot)$. ) This proves part (i).

<a id="pdf-d5b902970e61-p007-b007"></a>
<!-- pdf-source: page=7; block=7; confidence=0.96 -->
To bound $V_r$, the proof plans to apply Cauchy’s estimate using a bound on $\lambda(z)$ in a complex neighborhood of $r$, obtained from convergence of a contour integral.

<a id="pdf-d5b902970e61-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.90 -->
For complex $z$ near $r$, write $S(z)=S(r)+(e^{z-r}-1)B(r)$. Perturbation theory expresses the spectral projection for $\lambda(z)$ as $-\frac1{2\pi i}\int_\Gamma(S(z)-\zeta I)^{-1}\,d\zeta$, where $\Gamma$ encloses $\lambda(r)$ and no other eigenvalue of $S(r)$. Choose $\Gamma$ centered at $\lambda(r)$ with radius $\epsilon_r/2$. The resolvent remains finite if
\[
|e^{z-r}-1|<\|B(r)(S(r)-(\lambda(r)-\epsilon_r/2)I)^{-1}\|_2^{-1}\le 2/\epsilon_r. \tag{2.10}
\]
In the specified range of $r$, it suffices that
\[
|z-r|<3\epsilon_r/8. \tag{2.11}
\]
Continuity then implies $\lambda(z)$ stays inside $\Gamma$, hence $|\lambda(z)-\lambda(r)|\le\epsilon_r/2$.

<a id="pdf-d5b902970e61-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.96 -->
Whenever $|z-r|<3\epsilon_r/8$, $\lambda(z)$ lies inside $\Gamma$, and therefore $|\lambda(z)-\lambda(r)|\le\epsilon_r/2$. Comparing the Taylor series for $\lambda(z)$ and $\log\lambda(z)$ gives $V_r\le2\left.\frac{d^2\lambda}{dz^2}\right|_{z=r}$. Cauchy’s estimate, with $\rho=3\epsilon_r/8$, gives
\[
V_r\le 2\frac{\max\{|\lambda(z)|:|z-r|<\rho\}}{\rho^2}\le\frac{64}{9\epsilon_r}.
\]
By Claim 1(i), $V_r\le10/\epsilon$, completing the proof of Claim 1.

<a id="pdf-d5b902970e61-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.96 -->
The discussion notes improved deviation exponents by Dinwoodie and Kahale, including extensions to nonreversible chains and an optimality result for two-state chains; the details are cited to prior work.

<a id="pdf-d5b902970e61-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=1.00 -->
## 3. $(\beta,\delta)$-approximation algorithms for $\pi(A)$

<a id="pdf-d5b902970e61-p008-b005"></a>
<!-- pdf-source: page=8; block=5; confidence=1.00 -->
**Definition.** An algorithm estimating $\pi(A)$ is a $(\beta,\delta)$-approximation if its output $t$ satisfies, with probability at least $1-\delta$,
\[
\pi(A)(1-\beta)\le t\le\pi(A)(1+\beta).
\]
Its cost is the total number of random-walk steps. The setup assumes an efficiently obtainable starting vertex $s\in G$.

<a id="pdf-d5b902970e61-p008-b006"></a>
<!-- pdf-source: page=8; block=6; confidence=0.98 -->
The section introduces SP, AP, and modified AP (APm), and announces an efficiency analysis of AP followed by an analysis of APm using confidence amplification.

<a id="pdf-d5b902970e61-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.99 -->
Repeating a $(\beta,1/4)$ estimator independently $12\log(1/\delta)$ times and taking the median gives a $(\beta,\delta)$ estimator; APm is analyzed using this amplification result.

<a id="pdf-d5b902970e61-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.98 -->
**Definition (SP).** Run a $k'$-step walk from $s$ to obtain a sample with distribution $q'$, repeat independently $l'$ times from the same start, and estimate $\pi(A)$ by $t=t_{l'}/l'$, where $t_{l'}$ counts samples in $A$.

<a id="pdf-d5b902970e61-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.98 -->
**Definition (AP).** Choose positive integers $k,l$. Run a $k$-step delay from $s$, yielding $x_0$ with distribution $q$, then take the next $l$ visited states as samples. If $t_l$ samples lie in $A$, output $t=t_l/l$.

<a id="pdf-d5b902970e61-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.99 -->
**Definition (APm).** Run AP to estimate $\pi(A)$ independently $12\log(1/\delta)$ times and return the median estimate.

<a id="pdf-d5b902970e61-p009-b005"></a>
<!-- pdf-source: page=9; block=5; confidence=0.99 -->
For a distribution $d$ on the vertices of $G$, define its chi-square distance from $\pi$ by
\[
\chi_d^2=\sum_x\pi(x)\left(\frac{d(x)}{\pi(x)}-1\right)^2.
\]
Let $\chi_s^2$ denote the chi-square distance from $\pi$ of the initial distribution concentrated at $s$.

<a id="pdf-d5b902970e61-p009-b006"></a>
<!-- pdf-source: page=9; block=6; confidence=0.99 -->
**Proposition 3.1.** The cost of using AP to estimate $\pi(A)$ within additive error $\beta\pi(A)$ with probability at least $1-\delta$ is at most
\[
\frac{\log(1/\pi(s))}{\epsilon}+\frac{20\log(8/\delta)}{\epsilon\beta^2\pi(A)^2}.
\]

<a id="pdf-d5b902970e61-p009-b007"></a>
<!-- pdf-source: page=9; block=7; confidence=0.99 -->
**Proof.** Let $k=\log(1/\pi(s))/\epsilon$ and $l=20\log(8/\delta)/(\epsilon\beta^2\pi(A)^2)$. In the notation of Theorem 2.1, $N_q=1+\chi_q^2$. By Fill’s result, $\chi_q^2\le\chi_s^2(1-\epsilon)^k$. Therefore, $N_q\le1+\chi_s^2(1-\epsilon)^k\le e^{-\epsilon k}/\pi(s)\le2$. By Theorem 2.1 and the ensuing remark (ii),
\[
\Pr[|t_l/l-\pi(A)|\ge\beta\pi(A)]\le4N_qe^{-\beta^2\pi(A)^2\epsilon l/20}\le\delta.
\]

<a id="pdf-d5b902970e61-p009-b008"></a>
<!-- pdf-source: page=9; block=8; confidence=0.98 -->
Prior results bound modified AP’s cost in terms of $\pi_{\min}=\min_x\pi(x)$. The next result is introduced to replace this dependence by $\pi(s)$ for applications in the following section.

<a id="pdf-d5b902970e61-p009-b009"></a>
<!-- pdf-source: page=9; block=9; confidence=0.99 -->
**Proposition 3.2.** Let $\beta>0$ and $\alpha\le\beta^2$. Run AP with
\[
k=\frac{\log(20/(\pi(s)\alpha\pi(A)^2))}{\epsilon},\qquad l=\frac{10}{\epsilon\beta^2\pi(A)},
\]
and let $t$ be its estimate. Then
\[
|\mathbb E[t-\pi(A)]|\le\frac{\alpha\pi(A)^2}{20},\qquad \mathbb E(t-\pi(A))^2\le\frac{\beta^2\pi(A)^2}{4}.
\]

<a id="pdf-d5b902970e61-p009-b010"></a>
<!-- pdf-source: page=9; block=10; confidence=0.85 -->
The footnote says Fill’s bound depends on the larger of $\lambda_2$ and the absolute nontrivial eigenvalue maximum; a lazy walk makes $\lambda_2$ the larger quantity, increasing $k,l$ by at most a factor of two. The same observation applies to the later cited theorem.

<a id="pdf-d5b902970e61-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.94 -->
**Table 3.1. Costs of procedures for estimating $\pi(A)$.**

| Algorithm | Cost |
|---|---|
| SP | $\dfrac1\epsilon\log\dfrac1\delta\log\dfrac1{\pi(s)}\dfrac1{\beta^2\pi(A)}$ |
| AP | $\dfrac1\epsilon\left(\log\dfrac1{\pi(s)}+\log\dfrac1\delta\dfrac1{\beta^2\pi(A)^2}\right)$ |
| APm | $\dfrac1\epsilon\log\dfrac1\delta\left(\log\dfrac1{\pi(s)}+\dfrac1{\beta^2\pi(A)^2}\right)$ |

<a id="pdf-d5b902970e61-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.89 -->
**Proof.** The preceding result bounds the total variation distance of the sampled distribution \(q\) from \(\pi\) by \(\alpha\pi(A)^2/20\), and likewise for each sample distribution \(q_i\). Thus, for \(t=l^{-1}\sum_{i=1}^l 1_A(x_i)\), linearity gives \(\left|\mathbb E[t-\pi(A)]\right|\le \alpha\pi(A)^2/20\). Define \(b_j=\mathbb E[(t-\pi(A))^2\mid x_0=j]\); since \(\|b\|_\infty\le1\), Proposition 4.1 of [Ald87] gives \(\mathbb E_\pi b\le 2\pi(A)/(\varepsilon l)\). Consequently \(\mathbb E(t-\pi(A))^2\le 2\pi(A)/(\varepsilon l)+\alpha\pi(A)^2/20\le \beta^2\pi(A)^2/4\).

<a id="pdf-d5b902970e61-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.83 -->
**Corollary 3.3.** APm estimates \(\pi(A)\) within relative error \(\beta\), with probability at least \(1-\delta\), at cost at most \(12\log(1/\delta)\left[\log\!\left(20/(\pi(s)\alpha\pi(A)^2)\right)/\varepsilon+10/(\varepsilon\beta^2\pi(A))\right]\).

<a id="pdf-d5b902970e61-p010-b004"></a>
<!-- pdf-source: page=10; block=4; confidence=0.95 -->
**Proof.** Choose \(k,l\) as in Proposition 3.2 with \(\alpha=\beta^2\). The second-moment bound and Chebyshev's inequality imply \(\Pr(|t-\pi(A)|\ge\beta\pi(A))\le1/4\); Lemma 6.1 of [JVV] amplifies this to success probability at least \(1-\delta\).

<a id="pdf-d5b902970e61-p010-b005"></a>
<!-- pdf-source: page=10; block=5; confidence=0.90 -->
The standard procedure uses burn-in \(k'=O(\log(1/\pi_{\min})/\varepsilon)\) and sample count \(l'=O(\log(1/\delta)/(\beta^2\pi(A)))\); a refinement replaces \(\pi_{\min}\) by \(\pi(s)\). APm improves SP by a factor \(\min(\log(1/\pi(s)),1/(\beta^2\pi(A)))\), while AP is within factor \(O(1/\pi(A))\) of APm. AP may be preferable at small \(\delta\) when \(1/(\beta^2\pi(A)^2)<\log(1/\pi(s))\).

<a id="pdf-d5b902970e61-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.99 -->
## Chernoff Bound for Random Walks

<a id="pdf-d5b902970e61-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.87 -->
Dinwoodie’s improvement to Theorem 2.1’s exponent changes AP’s cost dependence from \(1/\pi(A)^2\) to \(1/\pi(A)\) for sufficiently small \(\beta\). The section’s results extend to estimating \(\mathbb E f\) for nonnegative vertex functions.

<a id="pdf-d5b902970e61-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.99 -->
**Proposition 3.4.** Let $\beta>0$ and $\alpha\le\beta^2$. Let $k=\log(20/(\pi(s)\alpha(\mathbb E f)^2))/\epsilon$ and $l=10\operatorname{Var}(f)/(\epsilon\beta^2(\mathbb E f)^2)$. Take a random walk on $G$ starting at $s$, and let $x_i$, $i\ge1$, stand for the $(i+k)$th vertex of the random walk. Let $t=\frac1l(f(x_1)+\cdots+f(x_l))$. Then
\[
|\mathbb E[t-\mathbb E f]|\le\alpha(\mathbb E f)^2/20
\quad\text{and}\quad
\mathbb E(t-\mathbb E f)^2\le\beta^2(\mathbb E f)^2/4.
\]

<a id="pdf-d5b902970e61-p011-b004"></a>
<!-- pdf-source: page=11; block=4; confidence=0.84 -->
For AP, the running time depends on \(\|f\|_\infty/(\mathbb E f)^2\); SP has the same dependence on \(\operatorname{Var}(f)\) and \((\mathbb E f)^2\) as APm. The discussion compares sampling costs and notes that starting samples immediately from \(s\) still yields polynomial-time estimates when \(\pi(A)\) is not too small; choosing burn-in at the relaxation time is most efficient under the stated analysis.

<a id="pdf-d5b902970e61-p011-b005"></a>
<!-- pdf-source: page=11; block=5; confidence=0.99 -->
## 4. Applications: Two Approximation Algorithms

### The subgraphs random walk for the Ising model

<a id="pdf-d5b902970e61-p011-b006"></a>
<!-- pdf-source: page=11; block=6; confidence=0.95 -->
A modified Jerrum–Sinclair algorithm estimates the ferromagnetic Ising partition function on \(m\) sites in time \(O(|E|^2m^6)\), improving the cited \(O(|E|^3m^7)\) bound.

<a id="pdf-d5b902970e61-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.96 -->
The algorithm is an FPRAS: given instance \(I\) and accuracy parameter \(a>0\), it runs in time polynomial in \(m,1/a\) and returns a relative-\(a\) approximation to \(Z\) with probability at least \(3/4\).

<a id="pdf-d5b902970e61-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.97 -->
**Definition.** For a graph \(I=([m],E)\) with positive edge interactions \(V_{ij}\), a spin configuration is \(\sigma\in\{-1,+1\}^m\). Its Hamiltonian is \(H(\sigma)=-\sum_{\{i,j\}\in E}V_{ij}\sigma_i\sigma_j-B\sum_{k\in[m]}\sigma_k\), where \(B\) is the external field. At temperature parameter \(\beta_T\), the partition function is \(Z=\sum_{\sigma\in\{-1,+1\}^m}e^{-\beta_T H(\sigma)}\).

<a id="pdf-d5b902970e61-p012-b003"></a>
<!-- pdf-source: page=12; block=3; confidence=0.98 -->
**Definition.** For \(X\subseteq E\), view \(X\) as a subgraph and let \(\operatorname{odd}(X)\) be its odd-degree vertices. Put \(\lambda_{ij}=\tanh(\beta_TV_{ij})\), \(\mu=\tanh(\beta_TB)\), and define \(w(X)=\mu^{|\operatorname{odd}(X)|}\prod_{\{i,j\}\in X}\lambda_{ij}\) (4.1). The subgraphs-world partition function is \(Z'=\sum_{X\subseteq E}w(X)\) (4.2).

<a id="pdf-d5b902970e61-p012-b004"></a>
<!-- pdf-source: page=12; block=4; confidence=0.97 -->
The spin and subgraph partition functions satisfy \(Z=AZ'\) (4.3), where \(A=(2\cosh(\beta_TB))^m\prod_{\{i,j\}\in E}\cosh(\beta_TV_{ij})\).

<a id="pdf-d5b902970e61-p012-b005"></a>
<!-- pdf-source: page=12; block=5; confidence=0.89 -->
A Markov chain on \(G=\{X:X\subseteq E\}\) uses the weights \(w(X)\) and fixed \(\mu\). Select an edge \(e\) uniformly and set \(Y=X\mathbin{\triangle}\{e\}\); if \(w(Y)\ge w(X)\), move to \(Y\) with probability one. The remaining transition rule continues beyond the supplied page text.

<a id="pdf-d5b902970e61-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.99 -->
The algorithm chooses the natural number $r$ satisfying $\frac{m-r}{m}>\tanh\beta_TB\ge\frac{m-r-1}{m}$. It sets $\mu_0=1$ and, for $j=0,1,\ldots,r$, uses $\mu_{j+1}=(m-j)/m$ when $j\le r$ and $\mu_{j+1}=\tanh\beta_TB$ otherwise.

<a id="pdf-d5b902970e61-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.98 -->
The walk on $G$ is connected by the transitions that have positive probability. Its unique stationary distribution is $\pi=\pi^\mu$, given by $\pi(X)=w(X)/Z'(\mu)$. The method computes $Z'(1)=\prod_{\{i,j\}\in E}(1+\lambda_{ij})$ and bootstraps from $Z'(1)$ down to $Z'(\mu)$ by computing successive ratios. For $0\le\mu_1<\mu_0\le1$, define $f(X)=(\mu_1/\mu_0)^{|\operatorname{odd}(X)|}$. Then $\mathbb E_{\mu_0}f=Z'(\mu_1)/Z'(\mu_0)$. If $\mu_0\le\mu_1+1/m$, the cited lemma gives $\mathbb E_{\mu_0}f\ge1/10$. The approximation scheme uses $\epsilon\ge(2m^4|E|^2)^{-1}$. In step (5) it uses $\beta=\Theta(a/\sqrt m)$ instead of $\beta=\Theta(a/m)$; the accumulated errors in $\Pi$ tend to cancel one another out.

<a id="pdf-d5b902970e61-p013-b003"></a>
<!-- pdf-source: page=13; block=3; confidence=0.93 -->
**Lemma 4.1.** Let \(z_1,\ldots,z_m\) be independent nonnegative random variables with \(\mathbb E z_i\le\eta/(2m^2)\) and \(\mathbb E z_i^2\le\nu/m\), where \(\eta,\nu\le1\). For \(Y=\prod_{i=1}^m(1+z_i)\), \(\mathbb E(Y-1)^2\le\eta/m+\nu+(\eta/m+\nu)^2\).

<a id="pdf-d5b902970e61-p013-b004"></a>
<!-- pdf-source: page=13; block=4; confidence=0.92 -->
**Proof.** Since \(Y\ge1\), \(\mathbb E(Y-1)^2\le\mathbb EY^2-1\). Independence gives \(\mathbb EY^2=\prod_i(1+2\mathbb Ez_i+\mathbb Ez_i^2)\le(1+\eta/m^2+\nu/m)^m\le e^{\eta/m+\nu}\). Using \(e^x-1\le x+x^2\) for the applicable range yields the stated bound.

<a id="pdf-d5b902970e61-p013-b005"></a>
<!-- pdf-source: page=13; block=5; confidence=0.97 -->
**Theorem 4.2.** For \(a\in(0,1)\), the algorithm's output \(\Pi\) satisfies \(\Pi(1-a)<Z<\Pi(1+a)\) with probability at least \(3/4\), using at most \(500m^6|E|^2/a^2\) random-walk steps.

<a id="pdf-d5b902970e61-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.97 -->
The cited Jerrum–Sinclair method requires \(O(m^7|E|^3/a^2)\) random-walk steps under its stated bounds.

<a id="pdf-d5b902970e61-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.95 -->
**Proof.** For iteration \(j\), let \(t_j\) estimate \(\mathbb E_{\mu_j}f\) and set \(z_j=t_j/(\mathbb E_{\mu_j}f)-1\); then \(Y=\prod_j(1+z_j)=\Pi/Z\). Proposition 3.4 supplies \(|\mathbb E_{\mu_j}z_j|\le a^2/(40m^2)\) and \(\mathbb E_{\mu_j}z_j^2\le a^2/(8m)\). Taking at most \(m\) factors, Lemma 4.1 with \(\eta=a^2/20\), \(\nu=a^2/8\), followed by Chebyshev, gives \(\Pr(|\Pi/Z-1|\ge a)\le[a^2/20+a^2/8+(a^2/20+a^2/8)^2]/a^2\le1/4\).

<a id="pdf-d5b902970e61-p014-b003"></a>
<!-- pdf-source: page=14; block=3; confidence=0.99 -->
## Perfect matchings

<a id="pdf-d5b902970e61-p014-b004"></a>
<!-- pdf-source: page=14; block=4; confidence=0.99 -->
A matching in $H=(V,E)$ is a subset of $E$ whose edges have no common endpoints. A perfect matching is a matching with $m$ edges, where $|V|=2m$. Let $M_j$ denote the set of matchings of size $j$ in $H$. An upper bound $q(m)>|M_{m-1}|/\max(1,|M_m|)$ is assumed known for some fixed polynomial $q$. Thus $H$ is said to be $q$-amenable. In general, $q(m)\ge m$.

<a id="pdf-d5b902970e61-p014-b005"></a>
<!-- pdf-source: page=14; block=5; confidence=0.94 -->
Prior results cited include amenability bounds for dense graphs, random bipartite graphs above the perfect-matching threshold, bipartite Cayley graphs, and regular periodic lattices. The Jerrum–Sinclair method uses a walk on matchings with stationary weights proportional to \(c^{|M_j|}\), then estimates adjacent size ratios \(|M_{j+1}|/|M_j|=c\,\pi(M_{j+1})/\pi(M_j)\) and multiplies them to estimate \(|M_m|\), starting from \(|M_1|=|E|\). The modified method uses AP and chooses \(c\) so both adjacent matching classes have stationary mass \(\Omega(1/m)\). Log-concavity of \(|M_1|,\ldots,|M_m|\) motivates adapting the parameter schedule to clustered ratio thresholds.

<a id="pdf-d5b902970e61-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.94 -->
Log-concavity gives \(\log|E|^{-1}=\log(|M_0|/|M_1|)\le\cdots\le\log(|M_{m-1}|/|M_m|)\le\log q(m)\). Set \(c_j=|M_{j-1}|/|M_j|\) and \(c_{m+1}=q(m)\). For \(c\in[c_j,c_{j+1}]\), \(\pi(M_j)\) is maximal among the matching-size classes; at \(c=c_{j+1}\), both \(\pi(M_j)\) and \(\pi(M_{j+1})\) are at least \(1/m\). The algorithm samples a constant-factor grid in \(c\), using finer steps where adjacent log-ratios cluster, so \(m+O(\log m)\) values suffice to approximate every threshold.

<a id="pdf-d5b902970e61-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.98 -->
**Theorem 4.3.** If \(a\in(0,1/2]\) and \(H\) is \(q\)-amenable, the output \(\Pi\) satisfies \(\Pi(1-a)<|M_m|<\Pi(1+a)\) with probability at least \(3/4\), using \(O(q^2m^5|E|\log m/a^2)\) random-walk steps.

<a id="pdf-d5b902970e61-p015-b003"></a>
<!-- pdf-source: page=15; block=3; confidence=0.97 -->
The original Jerrum–Sinclair bound is \(O(q^3m^6|E|\log^2m/a^2)\) under the cited eigenvalue-gap bound. A further factor-\(O(m)\) improvement via Lemma 4.1 is limited by the cost of reliably estimating each stage parameter \(c(j)\).

<a id="pdf-d5b902970e61-p015-b004"></a>
<!-- pdf-source: page=15; block=4; confidence=0.99 -->
## 5. Entropy of sources

<a id="pdf-d5b902970e61-p015-b005"></a>
<!-- pdf-source: page=15; block=5; confidence=0.99 -->
For an unweighted undirected graph $G$, let $\epsilon$ be its eigenvalue gap and define its nonuniformity by $\nu=\max_{x,y}\pi(x)/\pi(y)$. Let $M$ be twice the number of edges of $G$, and let $P=(p_{ij})$ be the transition matrix for the random walk on $G$. For all $i,j$, $p_{ij}=1/d_i$ if $\{i,j\}\in E$ and $0$ otherwise, where $d_i$ is the degree of vertex $i$. Then $\pi(i)=d_i/\sum_jd_j=d_i/M$; therefore, $M\ge\max_i1/\pi(i)\ge\nu$. Let $x_0,x_1,\ldots$ be a random walk starting from the stationary distribution, and consider $X=x_1,x_2,\ldots$ as an information source.

<a id="pdf-d5b902970e61-p015-b006"></a>
<!-- pdf-source: page=15; block=6; confidence=0.99 -->
### The random walk as an information source

<a id="pdf-d5b902970e61-p015-b007"></a>
<!-- pdf-source: page=15; block=7; confidence=0.96 -->
For a source \(Y=(y_1,y_2,\ldots)\), entropy is \(H(Y)=\lim_{n\to\infty}\mathbb E H[y_n\mid y_1,\ldots,y_{n-1}]\). For the stationary graph walk, equation (5.1) states \(H(X)=\mathbb E H(x_1\mid x_0)=-\mathbb E\log_2 p_{x_0x_1}=\mathbb E_\pi\log_2 d_{x_0}\).

<a id="pdf-d5b902970e61-p015-b008"></a>
<!-- pdf-source: page=15; block=8; confidence=0.91 -->
The Shannon–McMillan theorem is invoked under the walk's ergodicity to motivate rapid entropy estimation and a coding error-exponent bound; the preceding introduction claims an \(O(\log|G|)\)-step estimate for constant expansion and nonuniformity.

<a id="pdf-d5b902970e61-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.99 -->
For fixed block length $n$, typical source sequences number about $2^{nH(Y)}$ and each has probability about $2^{-nH(Y)}$; the probability outside this typical set tends to zero.

<a id="pdf-d5b902970e61-p016-b002"></a>
<!-- pdf-source: page=16; block=2; confidence=0.99 -->
For a length-$n$ sequence $x_1,\ldots,x_n$ generated by source $X$, define $V_n=-\frac1n\log_2\Pr[x_1,\ldots,x_n]$.

<a id="pdf-d5b902970e61-p016-b003"></a>
<!-- pdf-source: page=16; block=3; confidence=0.99 -->
**Theorem 5.1.** Let $X$ be the information source generated by the random walk on $G$. Let $x_1,\ldots,x_n$ be a finite sequence generated by $X$, with empirical entropy $V_n$. Then
\[
\Pr[|V_n-H(X)|\ge\gamma]\le4e^{-(\gamma-(\log_2 M)/n)^2n\epsilon/(20\log_2^2\nu)}. \tag{5.2}
\]

<a id="pdf-d5b902970e61-p016-b004"></a>
<!-- pdf-source: page=16; block=4; confidence=0.84 -->
**Proof.** Set $g(x)=\log_2 d_x$ and $f(x)=g(x)-\min_y g(y)$. Then $\|f\|_\infty=\log_2\nu$ and, by (5.1), $\mathbb E_\pi f=H(X)-\min_y g(y)$. With $t_n=\sum_{i=1}^n f(x_i)$,
\[
V_n-\min_y g(y)=\frac{t_n}{n}+\frac{\log_2(1/\pi(x_1))}{n}-\frac{\log_2 d_{x_n}}{n}.
\]
Using (2.2) and Remark (i) after Theorem 2.1 bounds the upper tail by
\[
\Pr[V_n-H(X)\ge\gamma]\le 2\exp\!\left(-\left(\frac{\gamma-(\log_2 M)/n}{(\log_2\nu)/n}\right)^2\frac{\epsilon}{20n}\right)
=2e^{-\frac{(\gamma-(\log_2 M)/n)^2n\epsilon}{20\log_2^2\nu}}.
\]
The lower tail is bounded similarly; adding the two yields (5.2).

<a id="pdf-d5b902970e61-p016-b005"></a>
<!-- pdf-source: page=16; block=5; confidence=0.98 -->
A vertex labeling $\chi:V(G)\to\{0,\ldots,k-1\}$ is unifilar when no vertex is adjacent to two or more vertices of the same label. For the label sequence $y_i=\chi(x_i)$, the entropy formula (5.1) and empirical entropy definition remain applicable.

<a id="pdf-d5b902970e61-p016-b006"></a>
<!-- pdf-source: page=16; block=6; confidence=0.99 -->
**Corollary 5.2.** Let $V_n$ denote the empirical entropy of $y_1,\ldots,y_n$. Then
\[
\Pr[|V_n-H(Y)|\ge\gamma]\le4e^{-(\gamma-(\log_2(k|G|))/n)^2n\epsilon/(20\log_2^2 k)}. \tag{5.3}
\]

<a id="pdf-d5b902970e61-p016-b007"></a>
<!-- pdf-source: page=16; block=7; confidence=0.96 -->
The bound gives a computable finite-$n$ error-exponent estimate. Estimating $H(Y)$ within additive error $\gamma$ and failure probability $\delta$ takes $O(\log_2 k\,\log(1/\delta)\,\log(k|G|)/(\epsilon\gamma^2))$ walk length; for constant $k$ and expansion, this is $O(\log(1/\delta)\log|G|/\gamma^2)$.

<a id="pdf-d5b902970e61-p017-b001"></a>
<!-- pdf-source: page=17; block=1; confidence=0.99 -->
## 6. Further work

<a id="pdf-d5b902970e61-p017-b002"></a>
<!-- pdf-source: page=17; block=2; confidence=0.95 -->
A deviation lower bound complementing Theorem 2.1 should depend on the set $A$, not only on $\pi(A)$; in a barbell graph, a set on one side of the handle can have a larger deviation probability than one spread across both sides. For weighted graphs, entropy estimation requires expectations of edge functions under an induced edge-chain, which is not time-reversible, so the stated Chernoff bound does not directly apply. A further goal is estimating entropy for a binary source from a possibly nonunifilar labeled Markov chain.

<a id="pdf-d5b902970e61-p017-b003"></a>
<!-- pdf-source: page=17; block=3; confidence=0.98 -->
The author acknowledges colleagues and collaborators for advising, discussions, references, and comments.

<a id="pdf-d5b902970e61-p017-b004"></a>
<!-- pdf-source: page=17; block=4; confidence=0.99 -->
## References

<a id="pdf-d5b902970e61-p017-b005"></a>
<!-- pdf-source: page=17; block=5; confidence=0.99 -->
Bibliography entries [Ahl] through [DFK] cite works on complex analysis, expanders, Markov chains, information theory, large deviations, approximation algorithms, and related topics.

<a id="pdf-d5b902970e61-p018-b001"></a>
<!-- pdf-source: page=18; block=1; confidence=0.99 -->
Bibliography entries [Fi] through [W] cite works on Markov-chain convergence, Chernoff bounds, hidden Markov chains, large deviations, counting and sampling algorithms, matrix theory, expanders, and eigenvalue problems.
