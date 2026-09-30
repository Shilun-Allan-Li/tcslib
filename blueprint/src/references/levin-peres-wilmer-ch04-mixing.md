<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: 70350d84fb7f89c058d2f56d7fc677ac57c8363f8e95d8df52de4d0e00d22763 -->

<a id="pdf-70350d84fb7f-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.98 -->
# Chapter 4. Introduction to Markov Chain Mixing

<a id="pdf-70350d84fb7f-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.95 -->
Overview of studying long-term behavior and speed of convergence of finite Markov chains. The chapter defines total variation distance (with several characterizations), proves the Convergence Theorem (Theorem 4.9) — that for an irreducible, aperiodic chain the distribution approaches the stationary distribution in total variation distance — then studies the effect of the initial distribution, defines mixing time, discusses chains with identical mixing, and proves an Ergodic Theorem (Theorem C.1) for Markov chains.

<a id="pdf-70350d84fb7f-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.98 -->
## 4.1. Total Variation Distance

<a id="pdf-70350d84fb7f-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.97 -->
**Definition (Total variation distance).** For probability distributions $\mu,\nu$ on $\mathcal{X}$,
$$\lVert\mu-\nu\rVert_{TV} = \max_{A\subseteq\mathcal{X}} |\mu(A)-\nu(A)|. \tag{4.1}$$
That is, the maximum difference between the probabilities the two distributions assign to a single event.

<a id="pdf-70350d84fb7f-p001-b005"></a>
<!-- pdf-source: page=1; block=5; confidence=0.95 -->
**Example 4.1.** Two-state chain (frog of Example 1.1) with transition matrix $\begin{pmatrix}1-p & p\\ q & 1-q\end{pmatrix}$ and stationary distribution $\pi=\left(\tfrac{q}{p+q},\tfrac{p}{p+q}\right)$. With start $\mu_0=(1,0)$ and $\Delta_t=\mu_t(e)-\pi(e)$, the four possible events give
$$\lVert\mu_t-\pi\rVert_{TV}=|\Delta_t|=|P^t(e,e)-\pi(e)|=|\pi(w)-P^t(e,w)|.$$
Since $\Delta_t=(1-p-q)^t\Delta_0$, the total variation distance decreases exponentially in $t$; note $(1-p-q)$ is an eigenvalue of $P$.

<a id="pdf-70350d84fb7f-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.94 -->
**Figure 4.1.** With $B=\{x:\mu(x)\ge\nu(x)\}$, Region I has area $\mu(B)-\nu(B)$ and Region II has area $\nu(B^c)-\mu(B^c)$. Since each of $\mu,\nu$ has total area 1, the two regions have equal area, which equals $\lVert\mu-\nu\rVert_{TV}$.

<a id="pdf-70350d84fb7f-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.93 -->
The definition (4.1) as a maximum over subsets is inconvenient for estimation; three alternative characterizations follow. Proposition 4.2 reduces the distance to a sum over the state space; Proposition 4.7 uses coupling to interpret $\lVert\mu-\nu\rVert_{TV}$ as how close two random variables realizing $\mu$ and $\nu$ can be forced to be identical.

<a id="pdf-70350d84fb7f-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.98 -->
**Proposition 4.2.** For probability distributions $\mu,\nu$ on $\mathcal{X}$,
$$\lVert\mu-\nu\rVert_{TV}=\tfrac12\sum_{x\in\mathcal{X}}|\mu(x)-\nu(x)|. \tag{4.2}$$

<a id="pdf-70350d84fb7f-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.96 -->
**Proof.** Let $B=\{x:\mu(x)\ge\nu(x)\}$ and $A\subset\mathcal{X}$ arbitrary. Then
$$\mu(A)-\nu(A)\le\mu(A\cap B)-\nu(A\cap B)\le\mu(B)-\nu(B), \tag{4.3}$$
the first inequality since any $x\in A\cap B^c$ has $\mu(x)-\nu(x)<0$, the second since adding elements of $B$ cannot decrease the difference. Parallel reasoning gives
$$\nu(A)-\mu(A)\le\nu(B^c)-\mu(B^c). \tag{4.4}$$
The right-hand bounds of (4.3) and (4.4) are equal (Figure 4.1), and taking $A=B$ (or $B^c$) attains them, so
$$\lVert\mu-\nu\rVert_{TV}=\tfrac12[\mu(B)-\nu(B)+\nu(B^c)-\mu(B^c)]=\tfrac12\sum_{x}|\mu(x)-\nu(x)|.\ \blacksquare$$

<a id="pdf-70350d84fb7f-p002-b005"></a>
<!-- pdf-source: page=2; block=5; confidence=0.97 -->
**Remark 4.3.** The proof also yields the identity
$$\lVert\mu-\nu\rVert_{TV}=\sum_{x:\,\mu(x)\ge\nu(x)}[\mu(x)-\nu(x)]. \tag{4.5}$$

<a id="pdf-70350d84fb7f-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.97 -->
**Remark 4.4.** By Proposition 4.2 and the triangle inequality for reals, total variation distance satisfies the triangle inequality: for distributions $\mu,\nu,\eta$,
$$\lVert\mu-\nu\rVert_{TV}\le\lVert\mu-\eta\rVert_{TV}+\lVert\eta-\nu\rVert_{TV}. \tag{4.6}$$

<a id="pdf-70350d84fb7f-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.97 -->
**Proposition 4.5.** For probability distributions $\mu,\nu$ on $\mathcal{X}$,
$$\lVert\mu-\nu\rVert_{TV}=\tfrac12\sup\left\{\sum_{x}f(x)\mu(x)-\sum_{x}f(x)\nu(x)\;:\;\max_{x}|f(x)|\le 1\right\}. \tag{4.7}$$

<a id="pdf-70350d84fb7f-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.95 -->
**Proof.** If $\max_x|f(x)|\le1$, then $\tfrac12\left|\sum_x f(x)\mu(x)-\sum_x f(x)\nu(x)\right|\le\tfrac12\sum_x|\mu(x)-\nu(x)|=\lVert\mu-\nu\rVert_{TV}$, so the RHS of (4.7) is $\le\lVert\mu-\nu\rVert_{TV}$. Conversely define $f^\star(x)=1$ if $\mu(x)\ge\nu(x)$ and $-1$ otherwise. Then
$$\tfrac12\Big[\sum_x f^\star(x)\mu(x)-\sum_x f^\star(x)\nu(x)\Big]=\tfrac12\Big[\sum_{\mu\ge\nu}(\mu(x)-\nu(x))+\sum_{\nu>\mu}(\nu(x)-\mu(x))\Big],$$
which by (4.5) equals $\lVert\mu-\nu\rVert_{TV}$; hence the RHS of (4.7) is $\ge\lVert\mu-\nu\rVert_{TV}$. $\blacksquare$

<a id="pdf-70350d84fb7f-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.98 -->
## 4.2. Coupling and Total Variation Distance

<a id="pdf-70350d84fb7f-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.97 -->
**Definition (Coupling).** A coupling of probability distributions $\mu,\nu$ is a pair of random variables $(X,Y)$ on a single probability space whose marginals are $\mu$ and $\nu$: $\mathbb{P}\{X=x\}=\mu(x)$ and $\mathbb{P}\{Y=y\}=\nu(y)$.

<a id="pdf-70350d84fb7f-p003-b006"></a>
<!-- pdf-source: page=3; block=6; confidence=0.90 -->
**Example 4.6.** Let $\mu,\nu$ both be the fair-coin measure giving weight $1/2$ to each element of $\{0,1\}$. (i) One coupling takes $(X,Y)$ to be independent coins, so $\mathbb{P}\{X=x,Y=y\}=1/4$ for all $x,y\in\{0,1\}$. [Text ends mid-example.]

<a id="pdf-70350d84fb7f-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.94 -->
Example 4.6(ii): with $Y=X$ a fair coin toss, $\mathbb P\{X=Y=0\}=\mathbb P\{X=Y=1\}=1/2$ and $\mathbb P\{X\neq Y\}=0$. A coupling $(X,Y)$ of $\mu,\nu$ has joint law $q(x,y)=\mathbb P\{X=x,Y=y\}$ whose marginals are $\sum_y q(x,y)=\mu(x)$ and $\sum_x q(x,y)=\nu(y)$. Conversely any $q$ on $\mathcal X\times\mathcal X$ with these marginals arises from some pair $(X,Y)$, a coupling of $\mu,\nu$. Thus a coupling is equivalently a pair of random variables on a common space or a distribution $q$ on $\mathcal X\times\mathcal X$.

<a id="pdf-70350d84fb7f-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.95 -->
Coupling (i) corresponds to $q_1(x,y)=\tfrac14$ for all $(x,y)\in\{0,1\}^2$. Coupling (ii) corresponds to $q_2(x,y)=\tfrac12$ at $(0,0)$ and $(1,1)$, and $0$ at $(0,1)$ and $(1,0)$.

<a id="pdf-70350d84fb7f-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.90 -->
Any $\mu,\nu$ admit an independent coupling, but when $\mu\neq\nu$ one cannot force $X=Y$ always; total variation distance measures how close a coupling can come.

<a id="pdf-70350d84fb7f-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.96 -->
**Proposition 4.7.** For probability distributions $\mu,\nu$ on $\mathcal X$,
$$\lVert\mu-\nu\rVert_{TV}=\inf\{\mathbb P\{X\neq Y\}:(X,Y)\text{ is a coupling of }\mu,\nu\}. \tag{4.8}$$

<a id="pdf-70350d84fb7f-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.95 -->
**Remark 4.8.** The infimum in (4.8) is attained by some coupling, called an *optimal* coupling.

<a id="pdf-70350d84fb7f-p004-b006"></a>
<!-- pdf-source: page=4; block=6; confidence=0.93 -->
**Proof (part 1).** For any coupling $(X,Y)$ and event $A\subset\mathcal X$,
$$\mu(A)-\nu(A)=\mathbb P\{X\in A\}-\mathbb P\{Y\in A\}\ \ (4.9)\ \le\ \mathbb P\{X\in A,\,Y\notin A\}\ \ (4.10)\ \le\ \mathbb P\{X\neq Y\}\ \ (4.11),$$
the first inequality by dropping the term $\{X\notin A,Y\in A\}$. Hence $\lVert\mu-\nu\rVert_{TV}\le\inf\{\mathbb P\{X\neq Y\}\}$ over couplings (4.12).

<a id="pdf-70350d84fb7f-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.92 -->
Figure 4.2: regions I and II each have area $\lVert\mu-\nu\rVert_{TV}$, so region III (the overlap) has area $1-\lVert\mu-\nu\rVert_{TV}$.

<a id="pdf-70350d84fb7f-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.90 -->
**Proof (cont.).** It suffices to build a coupling with $\mathbb P\{X\neq Y\}=\lVert\mu-\nu\rVert_{TV}$, forcing $X=Y$ as often as possible. Region III is bounded by $\mu(x)\wedge\nu(x)=\min\{\mu(x),\nu(x)\}$. Informally: pick a point in $\text{I}\cup\text{III}$ and set $X$ to its $x$-coordinate; if in III set $Y=X$; if in I, independently pick a point from region II and set $Y$ to its $x$-coordinate (then $X\neq Y$ as I, II are disjoint).

<a id="pdf-70350d84fb7f-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.92 -->
**Proof (cont.).** Set $p=\sum_{x}\mu(x)\wedge\nu(x)$. Writing $\sum_x\mu\wedge\nu=\sum_{x:\mu(x)\le\nu(x)}\mu(x)+\sum_{x:\mu(x)>\nu(x)}\nu(x)$ and adding/subtracting $\sum_{x:\mu(x)>\nu(x)}\mu(x)$ gives $\sum_x\mu\wedge\nu=1-\sum_{x:\mu(x)>\nu(x)}[\mu(x)-\nu(x)]$. By (4.5), $\sum_x\mu(x)\wedge\nu(x)=1-\lVert\mu-\nu\rVert_{TV}=p$ (4.13).

<a id="pdf-70350d84fb7f-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.93 -->
**Proof (cont.).** Flip a coin with $\mathbb P(\text{heads})=p$. (i) If heads, draw $Z$ from $\gamma_{III}(x)=\dfrac{\mu(x)\wedge\nu(x)}{p}$ and set $X=Y=Z$.

<a id="pdf-70350d84fb7f-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.93 -->
**Proof (cont.).** (ii) If tails, choose $X\sim\gamma_I(x)=\dfrac{\mu(x)-\nu(x)}{\lVert\mu-\nu\rVert_{TV}}$ when $\mu(x)>\nu(x)$ (else $0$), and independently $Y\sim\gamma_{II}(x)=\dfrac{\nu(x)-\mu(x)}{\lVert\mu-\nu\rVert_{TV}}$ when $\nu(x)>\mu(x)$ (else $0$). By (4.5) both $\gamma_I,\gamma_{II}$ are probability distributions.

<a id="pdf-70350d84fb7f-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.93 -->
**Proof (concl.).** Since $p\gamma_{III}+(1-p)\gamma_I=\mu$ and $p\gamma_{III}+(1-p)\gamma_{II}=\nu$, $X\sim\mu$ and $Y\sim\nu$. On tails $X\neq Y$ ($\gamma_I,\gamma_{II}$ have disjoint support), so $X=Y$ iff heads; hence $\mathbb P\{X\neq Y\}=\lVert\mu-\nu\rVert_{TV}$. $\blacksquare$

<a id="pdf-70350d84fb7f-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.95 -->
## 4.3. The Convergence Theorem

<a id="pdf-70350d84fb7f-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.90 -->
Irreducible aperiodic Markov chains converge to their stationary distribution; aperiodicity is necessary (even $n$-cycle, Example 1.4). The proof here decomposes the chain into a mixture of repeated i.i.d. sampling from $\pi$ and another Markov chain; Exercise 5.1 gives an alternative proof via two coupled copies.

<a id="pdf-70350d84fb7f-p006-b005"></a>
<!-- pdf-source: page=6; block=5; confidence=0.96 -->
**Theorem 4.9 (Convergence Theorem).** If $P$ is irreducible and aperiodic with stationary distribution $\pi$, then there exist $\alpha\in(0,1)$ and $C>0$ such that
$$\max_{x\in\mathcal X}\lVert P^t(x,\cdot)-\pi\rVert_{TV}\le C\alpha^{t}. \tag{4.14}$$

<a id="pdf-70350d84fb7f-p006-b006"></a>
<!-- pdf-source: page=6; block=6; confidence=0.92 -->
**Proof.** By Proposition 1.7 there is $r$ with $P^r$ having strictly positive entries. Let $\Pi$ be the $|\mathcal X|$-row matrix each row equal to $\pi$. For sufficiently small $\delta>0$, $P^r(x,y)\ge\delta\pi(y)$ for all $x,y$. With $\theta=1-\delta$, $P^r=(1-\theta)\Pi+\theta Q$ (4.15) defines a stochastic matrix $Q$. One checks $M\Pi=\Pi$ for any stochastic $M$, and $\Pi M=\Pi$ whenever $\pi M=\pi$. By induction, $P^{rk}=(1-\theta^k)\Pi+\theta^k Q^k$ (4.16).

<a id="pdf-70350d84fb7f-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.97 -->
**Proof (continued).** Establishes claim (4.16), $P^{rk} = (1-\theta^k)\Pi + \theta^k Q^k$, by induction on $k\ge 1$. Base case $k=1$ holds by (4.15). Assuming (4.16) at $k=n$: $P^{r(n+1)} = P^{rn}P^r = [(1-\theta^n)\Pi + \theta^n Q^n]P^r$ (4.17). Expanding $P^r$ via (4.15) gives $P^{r(n+1)} = (1-\theta^n)\Pi P^r + (1-\theta)\theta^n Q^n\Pi + \theta^{n+1}Q^n Q$ (4.18). Using $\Pi P^r = \Pi$ and $Q^n\Pi = \Pi$ yields $P^{r(n+1)} = (1-\theta^{n+1})\Pi + \theta^{n+1}Q^{n+1}$ (4.19), proving (4.16) for all $k$. Multiplying by $P^j$ and rearranging: $P^{rk+j} - \Pi = \theta^k(Q^k P^j - \Pi)$ (4.20). Summing absolute values over row $x_0$ and dividing by 2, and bounding the second factor by the maximal TV distance $\le 1$, gives $\lVert P^{rk+j}(x_0,\cdot) - \pi\rVert_{TV} \le \theta^k$ (4.21). Taking $\alpha = \theta^{1/r}$ and $C = 1/\theta$ completes the proof. $\blacksquare$

<a id="pdf-70350d84fb7f-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.95 -->
**Section 4.4. Standardizing Distance from Stationarity.** Motivates standardized measures of distance to stationarity for bounding the maximal distance between $P^t(x_0,\cdot)$ and $\pi$.

<a id="pdf-70350d84fb7f-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.95 -->
**Definition.** $d(t) := \max_{x\in\mathcal{X}} \lVert P^t(x,\cdot) - \pi\rVert_{TV}$ (4.22), the maximal distance to stationarity. $\bar d(t) := \max_{x,y\in\mathcal{X}} \lVert P^t(x,\cdot) - P^t(y,\cdot)\rVert_{TV}$ (4.23), the maximal distance between two chains started from different states.

<a id="pdf-70350d84fb7f-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.97 -->
**Lemma 4.10.** For $d(t)$ and $\bar d(t)$ as in (4.22), (4.23): $d(t) \le \bar d(t) \le 2\,d(t)$ (4.24).

<a id="pdf-70350d84fb7f-p007-b005"></a>
<!-- pdf-source: page=7; block=5; confidence=0.94 -->
**Proof.** The bound $\bar d(t) \le 2 d(t)$ is immediate from the triangle inequality for TV distance. For $d(t) \le \bar d(t)$: stationarity gives $\pi(A) = \sum_{y\in\mathcal{X}} \pi(y) P^t(y,A)$ for any set $A$. Hence $|P^t(x,A) - \pi(A)| = \bigl|\sum_{y} \pi(y)[P^t(x,A) - P^t(y,A)]\bigr| \le \sum_{y}\pi(y)\lVert P^t(x,\cdot) - P^t(y,\cdot)\rVert_{TV} \le \bar d(t)$ (4.25). Maximizing the left side over $x$ and $A$ gives $d(t) \le \bar d(t)$. $\blacksquare$

<a id="pdf-70350d84fb7f-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.93 -->
Let $\mathcal{P}$ be the set of all probability distributions on $\mathcal{X}$. Exercise 4.1 asks to prove: $d(t) = \sup_{\mu\in\mathcal{P}} \lVert \mu P^t - \pi\rVert_{TV}$ and $\bar d(t) = \sup_{\mu,\nu\in\mathcal{P}} \lVert \mu P^t - \nu P^t\rVert_{TV}$.

<a id="pdf-70350d84fb7f-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.97 -->
**Lemma 4.11.** $\bar d$ is submultiplicative: $\bar d(s+t) \le \bar d(s)\,\bar d(t)$.

<a id="pdf-70350d84fb7f-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.93 -->
**Proof.** Fix $x,y$ and let $(X_s, Y_s)$ be the optimal coupling of $P^s(x,\cdot)$ and $P^s(y,\cdot)$ (Proposition 4.7), so $\lVert P^s(x,\cdot) - P^s(y,\cdot)\rVert_{TV} = \mathbb{P}\{X_s \ne Y_s\}$ (4.26). Then $P^{s+t}(x,w) = \sum_z \mathbb{P}\{X_s = z\}P^t(z,w) = \mathbb{E}(P^t(X_s,w))$ (4.27). Summing over $w\in A$: $P^{s+t}(x,A) - P^{s+t}(y,A) = \mathbb{E}(P^t(X_s,A) - P^t(Y_s,A)) \le \mathbb{E}(\bar d(t)\mathbf{1}\{X_s\ne Y_s\}) = \mathbb{P}\{X_s\ne Y_s\}\bar d(t)$ (4.28). By (4.26) this is at most $\bar d(s)\bar d(t)$. $\blacksquare$

<a id="pdf-70350d84fb7f-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.95 -->
**Remark 4.12.** Theorem 4.9 can be deduced from Lemma 4.11; one needs $\bar d(s) < 1$ for some $s$, which holds since $P^s$ has all positive entries for some $s$.

<a id="pdf-70350d84fb7f-p008-b005"></a>
<!-- pdf-source: page=8; block=5; confidence=0.93 -->
Exercise 4.2 implies $\bar d(t)$ is non-increasing in $t$. By Lemmas 4.10 and 4.11, for positive integers $c,t$: $d(ct) \le \bar d(ct) \le \bar d(t)^c$ (4.29).

<a id="pdf-70350d84fb7f-p008-b006"></a>
<!-- pdf-source: page=8; block=6; confidence=0.95 -->
**Section 4.5. Mixing Time.** Introduces a parameter measuring the time for the distance to stationarity to become small.

<a id="pdf-70350d84fb7f-p008-b007"></a>
<!-- pdf-source: page=8; block=7; confidence=0.96 -->
**Definition.** Mixing time: $t_{mix}(\varepsilon) := \min\{t : d(t) \le \varepsilon\}$ (4.30), and $t_{mix} := t_{mix}(1/4)$ (4.31).

<a id="pdf-70350d84fb7f-p008-b008"></a>
<!-- pdf-source: page=8; block=8; confidence=0.93 -->
By Lemma 4.10 and (4.29), for positive integer $\ell$: $d(\ell\, t_{mix}(\varepsilon)) \le \bar d(t_{mix}(\varepsilon))^\ell \le (2\varepsilon)^\ell$ (4.32). Taking $\varepsilon = 1/4$ gives $d(\ell\, t_{mix}) \le 2^{-\ell}$ (4.33) and $t_{mix}(\varepsilon) \le \lceil \log_2 \varepsilon^{-1}\rceil\, t_{mix}$ (4.34).

<a id="pdf-70350d84fb7f-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.90 -->
The value $1/4$ in (4.31) is arbitrary, but $\varepsilon < 1/2$ is needed for the bound $d(\ell\, t_{mix}(\varepsilon)) \le (2\varepsilon)^\ell$ (4.32) to be meaningful and to obtain an inequality of the form (4.34); see Exercise 4.3 for a small improvement. Rigorous upper bounds on mixing times give confidence in simulations and randomized algorithms.

<a id="pdf-70350d84fb7f-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.92 -->
**Section 4.6. Mixing and Time Reversal.** For a distribution $\mu$ on a group $G$, the reversed distribution is $\hat\mu(g) := \mu(g^{-1})$ for all $g\in G$. If $P$ is the transition matrix of the random walk with increment distribution $\mu$, then the walk with increment distribution $\hat\mu$ is exactly the time reversal $\hat P$ (defined in (1.32)) of $P$. When $\hat\mu = \mu$ the walk is reversible ($P = \hat P$, Proposition 2.14); even otherwise, forward and reversed walks are at the same distance from stationarity.

<a id="pdf-70350d84fb7f-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.95 -->
**Lemma 4.13.** Let $P$ be the transition matrix of a random walk on a group $G$ with increment distribution $\mu$, and $\hat P$ that of the walk with increment distribution $\hat\mu$. Let $\pi$ be the uniform distribution on $G$. Then for any $t \ge 0$: $\lVert P^t(\mathrm{id},\cdot) - \pi\rVert_{TV} = \lVert \hat P^t(\mathrm{id},\cdot) - \pi\rVert_{TV}$.

<a id="pdf-70350d84fb7f-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.92 -->
**Proof.** Let $(X_t) = (\mathrm{id}, X_1, \dots)$ have transition matrix $P$ and $X_0 = \mathrm{id}$; write $X_k = g_k g_{k-1}\cdots g_1$ with $g_i$ i.i.d. from $\mu$. Let $(Y_t)$ have transition matrix $\hat P$ with increments $h_i$ i.i.d. from $\hat\mu$. For fixed $a_1,\dots,a_t \in G$: $\mathbb{P}\{g_1=a_1,\dots,g_t=a_t\} = \mathbb{P}\{h_1 = a_t^{-1}, \dots, h_t = a_1^{-1}\}$, by definition of $\hat P$. Summing over strings with $a_t a_{t-1}\cdots a_1 = a$ gives $P^t(\mathrm{id}, a) = \hat P^t(\mathrm{id}, a^{-1})$. Hence $\sum_{a\in G} |P^t(\mathrm{id},a) - |G|^{-1}| = \sum_{a\in G} |\hat P^t(\mathrm{id}, a^{-1}) - |G|^{-1}| = \sum_{a\in G} |\hat P^t(\mathrm{id}, a) - |G|^{-1}|$, which with Proposition 4.2 gives the result. $\blacksquare$

<a id="pdf-70350d84fb7f-p009-b005"></a>
<!-- pdf-source: page=9; block=5; confidence=0.95 -->
**Corollary 4.14.** If $t_{mix}$ is the mixing time of a random walk on a group and $\widehat{t_{mix}}$ is the mixing time of the reversed walk, then $t_{mix} = \widehat{t_{mix}}$.

<a id="pdf-70350d84fb7f-p009-b006"></a>
<!-- pdf-source: page=9; block=6; confidence=0.95 -->
Reversing a Markov chain can also significantly change the mixing time; the winning streak is such an example, discussed in Section 5.3.5.

<a id="pdf-70350d84fb7f-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.95 -->
**Section 4.7. ℓ^p Distance and Mixing.** Introduces alternative distances between distributions; material deferred to Chapter 10.

<a id="pdf-70350d84fb7f-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.97 -->
**Definition.** For a distribution π on X and 1 ≤ p ≤ ∞, the ℓ^p(π) norm of f : X → R is ‖f‖_p := [∑_{y∈X} |f(y)|^p π(y)]^{1/p} for 1 ≤ p < ∞, and ‖f‖_∞ := max_{y∈X} |f(y)| for p = ∞. The scalar product is ⟨f,g⟩_π := ∑_{x∈X} f(x)g(x)π(x). For an irreducible transition matrix P with stationary distribution π, define q_t(x,y) := P^t(x,y)/π(y); when P is reversible, q_t(x,y) = q_t(y,x). Also ⟨q_t(x,·), 1⟩_π = ∑_y q_t(x,y)π(y) = 1 (4.35).

<a id="pdf-70350d84fb7f-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.96 -->
**Definition.** The ℓ^p-distance is d^{(p)}(t) := max_{x∈X} ‖q_t(x,·) − 1‖_p (4.36). Proposition 4.2 gives d^{(1)}(t) = 2d(t). It is submultiplicative: d^{(p)}(t+s) ≤ d^{(p)}(t) d^{(p)}(s) (proved as Lemma 4.18). Since ℓ^p norms are non-decreasing in p (Exercise 4.5), 2d(t) = d^{(1)}(t) ≤ d^{(2)}(t) ≤ d^{(∞)}(t) (4.37). Focus is on p = 1, 2, ∞.

<a id="pdf-70350d84fb7f-p010-b004"></a>
<!-- pdf-source: page=10; block=4; confidence=0.97 -->
**Proposition 4.15.** For a reversible Markov chain, d^{(∞)}(2t) = [d^{(2)}(t)]^2 = max_{x∈X} [q_{2t}(x,x) − 1] (4.38).

<a id="pdf-70350d84fb7f-p010-b005"></a>
<!-- pdf-source: page=10; block=5; confidence=0.96 -->
**Proof.** From P^{2t}(x,y) = ∑_{z∈X} P^t(x,z)P^t(z,y), dividing by π(y) and using reversibility gives q_{2t}(x,y) = ∑_{z} [P^t(x,z)/π(z)][P^t(z,y)/π(y)] π(z) = ⟨q_t(x,·), q_t(y,·)⟩_π (4.39). Using (4.35), ⟨q_t(x,·) − 1, q_t(y,·) − 1⟩_π = ⟨q_t(x,·), q_t(y,·)⟩_π − ⟨1, q_t(y,·)⟩_π − ⟨q_t(x,·), 1⟩_π + 1 = q_{2t}(x,y) − 1 (4.40). [Continues on next page.]

<a id="pdf-70350d84fb7f-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.96 -->
**Proof (continued).** Setting x = y in (4.40) gives ‖q_t(x,·) − 1‖_2^2 = q_{2t}(x,x) − 1 (4.41); maximizing over x yields the right-hand equality in (4.38). By (4.40) and Cauchy–Schwarz, |q_{2t}(x,y) − 1| ≤ ‖q_t(x,·) − 1‖_2 · ‖q_t(y,·) − 1‖_2 = √(q_{2t}(x,x) − 1) · √(q_{2t}(y,y) − 1) (4.42). Hence d^{(∞)}(2t) = max_{x,y} |q_{2t}(x,y) − 1| ≤ max_x [q_{2t}(x,x) − 1] (4.43). Taking x = y gives equality in (4.43), proving the proposition. ∎

<a id="pdf-70350d84fb7f-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.95 -->
**Definition.** The ℓ^p-mixing time is t^{(p)}_mix(ε) := inf{t ≥ 0 : d^{(p)}(t) ≤ ε} (4.44). Since d^{(1)}(t) = 2d(t), taking ε = 1/2 gives t^{(1)}_mix(1/2) = t_mix. The parameter t^{(∞)}_mix is called the uniform mixing time. By submultiplicativity (Lemma 4.18), d^{(p)}(k t^{(p)}_mix) ≤ 2^{−k}, so t^{(p)}_mix(ε) ≤ ⌈log_2 ε^{−1}⌉ t^{(p)}_mix.

<a id="pdf-70350d84fb7f-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.95 -->
**Exercise 4.1.** Prove d(t) = sup_μ ‖μP^t − π‖_TV and d̄(t) = sup_{μ,ν} ‖μP^t − νP^t‖_TV, where μ, ν range over probability distributions on finite X.

<a id="pdf-70350d84fb7f-p011-b004"></a>
<!-- pdf-source: page=11; block=4; confidence=0.95 -->
**Exercise 4.2.** For transition matrix P and any distributions μ, ν on X, prove ‖μP − νP‖_TV ≤ ‖μ − ν‖_TV. Deduce ‖μP^{t+1} − π‖_TV ≤ ‖μP^t − π‖_TV, and hence for t ≥ 0: d(t+1) ≤ d(t) and d̄(t+1) ≤ d̄(t).

<a id="pdf-70350d84fb7f-p011-b005"></a>
<!-- pdf-source: page=11; block=5; confidence=0.95 -->
**Exercise 4.3.** Prove that for t, s ≥ 0, d(t+s) ≤ d(t) d̄(s). Deduce that for k ≥ 2, t_mix(2^{−k}) ≤ (k−1) t_mix.

<a id="pdf-70350d84fb7f-p011-b006"></a>
<!-- pdf-source: page=11; block=6; confidence=0.93 -->
**Exercise 4.4.** For i = 1,…,n let μ_i, ν_i be measures on X_i; define product measures μ := ∏_{i=1}^n μ_i and ν := ∏_{i=1}^n ν_i on ∏_{i=1}^n X_i. Show ‖μ − ν‖_TV ≤ ∑_{i=1}^n ‖μ_i − ν_i‖_TV.

<a id="pdf-70350d84fb7f-p011-b007"></a>
<!-- pdf-source: page=11; block=7; confidence=0.96 -->
**Exercise 4.5.** Show that for any f : X → R, the map p ↦ ‖f‖_p is non-decreasing for p ≥ 1.

<a id="pdf-70350d84fb7f-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.90 -->
**Notes.** Convergence Theorem exposition follows Aldous–Diaconis (1986); an eigenvalue-based approach (Seneta 2006) is developed in Chapters 12–13; infinite state spaces in Chapter 21. Aldous (1983b, Lemma 3.5) parallels Lemma 4.11 and Exercise 4.2. Winning streak example from Lovász–Winkler (1998). Mixing may be defined via other distances, e.g. the separation distance (Chapter 6).

<a id="pdf-70350d84fb7f-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.95 -->
**Definition.** The Hellinger distance is d_H(μ,ν) := √(∑_{x∈X} (√μ(x) − √ν(x))^2) (4.45). It behaves well on products (cf. Exercise 20.7) and is used in Section 20.4 to bound mixing time for continuous product chains.

<a id="pdf-70350d84fb7f-p012-b003"></a>
<!-- pdf-source: page=12; block=3; confidence=0.90 -->
**Further reading.** Combinatorial view: Lovász (1993); analytic tools: Saloff-Coste (1997), Montenegro–Tetali (2006); Aldous–Fill (1999); also Sinclair (1993), Häggström (2002), Jerrum (2003), and Grinstead–Snell (1997, Ch. 11).

<a id="pdf-70350d84fb7f-p012-b004"></a>
<!-- pdf-source: page=12; block=4; confidence=0.95 -->
**Lemma 4.16 (Complements).** Generalizing Lemma 4.13 to transitive chains (Section 2.6.2): Let P be the transition matrix of a transitive Markov chain on X, let P̂ be its time reversal, and let π be uniform on X. Then ‖P̂^t(x,·) − π‖_TV = ‖P^t(x,·) − π‖_TV (4.46).

<a id="pdf-70350d84fb7f-p012-b005"></a>
<!-- pdf-source: page=12; block=5; confidence=0.90 -->
**Proof.** By transitivity, for every x,y ∈ X there is a bijection φ_{(x,y)} : X → X carrying x to y and preserving transition probabilities. For any x,y,t: ∑_{z} |P^t(x,z) − |X|^{−1}| = ∑_{z} |P^t(φ(x), φ(z)) − |X|^{−1}| = ∑_{z} |P^t(y,z) − |X|^{−1}| (4.47)–(4.48). Averaging over y: ∑_{z} |P^t(x,z) − |X|^{−1}| = (1/|X|) ∑_{y}∑_{z} |P^t(y,z) − |X|^{−1}| (4.49). Since π is uniform, P(y,z) = P̂(z,y), so P^t(y,z) = P̂^t(z,y); thus the right side equals (1/|X|) ∑_{y}∑_{z} |P̂^t(z,y) − |X|^{−1}| = (1/|X|) ∑_{z}∑_{y} |P̂^t(z,y) − |X|^{−1}| (4.50). [Argument concludes yielding (4.46).]

<a id="pdf-70350d84fb7f-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.90 -->
**Proof (continued).** By Exercise 2.8, $\hat{P}$ is also transitive, so (4.49) holds with $\hat{P}$ replacing $P$ and $z, y$ interchanging roles. Hence (4.51): $\sum_{z\in X}\big|P^t(x,z)-|X|^{-1}\big| = \sum_{y\in X}\big|\hat{P}^t(x,y)-|X|^{-1}\big|$. Dividing by 2 and applying Proposition 4.2 completes the proof. $\square$

<a id="pdf-70350d84fb7f-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.95 -->
**Remark 4.17.** The proof of Lemma 4.13 established an exact correspondence between forward and reversed trajectories, whereas that of Lemma 4.16 relied on averaging over the state space.

<a id="pdf-70350d84fb7f-p013-b003"></a>
<!-- pdf-source: page=13; block=3; confidence=0.92 -->
The distances $d^{(p)}$ are all submultiplicative, which diminishes the importance of the constant $\tfrac12$ in definition (4.44).

<a id="pdf-70350d84fb7f-p013-b004"></a>
<!-- pdf-source: page=13; block=4; confidence=0.95 -->
**Lemma 4.18.** The distance $d^{(p)}$ is submultiplicative: (4.52) $d^{(p)}(s+t) \le d^{(1)}(s)\,d^{(p)}(t) \le d^{(p)}(s)\,d^{(p)}(t)$.

<a id="pdf-70350d84fb7f-p013-b005"></a>
<!-- pdf-source: page=13; block=5; confidence=0.88 -->
**Proof.** Hölder's inequality: if $1/p+1/q=1$, then (4.53) $\|g\|_p = \max_{\|f\|_q\le 1}\big|\sum_{x\in X} f(x)g(x)\pi(x)\big|$ (cf. Folland (1999), Prop. 6.13). For $p=q=2$ this is Cauchy–Schwarz; for $p=\infty,q=1$ and $p=1,q=\infty$ it is elementary. From (4.53) and definition (4.36): (4.54) $d^{(p)}(t) = \max_{x\in X}\max_{\|f\|_q\le 1}\big|\sum_{y\in X} f(y)[q^t(x,y)-1]\pi(y)\big| = \max_{\|f\|_q\le 1}\max_{x\in X}|P^t f(x)-\pi(f)| = \max_{\|f\|_q\le 1}\|P^t f-\pi(f)\|_\infty$. Thus for every $g:X\to\mathbb{R}$, $\|P^s g-\pi(g)\|_\infty = \|P^s(g/\|g\|_q)-\pi(g/\|g\|_q)\|_\infty\cdot\|g\|_q \le d^{(p)}(s)\|g\|_q$. Applying this with $g=P^t f-\pi(f)$ and $p=1$, then using (4.54), yields $\|P^{t+s}f-\pi(f)\|_\infty \le d^{(1)}(s)\|P^t f-\pi(f)\|_\infty \le d^{(1)}(s)\,d^{(p)}(t)$. Maximizing over $f$ with $\|f\|_q\le 1$ and using (4.54) with $t+s$ in place of $t$ gives (4.52). $\square$
