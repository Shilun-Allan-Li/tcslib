<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: a6706e37c21a69694f85415c162324ed031eb33e675367aa04ee6abdf37ada97 -->

<a id="pdf-a6706e37c21a-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.98 -->
# An Elementary Proof of a Theorem of Johnson and Lindenstrauss

Sanjoy Dasgupta (AT&T Labs Research) and Anupam Gupta (Lucent Bell Labs). Received 16 Dec 2001; accepted 11 July 2002. *Random Struct. Alg.* 22:60–65, 2002.

<a id="pdf-a6706e37c21a-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.95 -->
**Abstract.** The Johnson–Lindenstrauss result [13] states that $n$ points in high-dimensional Euclidean space can be mapped into $O(\log n / \varepsilon^2)$ dimensions so that all pairwise distances are preserved up to a factor $(1 \pm \varepsilon)$. This note reproves it via elementary probabilistic techniques.

<a id="pdf-a6706e37c21a-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.90 -->
**Introduction.** The JL theorem [13]: any $n$-point subset of Euclidean space embeds into $k = O(\log n / \varepsilon^2)$ dimensions with pairwise distances distorted by at most a factor $(1 \pm \varepsilon)$, for any $0 < \varepsilon < 1$. Alon's near-matching lower bound: $n$ points with interpoint distances in $[1-\varepsilon, 1+\varepsilon]$ require at least $\Omega\!\left(\log n / (\varepsilon^2 \log(1/\varepsilon))\right)$ dimensions [1, §9]. Applications of JL are then listed (bi-Lipschitz graph embeddings [14], ...).

<a id="pdf-a6706e37c21a-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.90 -->
Further applications: approximate nearest-neighbor search [12], learning mixtures of Gaussians [5], database dimension reduction [2]. Proof history: the original JL proof projects onto a random $O(\log n/\varepsilon^2)$-dimensional subspace, preserving distances within $(1\pm\varepsilon)$ with positive probability; simplified by Frankl–Maehara [7,8]; similar randomized-algorithm proofs by Indyk–Motwani [12], Arriaga–Vempala [3], Achlioptas [2]; derandomizations in [6,15].

<a id="pdf-a6706e37c21a-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.97 -->
## 2. The Johnson–Lindenstrauss Theorem

<a id="pdf-a6706e37c21a-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.95 -->
**Theorem 2.1.** For any $0 < \varepsilon < 1$ and any integer $n$, let $k$ be a positive integer with
$$k \ge 4\left(\tfrac{\varepsilon^2}{2} - \tfrac{\varepsilon^3}{3}\right)^{-1} \ln n. \tag{2.1}$$
Then for any set $V$ of $n$ points in $\mathbb{R}^d$ there is a map $f : \mathbb{R}^d \to \mathbb{R}^k$ such that for all $u, v \in V$,
$$(1-\varepsilon)\,\lVert u - v\rVert^2 \;\le\; \lVert f(u) - f(v)\rVert^2 \;\le\; (1+\varepsilon)\,\lVert u - v\rVert^2.$$
Moreover $f$ can be found in randomized polynomial time.

<a id="pdf-a6706e37c21a-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.90 -->
Prior bounds: JL [13] originally gave lower bound $k = O(\log n)$; Frankl–Maehara [7] showed $k \ge 9(\varepsilon^2 - 2\varepsilon^3/3)^{-1}\ln n + 1$ suffices; Indyk–Motwani [12] and Achlioptas [2] give essentially the same bound as here. Strategy: show the squared length of a random unit vector projected onto a random $k$-dimensional subspace concentrates around its mean, so its (scaled) length is distorted by more than $(1\pm\varepsilon)$ only with probability $O(1/n^2)$; the theorem then follows by a union bound.

<a id="pdf-a6706e37c21a-p002-b005"></a>
<!-- pdf-source: page=2; block=5; confidence=0.93 -->
**Setup.** Estimating the length of a random unit vector projected onto a fixed $k$-dimensional subspace (taken as the span of the first $k$ coordinates). Let $X_1,\dots,X_d$ be i.i.d. Gaussian $N(0,1)$, and set $Y = \tfrac{1}{\lVert X\rVert}(X_1,\dots,X_d)$, which is uniform on the sphere $S^{d-1}$. Let $Z \in \mathbb{R}^k$ be the projection of $Y$ onto its first $k$ coordinates and $L = \lVert Z\rVert^2$.

<a id="pdf-a6706e37c21a-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.92 -->
The expected squared length is $\mu = \mathbb{E}[L] = k/d$. The next lemma shows $L$ is tightly concentrated around $\mu$.

<a id="pdf-a6706e37c21a-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.97 -->
**Lemma 2.2.** Let $k < d$. Then

**(a)** If $\beta < 1$, then
$$\Pr\!\left[L \le \tfrac{\beta k}{d}\right] \le \beta^{k/2}\left(1 + \tfrac{(1-\beta)k}{d-k}\right)^{(d-k)/2} \le \exp\!\left(\tfrac{k}{2}\,(1 - \beta + \ln \beta)\right).$$

**(b)** If $\beta > 1$, then
$$\Pr\!\left[L \ge \tfrac{\beta k}{d}\right] \le \beta^{k/2}\left(1 + \tfrac{(1-\beta)k}{d-k}\right)^{(d-k)/2} \le \exp\!\left(\tfrac{k}{2}\,(1 - \beta + \ln \beta)\right).$$

<a id="pdf-a6706e37c21a-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.90 -->
**Proof of Theorem 2.1.** If $d \le k$, the theorem is trivial. Else take a random $k$-dimensional subspace $S$, and let $v'_i$ be the projection of point $v_i \in V$ into $S$. Then, setting $L = \lVert v'_i - v'_j\rVert^2$ and $\mu = (k/d)\lVert v_i - v_j\rVert^2$ and applying Lemma 2.2(a), we get that
$$\begin{aligned}\Pr[L \le (1-\varepsilon)\mu] &\le \exp\!\left(\tfrac{k}{2}\big(1 - (1-\varepsilon) + \ln(1-\varepsilon)\big)\right)\\ &\le \exp\!\left(\tfrac{k}{2}\Big(\varepsilon - \big(\varepsilon + \tfrac{\varepsilon^2}{2}\big)\Big)\right) = \exp\!\left(-\tfrac{k\varepsilon^2}{4}\right)\\ &\le \exp(-2\ln n) = 1/n^2,\end{aligned}$$
where, in the second line, we have used the inequality $\ln(1-x) \le -x - x^2/2$, valid for all $0 \le x < 1$.

Similarly, we can apply Lemma 2.2(b) and the inequality $\ln(1+x) \le x - x^2/2 + x^3/3$ (which is valid for all $x \ge 0$) to get
$$\begin{aligned}\Pr[L \ge (1+\varepsilon)\mu] &\le \exp\!\left(\tfrac{k}{2}\big(1 - (1+\varepsilon) + \ln(1+\varepsilon)\big)\right)\\ &\le \exp\!\left(\tfrac{k}{2}\Big(-\varepsilon + \big(\varepsilon - \tfrac{\varepsilon^2}{2} + \tfrac{\varepsilon^3}{3}\big)\Big)\right) = \exp\!\left(-\tfrac{k(\varepsilon^2/2 - \varepsilon^3/3)}{2}\right)\\ &\le \exp(-2\ln n) = \tfrac{1}{n^2}.\end{aligned}$$

Now set the map $f(v_i) = (\sqrt{d/k})\,v'_i$. By the above calculations, for some fixed pair $i,j$, the chance that the distortion $\lVert f(v_i)-f(v_j)\rVert^2 / \lVert v_i - v_j\rVert^2$ does not lie in the range $[(1-\varepsilon),(1+\varepsilon)]$ is at most $2/n^2$. Using the trivial union bound, the chance that some pair of points suffers a large distortion is at most $\binom{n}{2}\times 2/n^2 = 1 - 1/n$. Hence $f$ has the desired properties with probability at least $1/n$. Repeating this projection $O(n)$ times can boost the success probability to the desired constant, giving us the claimed randomized polynomial time algorithm. $\blacksquare$

<a id="pdf-a6706e37c21a-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.90 -->
Remaining task: prove Lemma 2.2 using standard large-deviation (Chernoff/Hoeffding-type) bounds on sums of random variables [4, 9].

<a id="pdf-a6706e37c21a-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.93 -->
**Proof of Lemma 2.2(a).** We use the easily-proved fact that if $X \sim N(0,1)$, then $E[e^{sX^2}] = 1/\sqrt{1-2s}$, for $-\infty < s < \tfrac12$. We now prove that
$$\Pr\!\big[d(X_1^2+\cdots+X_k^2) \le k\beta(X_1^2+\cdots+X_d^2)\big] \le \beta^{k/2}\Big(1+\tfrac{k(1-\beta)}{d-k}\Big)^{(d-k)/2}. \tag{2.2}$$
Note that this is just another way of stating Lemma 2.2(a). However, this can be shown by the following algebraic manipulations:
$$\begin{aligned}&\Pr\!\big[d(X_1^2+\cdots+X_k^2) \le k\beta(X_1^2+\cdots+X_d^2)\big]\\ &= \Pr\!\big[k\beta(X_1^2+\cdots+X_d^2) - d(X_1^2+\cdots+X_k^2) \ge 0\big]\\ &= \Pr\!\big[\exp\{t(k\beta(X_1^2+\cdots+X_d^2) - d(X_1^2+\cdots+X_k^2))\} \ge 1\big] \quad (\text{for } t>0)\\ &\le E\!\big[\exp\{t(k\beta(X_1^2+\cdots+X_d^2) - d(X_1^2+\cdots+X_k^2))\}\big] \quad (\text{by Markov's inequality})\\ &= E[\exp\{tk\beta X^2\}]^{d-k}\,E[\exp\{t(k\beta-d)X^2\}]^{k} \quad (\text{where } X\sim N(0,1))\\ &= (1-2tk\beta)^{-(d-k)/2}(1-2t(k\beta-d))^{-k/2}.\end{aligned}$$
We will refer to this last expression as $g(t)$. The last line of the derivation gives us the additional constraints that $tk\beta<\tfrac12$ and $t(k\beta-d)<\tfrac12$. The latter constraint is subsumed by the former (since $t\ge0$), and so $0<t<1/2k\beta$. Now, to minimize $g(t)$, we maximize
$$f(t)=(1-2tk\beta)^{d-k}(1-2t(k\beta-d))^{k}$$
in the interval $0<t<1/2k\beta$. Differentiating $f$, we get that the maximum is achieved at
$$t_0 = \tfrac{(1-\beta)}{2\beta(d-k\beta)},$$
which lies in the permitted range $(0,\,1/2k\beta)$. Hence we have
$$f(t_0)=\Big(\tfrac{d-k}{d-k\beta}\Big)^{d-k}\Big(\tfrac{1}{\beta}\Big)^{k}$$
and the fact that $g(t_0)=1/\sqrt{f(t_0)}$ proves the inequality (2.2). $\blacksquare$

<a id="pdf-a6706e37c21a-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.93 -->
**Proof of Lemma 2.2(b).** The proof is almost exactly the same as that of Lemma 2.2(a). The same calculations show
$$\Pr\!\big[d(X_1^2+\cdots+X_k^2) \ge k\beta(X_1^2+\cdots+X_d^2)\big] \le (1+2tk\beta)^{-(d-k)/2}(1+2t(k\beta-d))^{-k/2} = g(-t)$$

<a id="pdf-a6706e37c21a-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.66 -->
**(Proof of Lemma 2.2(b), concluded.)** The bound $g(-t)$ holds for $0<t<1/(2(d-k\beta))$, and is minimized at $-t_0$ (with $t_0$ as in part (a)), which lies in $(0, 1/(2(d-k\beta)))$ when $\beta>1$. This yields
$$\Pr\!\big[d(X_1^2+\cdots+X_k^2) \ge \beta k(X_1^2+\cdots+X_d^2)\big] \le \beta^{k/2}\Big(1+\tfrac{k(1-\beta)}{d-k}\Big)^{(d-k)/2}. \quad\square$$

<a id="pdf-a6706e37c21a-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.97 -->
**3. Discussion**

<a id="pdf-a6706e37c21a-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.92 -->
The reader may find it interesting to compare the results of this paper with the alternate proofs given by Indyk and Motwani in [12], and by Achlioptas in [2]. The algorithm in the former paper does not choose a random $k$-dimensional subspace *per se*; it instead picks $k$ independent random vectors $\{U_i\}_{i=1}^{k}$ from the $d$-dimensional normal distribution (with the unit covariance matrix), and sets the $i$-th coordinate of the map $f(x)$ to be $\tfrac{1}{\sqrt d}\langle U_i, x\rangle$. The proof follows by formalizing the intuition that these random vectors are almost orthogonal to each other, and hence this mapping is almost the same as projecting onto a random $k$-dimensional subspace. The statement in [12] analogous to our Lemma 2.2 is somewhat weaker in the sense that the lower bound for $k$ contains some lower order terms, as a result of which one has to assume a lower bound for $k$ larger by an additive factor of roughly $O(\log\log n)$. However, their algorithm is substantially simpler, since it just has to populate all the entries of a $k\times d$ matrix $A$ by independent $N(0,1)$ random variables, whereupon the images of $x \in V$ are given by $f(x)=\tfrac{1}{\sqrt d}(Ax)$. The latter paper [2] takes this idea even further and shows that, instead of using Gaussians, one can pick the entries of $A$ to be uniformly and independently drawn from $\{1, -1\}$. With a tighter analysis than that of [12], this paper gives the same bound for $k$ as Theorem 2.1.

<a id="pdf-a6706e37c21a-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.95 -->
**References.** [1] N. Alon, *Problems and results in extremal combinatorics, Part I*, unpublished. [2] D. Achlioptas, *Database-friendly random projections*, PODS 2001, 274–281. [3] R. I. Arriaga, S. Vempala, *An algorithmic theory of learning: robust concepts and random projection*, FOCS 1999, 616–623. [4] H. Chernoff, *A measure of asymptotic efficiency for tests of a hypothesis based on the sum of observations*, Ann. Math. Stat. 23 (1952), 493–507. [5] S. Dasgupta, *Learning mixtures of Gaussians*, FOCS 1999, 634–644. [6] L. Engebretsen, P. Indyk, R. O'Donnell, *Derandomized dimensionality reduction with applications*, SODA 2002, 705–712.

<a id="pdf-a6706e37c21a-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.95 -->
**References (cont.).** [7] P. Frankl, H. Maehara, *The Johnson–Lindenstrauss lemma and the sphericity of some graphs*, J. Combin. Theory Ser. B 44(3) (1988), 355–362. [8] P. Frankl, H. Maehara, *Some geometric applications of the beta distribution*, Ann. Inst. Stat. Math. 42(3) (1990), 463–474. [9] W. Hoeffding, *Probability inequalities for sums of bounded random variables*, J. Am. Stat. Assoc. 58 (1963), 13–30. [10] P. Indyk, R. Motwani, *Approximate nearest neighbors: towards removing the curse of dimensionality*, STOC 1998, 604–613. [11] W. B. Johnson, J. Lindenstrauss, *Extensions of Lipschitz maps into a Hilbert space*, Contemp. Math. 26 (1984), 189–206. [12] N. Linial, F. London, Y. Rabinovich, *The geometry of graphs and some of its algorithmic applications*, Combinatorica 15(2) (1995), 215–245 (prelim. FOCS 1994, 577–591). [13] D. Sivakumar, *Algorithmic derandomization using complexity theory*, STOC 2002, 619–626.
