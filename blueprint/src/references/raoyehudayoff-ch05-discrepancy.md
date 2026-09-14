<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: 4c44440f2aaa0ac0f6a2e09591838c6865607cd9872cd966896a94edb2dc06bb -->

<a id="pdf-4c44440f2aaa-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.90 -->
# 5. Discrepancy

The discrepancy method proves communication-complexity lower bounds; used here for optimal lower bounds on randomized protocols and tight lower bounds in the number-on-forehead model. Motivation: randomized protocols only yield *nearly* monochromatic rectangles, so a bias-sensitive measure is needed.

<a id="pdf-4c44440f2aaa-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.92 -->
**Definition (Discrepancy).** Let $g$ be a boolean function and let $\chi_S$ be the characteristic function of the set $S$. The discrepancy of $S$ with respect to $g$ is
$$\left| \mathbb{E}\big[\chi_S(x)\cdot(-1)^{g(x)}\big] \right|,$$
where the expectation is taken over a random input $x$.

<a id="pdf-4c44440f2aaa-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.95 -->
**Fact 5.1.** If $R$ is a $(1-e)$-monochromatic rectangle (or cylinder intersection) of density $\delta$, then the discrepancy of $R$ is at least $(1-2e)\delta$.

<a id="pdf-4c44440f2aaa-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.90 -->
**Proof.** Only points inside $R$ contribute to its discrepancy. Since a $(1-e)$ fraction of these points share the same value under $g$, the discrepancy is at least $\delta(1-e)-\delta e = \delta(1-2e)$. $\qquad\square$

<a id="pdf-4c44440f2aaa-p001-b005"></a>
<!-- pdf-source: page=1; block=5; confidence=0.85 -->
Let $\pi(x,y)$ be the output of a protocol $\pi$ with $c$ bits of communication and error $e$, and let $R_1,\dots,R_t$ be the rectangles induced by the protocol. (Calculation continues on next page.)

<a id="pdf-4c44440f2aaa-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.90 -->
Bounding the protocol's advantage:
$$1-2\epsilon = \mathbb{E}_{x,y}\big[(-1)^{\pi(x,y)+g(x,y)}\big] = \mathbb{E}_{x,y}\big[(-1)^{\pi(x,y)}\cdot(-1)^{g(x,y)}\big]$$
$$\le \mathbb{E}_{x,y}\Big[\Big(\sum_{i=1}^{t}\chi_{R_i}(x,y)\cdot o(R_i)\Big)\cdot(-1)^{g(x,y)}\Big],$$
where $o(R_i)$ is $-1$ if the protocol outputs $1$ in $R_i$, and it is $1$ if the protocol outputs $0$. Continuing to bound:
$$1-2\epsilon \le \sum_{i=1}^{t}\Big|\mathbb{E}_{x,y}\big[\chi_{R_i}(x,y)\cdot(-1)^{g(x,y)}\big]\Big| \le 2^c\,\max_R\Big|\mathbb{E}_{x,y}\big[\chi_R(x,y)\cdot(-1)^{g(x,y)}\big]\Big|,$$
where the maximum is over all rectangles. Rearranging:
$$2^c \ge \frac{1-2\epsilon}{\max_R \big|\mathbb{E}_{x,y}[\chi_R(x,y)\cdot(-1)^{g(x,y)}]\big|}.$$
The same calculation also works in the case of cylinder intersections.

<a id="pdf-4c44440f2aaa-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.95 -->
**Theorem 5.2.** If the maximum discrepancy of every rectangle (or cylinder intersection) is at most $\gamma$, then every protocol with error $e$ computing the function must have communication at least $\log\!\left(\dfrac{1-2e}{\gamma}\right)$.

<a id="pdf-4c44440f2aaa-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.85 -->
## Some Examples Using Convexity in Combinatorics

Discrepancy bounds will use Jensen's inequality; first, applications to combinatorics. Dense graphs may avoid 3-cycles (e.g. complete bipartite graph, Figure 5.1), but not 4-cycles.

<a id="pdf-4c44440f2aaa-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.85 -->
**Lemma 5.3.** Every $n$-vertex graph with $e\binom{n}{2}$ edges has at least $(en-1)^4/4$ 4-cycles.

<a id="pdf-4c44440f2aaa-p002-b005"></a>
<!-- pdf-source: page=2; block=5; confidence=0.90 -->
**Proof.** Let $\mathbf{1}_{x,y}=1$ when there is an edge between the vertices $x$ and $y$, and $0$ otherwise. For $x,x',y,y'$ chosen uniformly at random, the number of 4-cycles is counted by
$$\mathbb{E}\big[\mathbf{1}_{x,y}\cdot\mathbf{1}_{x',y}\cdot\mathbf{1}_{x,y'}\cdot\mathbf{1}_{x',y'}\big] = \mathbb{E}_{x,x'}\Big[\mathbb{E}_y[\mathbf{1}_{x,y}\cdot\mathbf{1}_{x',y}]^2\Big]$$
$$\ge \mathbb{E}_{x,x'}\Big[\mathbb{E}_y[\mathbf{1}_{x,y}\cdot\mathbf{1}_{x',y}]\Big]^2 = \mathbb{E}_y\Big[\mathbb{E}_x[\mathbf{1}_{x,y}]^2\Big]^2 \ge \mathbb{E}_{x,y}[\mathbf{1}_{x,y}]^4.$$
This last quantity is at least $(\epsilon-1/n)^4$, since we are picking a random edge as long as $x$ and $y$ are distinct. This gives $(\epsilon n-1)^4/4$ cycles, since each cycle is counted 4 times. $\quad\square$

<a id="pdf-4c44440f2aaa-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.85 -->
Similar convexity ideas show every dense bipartite graph contains a large bipartite clique; a slightly different proof follows.

<a id="pdf-4c44440f2aaa-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.95 -->
**Lemma 5.4.** If $G$ is a bipartite graph of edge density $\epsilon$, and bipartition $A,B$, with $|B|=n$, then there exist subsets $Q\subseteq A$, $R\subseteq B$ with $|Q|\ge \dfrac{\log n}{2\log(e/\epsilon)}$, $|R|\ge \sqrt{n}$, such that every pair of vertices $q\in Q$, $r\in R$ is connected by an edge.

<a id="pdf-4c44440f2aaa-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.55 -->
**Proof.** Pick a random subset $Q\subseteq A$ of size $k=\frac{\log n}{2\log(e/\mathrm{e})}$, and let $R$ be the common neighbors of $Q$. A vertex $b\in B$ of degree $d$ lies in $R$ with probability
$$\frac{\binom{d}{k}}{\binom{n}{k}} \ge \left(\frac{d}{en}\right)^{k},\qquad k=\tfrac{\log n}{2\log(e/\mathrm{e})},$$
using the fact $(n/k)^k \le \binom{n}{k} \le (\mathrm{e}n/k)^k$. If $d_i$ is the degree of the $i$-th vertex, the expected size of $R$ is at least
$$\sum_{i=1}^{n}\left(\frac{d_i}{en}\right)^{k} \ge n\left(\frac{1}{n}\sum_{i=1}^{n}\frac{d_i}{en}\right)^{k} \ge n\left(\frac{e}{\mathrm{e}}\right)^{k} = \sqrt{n}$$
(by convexity). Hence some choice of $Q,R$ proves the lemma. $\quad\square$

<a id="pdf-4c44440f2aaa-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.90 -->
## Lower bounds for Inner-Product

Alice and Bob hold $x,y\in\{0,1\}^n$ and want to compute $\langle x,y\rangle \bmod 2$. Deterministically this needs $n+1$ bits; here it is shown to require $\approx n/2$ bits even with a randomized protocol.

<a id="pdf-4c44440f2aaa-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.50 -->
Running header: *Communication complexity* (p. 66).

<a id="pdf-4c44440f2aaa-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.96 -->
**Lemma 5.5.** For any rectangle $R$, the discrepancy of $R$ with respect to the inner product is at most $2^{-n/2}$.

<a id="pdf-4c44440f2aaa-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.90 -->
**Proof.** Write the rectangle's indicator as a product $\chi_R(x,y)=A(x)\cdot B(y)$. Then
$$\mathbb{E}_{x,y}[\chi_R(x,y)(-1)^{\langle x,y\rangle}]^2 = \mathbb{E}_x\big[A(x)\,\mathbb{E}_y[B(y)(-1)^{\langle x,y\rangle}]\big]^2 \le \mathbb{E}_x\big[A(x)^2\,\mathbb{E}_y[B(y)(-1)^{\langle x,y\rangle}]^2\big],$$
using $\mathbb{E}[Z]^2\le\mathbb{E}[Z^2]$. Dropping $A(x)$ (bounded by 1) eliminates set $A$:
$$\le \mathbb{E}_{x,y,y'}[B(y)B(y')(-1)^{\langle x,y+y'\rangle}].$$
Eliminating $B$ likewise gives
$$\mathbb{E}_{x,y}[\chi_R(x,y)(-1)^{\langle x,y\rangle}]^2 \le \mathbb{E}_x\,\mathbb{E}_{y,y'}\big[\,|(-1)^{\langle x,y+y'\rangle}|\,\big]. \tag{5.1}$$
When $y+y'\ne 0 \bmod 2$ the expectation over $x$ is $0$; the probability that $y+y'\equiv 0\bmod 2$ is exactly $2^{-n}$, so (5.1) is bounded by $2^{-n}$, giving discrepancy $\le 2^{-n/2}$.

<a id="pdf-4c44440f2aaa-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.95 -->
**Theorem 5.6.** (From Lemma 5.5 and Theorem 5.2.) Any 2-party protocol computing the inner product with error at most $e$ over the uniform distribution must have communication at least $n/2 - \log(1/(1-2e))$.

<a id="pdf-4c44440f2aaa-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.92 -->
Similar ideas bound the number-on-forehead communication complexity of the generalized inner product. Each of $k$ players holds a binary string $x_i\in\{0,1\}^n$, and they compute $\mathrm{GIP}(x)=\sum_{j=1}^n \prod_{i=1}^k x_{i,j} \bmod 2$.

<a id="pdf-4c44440f2aaa-p004-b006"></a>
<!-- pdf-source: page=4; block=6; confidence=0.97 -->
**Lemma 5.7.** For any cylinder intersection $S$, the discrepancy of $S$ with respect to the inner product is at most $e^{-n/4^{\,k-1}}$.

<a id="pdf-4c44440f2aaa-p004-b007"></a>
<!-- pdf-source: page=4; block=7; confidence=0.70 -->
Footnote: Babai et al., 1989. Margin note: each vector $x_i$ can be read as a subset of $[n]$, so the set-intersection-size protocol yields an inner-product protocol with communication $O(k4^n/2^k)$.

<a id="pdf-4c44440f2aaa-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.90 -->
**Proof.** Since $S$ is a cylinder intersection, its characteristic function is the product of $k$ boolean functions $\chi_S=\prod_{i=1}^k \chi_i$, where $\chi_i$ does not depend on the $i$-th input. Then
$$\mathbb{E}_x[\chi_S(x)(-1)^{\mathrm{GIP}(x)}]^2 = \mathbb{E}_{x_1,\dots,x_{k-1}}\Big[\chi_k(x)\,\mathbb{E}_{x_k}\big[\textstyle\prod_{i=1}^{k-1}\chi_i(x)(-1)^{\mathrm{GIP}(x)}\big]\Big]^2 \le \mathbb{E}_{x_1,\dots,x_{k-1}}\big[\chi_k(x)^2\,\mathbb{E}_{x_k}[\textstyle\prod_{i=1}^{k-1}\chi_i(x)(-1)^{\mathrm{GIP}(x)}]^2\big]$$
by $\mathbb{E}[Z]^2\le\mathbb{E}[Z^2]$. Dropping $\chi_k$ eliminates it:
$$\le \mathbb{E}_{x_1,\dots,x_k,x_k'}\Big[\textstyle\prod_{i=1}^{k-1}\chi_i(x)\chi_i(x')(-1)^{\sum_{j=1}^n (x_{k}+x_k')\prod_{i=1}^{k-1}x_{i,j}}\Big].$$
Repeating this trick $k-1$ times gives the bound
$$\mathbb{E}_x[\chi_S(x)(-1)^{\mathrm{GIP}(x)}]^{2^{k-1}} \le \mathbb{E}_{x_2,x_2',\dots,x_k,x_k'}\Big[\big|\mathbb{E}_{x_1}[(-1)^{\sum_{j=1}^n x_1\prod_{i=2}^k (x_i+x_i')}]\big|\Big].$$
Whenever $\prod_{i=2}^k (x_{i,j}+x_{i,j}')\ne 0 \bmod 2$ at some coordinate $j$, the expectation is $0$; the probability the expression is $0 \bmod 2$ is exactly $(1-2^{-k+1})^n$. Hence
$$\mathbb{E}_x[\chi_S(x)(-1)^{\mathrm{GIP}(x)}]^{2^{k-1}} \le (1-2^{-k+1})^n < e^{-n/2^{k-1}},$$
using the fact $1-x<e^{-x}$ for $x>0$, which yields $\mathbb{E}_x[\chi_S(x)(-1)^{\mathrm{GIP}(x)}] < e^{-n/4^{k-1}}$.

<a id="pdf-4c44440f2aaa-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.90 -->
**Theorem 5.8.** (From Lemma 5.7 and Theorem 5.2.) Any randomized protocol computing the generalized inner product in the number-on-forehead model with error $e$ requires $n/4^{\,k-1} - \log(1/(1-2e))$ bits of communication.

<a id="pdf-4c44440f2aaa-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.95 -->
## Lower bounds for Disjointness in the Number-on-Forehead model

<a id="pdf-4c44440f2aaa-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.88 -->
Discrepancy seems weak against disjointness, which has large monochromatic rectangles. For Alice and Bob holding $X,Y\subseteq[n]$: if the input distribution makes sets intersect with probability $\le e$ there is a trivial protocol with error $\le e$; if intersection probability is $\ge e$, some fixed coordinate $i$ has an intersection with probability $\ge e/n$, and setting $R=\{(X,Y): i\in X, i\in Y\}$ gives $|\mathbb{E}[\chi_R(X,Y)(-1)^{\mathrm{Disj}(X,Y)}]|\ge e/n$, so this route cannot beat $\Omega(\log n)$. A different expression nonetheless yields a randomized lower bound for disjointness — the only known method in the number-on-forehead model. Footnote: Sherstov 2012; Rao and Yehudayoff 2015.

<a id="pdf-4c44440f2aaa-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.85 -->
**Distribution.** The universe is partitioned into disjoint sets $I_1,\dots,I_m$. Alice draws $m$ independent sets $X_1,\dots,X_m$ with $X_i$ a random subset of $I_i$; Bob draws $m$ random singletons $Y_1,\dots,Y_m$ with $Y_i$ from $I_i$. Set $X=\bigcup_{i=1}^m X_i$, $Y=\bigcup_{i=1}^m Y_i$.

**Lemma 5.9.** For any rectangle $R$,
$$\mathbb{E}\big[\chi_R(X,Y)(-1)^{\sum_{i=1}^m \mathrm{Disj}(X_i,Y_i)}\big] \le \sqrt{\frac{1}{\prod_{i=1}^m |I_i|}}.$$

<a id="pdf-4c44440f2aaa-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.78 -->
**Proof.** Write $\chi_R(X,Y)=A(X)\cdot B(Y)$ and apply a convexity argument:
$$\mathbb{E}[\chi_R(X,Y)(-1)^{\sum_i \mathrm{Disj}(X_i,Y_i)}]^2 = \mathbb{E}\big[A(X)\,B(Y)(-1)^{\sum_i \mathrm{Disj}(X_i,Y_i)}\big]^2$$
$$\le \mathbb{E}\big[A(X)^2\,\mathbb{E}_Y[B(Y)(-1)^{\sum_i \mathrm{Disj}(X_i,Y_i)}]^2\big] \le \mathbb{E}_{X,Y,Y'}\big[B(Y)B(Y')(-1)^{\sum_i \mathrm{Disj}(X_i,Y_i)+\sum_i \mathrm{Disj}(X_i,Y_i')}\big]$$
$$\le \mathbb{E}_X\,\mathbb{E}_{Y,Y'}\big[\,|(-1)^{\sum_i \mathrm{Disj}(X_i,Y_i)+\sum_i \mathrm{Disj}(X_i,Y_i')}|\,\big].$$
(Proof continues beyond the supplied pages.)

<a id="pdf-4c44440f2aaa-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.90 -->
**Proof (concl. of Lemma 5.9).** For any fixing of $Y,Y'$, the inner expectation is $0$ as long as $Y\ne Y'$. The probability that $Y=Y'$ is exactly $1/\prod_{j=1}^m |I_j|$. Thus
$$\mathbb{E}\big[\chi_R(X,Y)\,(-1)^{\sum_{i=1}^m \mathrm{Disj}(X_i,Y_i)}\big]^2 \le \frac{1}{\prod_{j=1}^m |I_j|},$$
proving the bound. $\square$

<a id="pdf-4c44440f2aaa-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.90 -->
Lemma 5.9 gives a linear lower bound for deterministic disjointness protocols: communication $c$ implies at most $2^c$ monochromatic 1-rectangles $R_1,\dots,R_t$ covering all the 1's. When $X,Y$ are disjoint $\sum_{j=1}^m \mathrm{Disj}(X_i,Y_i)=m$, and $\Pr[\text{disjoint}]=2^{-m}$, so
$$2^{-m}\le \mathbb{E}\Big[\sum_{i=1}^t \chi_{R_i}(X,Y)(-1)^{\sum_{j=1}^m \mathrm{Disj}(X_i,Y_i)}\Big] \le \sum_{i=1}^t\big|\mathbb{E}[\cdots]\big| \le 2^c\Big(1/\prod_{j=1}^m \sqrt{|I_j|}\Big).$$
Setting $|I_i|=4$ and rearranging gives $c\ge m$. Unlike the earlier approaches, this method also works in the number-on-forehead model.

<a id="pdf-4c44440f2aaa-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.75 -->
**Setup.** For each $j=1,\dots,m$: $X_{1,j}\subseteq I_j$ is uniform, and $X_{2,j},\dots,X_{k,j}\subseteq I_j$ are uniform subject to their intersection containing exactly one element. Set $X_i=\bigcup_{j=1}^m X_{i,j}$; player $i$ holds $X_i$ on his forehead.

<a id="pdf-4c44440f2aaa-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.80 -->
**Lemma 5.10.** For any cylinder intersection $S$, $$\mathbb{E}\big[\chi_S(X)\,(-1)^{\sum_{j=1}^m \mathrm{Disj}(X_{1,j},\dots,X_{k,j})}\big] \le \prod_{j=1}^m \frac{1}{\sqrt{(2^k-1)\,|I_j|}}.$$

<a id="pdf-4c44440f2aaa-p007-b005"></a>
<!-- pdf-source: page=7; block=5; confidence=0.70 -->
**Proof.** By induction on $k$; the base case $k=2$ is Lemma 5.9. Write $T_j=(X_{1,j},\dots,X_{k,j})$ and $\chi_S(X)=\prod_{i=1}^k \chi_i(X)$, with $\chi_i$ the indicator of the $i$-th cylinder. A convexity (Cauchy–Schwarz) argument bounds the squared expectation (continued next page).

<a id="pdf-4c44440f2aaa-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.60 -->
**Proof (cont.).** Squaring and applying Cauchy–Schwarz over $X_k$ yields $$\mathbb{E}\big[\chi_S(X)(-1)^{\sum_j \mathrm{Disj}(T_j)}\big]^2 \le \mathbb{E}_{X_1,\dots,X_{k-1},X_k,X_k'}\Big[\prod_{i=1}^{k-1}\chi_i(X)\chi_i(X')\,(-1)^{\sum_j \mathrm{Disj}(T_j)+\mathrm{Disj}(T_j')}\Big]\quad(5.2),$$ where $X'=(X_1,\dots,X_{k-1},X_k')$, $T_j'=(X_{1,j},\dots,X_{k-1,j},X_{k,j}')$, and $v,v'$ are the two common intersection points. If $v=v'$ then $\mathrm{Disj}(T_j)=\mathrm{Disj}(T_j')$, so the $j$-term is $0\bmod 2$; if $v\ne v'$, intersections in $T_j$ lie in $X_{k,j}\setminus X_{k,j}'$ and in $T_j'$ in $X_{k,j}'\setminus X_{k,j}$, and induction bounds the discrepancy.

<a id="pdf-4c44440f2aaa-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.95 -->
Let $Z_j$ be the random variable defined as
$$Z_j = \begin{cases} 1 & \text{if } v=v', \\[4pt] \dfrac{(2^{k-2}-1)^2}{\sqrt{|X_{k,j}\setminus X_{k,j}'|\,|X_{k,j}'\setminus X_{k,j}|}} & \text{otherwise.}\end{cases}$$
Then, since the $Z_j$ are independent of each other,
$$(5.2)\le \mathbb{E}\Big[\prod_{j=1}^m Z_j\Big]\le \prod_{j=1}^m \mathbb{E}[Z_j].$$

<a id="pdf-4c44440f2aaa-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.80 -->
**Claim 5.11.** If $Q\subseteq I_j$ is sampled by including a uniformly random element $v\in I_j$ and adding every other element to $Q$ independently with probability $\gamma$ (so $Q\ne\emptyset$), then $\mathbb{E}[1/|Q|]\le 1/(\gamma|I_j|)$.

<a id="pdf-4c44440f2aaa-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.70 -->
**Proof.** $\mathbb{E}[1/|Q|]=\sum_{Q\ne\emptyset,v}\frac{1}{|Q|}\cdot\frac{1}{|I_j|}\,\gamma^{|Q|-1}(1-\gamma)^{|I_j|-|Q|}$; summing over the $|Q|$ choices of $v$ gives $\frac{1}{\gamma|I_j|}\sum_{Q\ne\emptyset}\gamma^{|Q|}(1-\gamma)^{|I_j|-|Q|}\le \frac{1}{\gamma|I_j|}(1-\gamma+\gamma)^{|I_j|}=\frac{1}{\gamma|I_j|}$. $\square$

<a id="pdf-4c44440f2aaa-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.90 -->
**Proof (concl. of Lemma 5.10).** If $X_{2,j}\cap\dots\cap X_{k-1,j}$ is of size $t$, then $\Pr[v=v']=1/t$; this probability is exactly the expected size of $1/|Q|$, where $Q$ is the intersection of the first $k-1$ sets. After picking the common intersection point, every other element of $I_j$ is included in $Q$ independently with probability $\tfrac{1}{2^{k-1}-1}$, so by Claim 5.11, $\Pr[v=v']=\tfrac{2^{k-1}-1}{|I_j|}$. When $v\ne v'$, by the AM–GM inequality ($\sqrt{ab}\le(a+b)/2$),
$$Z_j = \frac{(2^{k-2}-1)^2}{\sqrt{|X_{k,j}\setminus X_{k,j}'|\cdot|X_{k,j}'\setminus X_{k,j}|}} \le \frac{(2^{k-2}-1)^2}{2}\left(\frac{1}{|X_{k,j}\setminus X_{k,j}'|}+\frac{1}{|X_{k,j}'\setminus X_{k,j}|}\right).$$
With $Q=X_k\setminus X_k'$ sampled by picking $V$ uniformly and then including every other element independently with probability $\tfrac{2^{k-2}-1}{2(2^{k-1}-1)}$, Claim 5.11 gives $\mathbb{E}[1/|X_{k,j}\setminus X_{k,j}'|]=\tfrac{2(2^{k-1}-1)}{(2^{k-2}-1)|I_j|}$. Combining these bounds,
$$\mathbb{E}[Z_j]\le \Pr[v=v']+\mathbb{E}\left[\frac{(2^{k-2}-1)^2}{|X_{k,j}\setminus X_{k,j}'|}\right] \le \frac{2^{k-1}-1}{|I_j|}+\frac{2(2^{k-1}-1)(2^{k-2}-1)^2}{(2^{k-2}-1)|I_j|} = \frac{(2^{k-1}-1)^2}{|I_j|},$$
as required. $\square$

<a id="pdf-4c44440f2aaa-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.65 -->
Lemma 5.10 yields a linear number-on-forehead lower bound for deterministic disjointness: communication $c$ implies $\le 2^c$ monochromatic 1-cylinder intersections $S_1,\dots,S_t$ covering all 1's; when $X_1,\dots,X_k$ are disjoint $\sum_{j=1}^m \mathrm{Disj}=m$ and $\Pr[\text{disjoint}]=2^{-m}$, so $$2^{-m}\le \sum_i\big|\mathbb{E}[\chi_{S_i}(-1)^{\sum_j \mathrm{Disj}}]\big|\le 2^c\prod_{j=1}^m \frac{1}{\sqrt{(2^k-1)|I_j|}}.$$ Setting $|I_j|=16(2^k-1)^2$ gives $c\ge m=\frac{n}{16(2^k-1)^2}$. Optimizing $|I_i|=\ell$ (with $a=(2(2^k-1))^2$; the derivative of $(\ell/a)^{1/\ell}$ vanishes at $\ell=e\,a$) improves this to $c\ge \frac{n\log e}{8e\,(2^k-1)^2}$.

<a id="pdf-4c44440f2aaa-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.60 -->
Chapter/section running header: "communication complexity" (page 72).

<a id="pdf-4c44440f2aaa-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.97 -->
**Theorem 5.12.** Any deterministic protocol for computing disjointness in the number-on-forehead model requires $\dfrac{n}{16(2^{k-1}-1)^2}$ bits of communication.
