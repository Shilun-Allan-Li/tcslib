<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: 6d75772463348271496e345864f541b18ebe1d130191f210a3310d21cd274be7 -->

<a id="pdf-6d7577246334-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.90 -->
# 6 Information

Introduces Shannon's information theory (Shannon, 1948) and its impact on communication complexity. Motivation: the information/entropy of a message is not the same as its length. Setting is distributional, with inputs sampled from a distribution $\mu$.

<a id="pdf-6d7577246334-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.90 -->
Three examples in the distributional setting illustrate that a message's information content differs from its length:

1. Alice's first message is always the fixed string $0^c$ regardless of input. It conveys no information; entropy $= 0$; communication of this step reduces to $0$.
2. Alice's first message is a uniformly random string from a set $S \subseteq \{0,1\}^c$ with $|S| \ll 2^c$. Entropy $= \log|S|$; parties should use $\log|S|$ bits to index elements, reducing communication from $c$ to $\log|S|$.
3. Alice's first message is $0^n$ with probability $1-\varepsilon$ and a uniformly random $n$-bit string otherwise. No fixed-length encoding beats $n$ bits, but Alice can send bit $0$ for $0^n$ and $1x$ for other strings $x$; expected length $= 1 - \varepsilon + \varepsilon(n+1) = 1 + \varepsilon n$. Entropy $\approx \varepsilon n$.

<a id="pdf-6d7577246334-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.95 -->
**Definition (Entropy).** For a random variable $X$ with distribution $p(x)$,
$$H(X) = \sum_x p(x)\log(1/p(x)) = \mathbb{E}_{p(x)}\!\left[\log \tfrac{1}{p(x)}\right].$$
The definition ensures $H(X)$ is always non-negative.

<a id="pdf-6d7577246334-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.75 -->
$H(X)$ characterizes the expected number of bits needed to encode $X$. Intuition: an expected-length-$k$ encoding means $X$ takes one of $2^{O(k)}$ values most of the time, so $\mathbb{E}[\log(1/p(x))]$ is $O(k)$; conversely, encoding by positive integers with the $i$-th most likely value having $p(i) \le 1/i$ bounds expected length by $\sum_i p(i)\log i \le H(X)$.

<a id="pdf-6d7577246334-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.97 -->
**Theorem 6.1.** $X$ can be encoded using a message whose expected length is at most $H(X)+1$. Conversely, every encoding of $X$ has expected length at least $H(X)$.

<a id="pdf-6d7577246334-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.85 -->
**Proof.** WLOG $X$ is an integer in $[n]$ with $p(i) \ge p(i+1)$. Set $\ell_i = \lceil \log(1/p(i)) \rceil$ and encode $i$ by a leaf at depth $\ell_i$ in a complete binary tree, so expected length $\sum_i p(i)\ell_i \le \sum_i p(i)(\log(1/p(i))+1) = H(X)+1$. Encoding is greedy: pick the first depth-$\ell_1$ vertex for $1$ and delete its descendants (making it a leaf); then the first non-deleted depth-$\ell_2$ vertex for $2$; continue for all of $[n]$. For $i<j$, the $i$-th step deletes exactly $2^{\ell_j-\ell_i}$ vertices at depth $\ell_j$.

<a id="pdf-6d7577246334-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.85 -->
**Proof (continued).** Vertices at depth $\ell_j$ deleted before step $j$: $\sum_{i=1}^{j-1} 2^{\ell_j-\ell_i} = 2^{\ell_j}\sum_{i=1}^{j-1} 2^{-\ell_i} \le 2^{\ell_j}\sum_{i=1}^{j-1} p(i) < 2^{\ell_j}$, so a vertex is available at step $j$ and every step succeeds.

Converse: if $i$ is encoded with $\ell_i$ bits, then
$$\mathbb{E}_{p(i)}[\ell_i] = \mathbb{E}_{p(i)}[\log(1/p(i))] - \mathbb{E}_{p(i)}[\log(2^{-\ell_i}/p(i))] \ge H(X) - \log \mathbb{E}_{p(i)}[2^{-\ell_i}/p(i)] = H(X) - \log\!\big(\sum_i 2^{-\ell_i}\big),$$
using convexity of $\log$ (Jensen: $\mathbb{E}[\log Y] \le \log \mathbb{E}[Y]$). A random root-to-leaf path hits leaf $i$ with probability $2^{-\ell_i}$, so $\sum_i 2^{-\ell_i} \le 1$, giving $\log(\sum_i 2^{-\ell_i}) \le 0$ and expected length $\ge H(X)$. $\square$

<a id="pdf-6d7577246334-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.90 -->
## Entropy, Divergence and Mutual Information

Divergence and mutual information are closely related to entropy and help analyze information flow.

<a id="pdf-6d7577246334-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.90 -->
**Definition (Divergence).** For distributions $p(x)$ and $q(x)$,
$$D(p\,\|\,q) = \sum_x p(x)\log\frac{p(x)}{q(x)} = \mathbb{E}_{p(x)}\!\left[\log\frac{p(x)}{q(x)}\right].$$
It is a measure of distance between the two distributions.

<a id="pdf-6d7577246334-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.88 -->
**Fact 6.2.** $D(p\,\|\,q) \ge 0$, and $D(p\,\|\,p) = 0$.

<a id="pdf-6d7577246334-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.88 -->
**Proof.** $-D(p\,\|\,q) = \mathbb{E}_{p(x)}\!\left[\log\frac{q(x)}{p(x)}\right] = \sum_x p(x)\log\frac{q(x)}{p(x)} \ge -\log\sum_x p(x)\frac{q(x)}{p(x)} = -\log\sum_x q(x) = -\log 1 = 0,$ so $D(p\,\|\,q) \ge 0$. The inequality follows from convexity of $\log$ (Jensen). $\square$

<a id="pdf-6d7577246334-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.85 -->
**Figure 6.2.** Plot of the divergence between two bits as a function of the parameters $\varepsilon$ and $\gamma$, showing the surface $\varepsilon\log\tfrac{\varepsilon}{\gamma} + (1-\varepsilon)\log\tfrac{1-\varepsilon}{1-\gamma}$.

<a id="pdf-6d7577246334-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.85 -->
Divergence is not symmetric: D(p‖q) ≠ D(q‖p) in general, and can be infinite (e.g. when p is supported on a point of zero q-probability). For X an ℓ-bit string, H(X) = E_{p(x)}[log(1/p(x))] = ℓ − E_{p(x)}[log(p(x)/2^{−ℓ})] = ℓ − D(p‖q), where q is the uniform distribution on ℓ-bit strings. Hence entropy measures divergence from uniform, and since divergence is non-negative (Fact 6.2), the uniform distribution has maximum entropy among all distributions on a set.

<a id="pdf-6d7577246334-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.85 -->
**Fact 6.3.** If E is an event in a probability space containing x, then D(p(x|E)‖p(x)) ≤ log(1/p(E)).

<a id="pdf-6d7577246334-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.80 -->
**Proof.** D(p(x|E)‖p(x)) = E_{p(x|E)}[log(p(x|E)/p(x))] = E_{p(x|E)}[log(p(E|x)/p(E))] ≤ log(1/p(E)), using p(E|x) ≤ 1.

<a id="pdf-6d7577246334-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.78 -->
**Definition (mutual information).** For a joint distribution p(a,b), I(A:B) = E_{p(a,b)}[log(p(a,b)/(p(a)p(b)))] = E_{p(a,b)}[log(p(b|a)/p(b))]. Properties: I(A:B) = H(A) + H(B) − H(AB); I(A:A) = H(A); I(A:B) = 0 when A,B are independent; and 0 ≤ I(A:B) ≤ H(A). The lower bound follows from Fact 6.2; the upper bound follows since H(A) − I(A:B) = E_{p(a,b)}[log(1/p(a)) − log(p(a,b)/(p(a)p(b)))] = E_{p(a,b)}[log(p(b)/p(a,b))] ≥ 0. (Marginal remark: entropy, mutual information, and divergence are all expectations of log-ratios.)

<a id="pdf-6d7577246334-p005-b005"></a>
<!-- pdf-source: page=5; block=5; confidence=0.90 -->
**Chain Rules.** Section heading. Chain rules relate bounds on the information of a collection of random variables to the information of each individual variable.

<a id="pdf-6d7577246334-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.82 -->
For distributions p(a,b), q(a,b): D(p(a,b)‖q(a,b)) = E_{p(a,b)}[log((p(a)/q(a))·(p(b|a)/q(b|a)))] = E_{p(a,b)}[log(p(a)/q(a))] + E_{p(a,b)}[log(p(b|a)/q(b|a))] = D(p(a)‖q(a)) + E_{p(a)}[D(p(b|a)‖q(b|a))]. In words: total divergence = divergence of the first variable + expected divergence of the second.

<a id="pdf-6d7577246334-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.82 -->
**Chain rule (entropy).** Entropy does not add in general: if A,B are two always-equal random bits, H(AB) = 1 ≠ 2 = H(A) + H(B). Defining conditional entropy H(B|A) = E_{p(a,b)}[log(1/p(b|a))], the chain rule holds: H(AB) = H(A) + H(B|A). (Derivation: H(AB) = E_{p(a,b)}[log(1/(p(a)p(b|a)))] = E_{p(a,b)}[log(1/p(a)) + log(1/p(b|a))] = H(A) + H(B|A).)

<a id="pdf-6d7577246334-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.78 -->
**Chain rule (mutual information).** Mutual information does not add: for three always-equal bits A,B,C, I(AB:C) = 1 < 2 = I(A:C) + I(B:C); for bits satisfying A + B + C = 0 mod 2, I(AB:C) = 1 > 0 = I(A:C) + I(B:C). Defining conditional mutual information I(B:C|A) = E_{p(a,b,c)}[log(p(b,c|a)/(p(b|a)p(c|a)))], the chain rule holds: I(AB:C) = I(A:C) + I(B:C|A). (This follows from expanding I(AB:C) = E_{p(a,b,c)}[log(p(a,c)/(p(a)p(b|a)) · p(b|a,c)/p(c))] = I(A:C) + E_{p(a,b,c)}[log(p(b|a,c)/p(b|a))] = I(A:C) + I(B:C|A).)

<a id="pdf-6d7577246334-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.78 -->
**Subadditivity.** Section heading. Each quantity satisfies that conditioning on variables can only increase or only decrease it (loosely, subadditivity). For divergence, with p(a,b), q(a,b): E_{p(b)}[D(p(a|b)‖q(a))] = E_{p(a,b)}[log((p(a)/q(a))·(p(a|b)/p(a)))] = D(p(a)‖q(a)) + I(A:B) ≥ D(p(a)‖q(a)). A consequence of this inequality continues on the next page.

<a id="pdf-6d7577246334-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.85 -->
**Fact 6.4.** If $q(x_1,\dots,x_n)$ is a product distribution, then for any $p$,
$$D(p\|q) \ge \sum_{i=1}^n D\big(p(x_i)\,\|\,q(x_i)\big).$$

<a id="pdf-6d7577246334-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.85 -->
**Entropy facts.** $H(AB)=H(A)+H(B)-I(A:B)\le H(A)+H(B)$; hence $H(A)\ge H(AB)-H(B)=H(A\mid B)$. Conditioning may raise or lower mutual information, but for independent $A,B$: $I(AB:C)\ge I(A:C)+I(B:C)$.

<a id="pdf-6d7577246334-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.80 -->
**Shearer's Inequality.** Section heading; introduced as a consequence of subadditivity. The actual statement is not present on this page.

<a id="pdf-6d7577246334-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.80 -->
**Proof of Fact 6.4.** By the chain rule for divergence,
$$D(p\|q)=\sum_{i=1}^n \mathbb{E}_{p(x_{<i})}\big[D\big(p(x_i\mid x_{<i})\,\|\,q(x_i\mid x_{<i})\big)\big] = \sum_{i=1}^n \mathbb{E}_{p(x_{<i})}\big[D\big(p(x_i\mid x_{<i})\,\|\,q(x_i)\big)\big],$$
since $q$ is a product ($q(x_i\mid x_{<i})=q(x_i)$); applying convexity then gives $\ge \sum_{i=1}^n D\big(p(x_i)\|q(x_i)\big)$.

<a id="pdf-6d7577246334-p007-b005"></a>
<!-- pdf-source: page=7; block=5; confidence=0.60 -->
**Footnote (independence bound).** For $I(AB:C)\ge I(A:C)+I(B:C)$: write $I(AB:C)-I(B:C)=I(A:C)+I(B:C\mid A)-I(B:C)$, with $I(B:C\mid A)=H(B\mid A)-H(B\mid AC)$. Since $A,B$ independent, $H(B\mid A)=H(B)$, and $H(B\mid AC)\le H(B\mid C)$, so $I(B:C\mid A)\ge I(B:C)\ge 0$, giving the claim.

<a id="pdf-6d7577246334-p007-b006"></a>
<!-- pdf-source: page=7; block=6; confidence=0.90 -->
**Lemma 6.5.** Let $X=X_1,\dots,X_n$ and let $S\subseteq[n]$ be sampled independently of $X$. If $\Pr[i\in S]\ge \varepsilon$ for every $i\in[n]$, then $H(X_S\mid S)\ge \varepsilon\cdot H(X)$.

<a id="pdf-6d7577246334-p007-b007"></a>
<!-- pdf-source: page=7; block=7; confidence=0.85 -->
**Proof.** For $S=\{a,b,c\}$ with $a<b<c$, $H(X_S)=H(X_a)+H(X_b\mid X_a)+H(X_c\mid X_a,X_b)\ge H(X_a\mid X_{<a})+H(X_b\mid X_{<b})+H(X_c\mid X_{<c})$ by subadditivity; in general $H(X_S)\ge\sum_{i\in S}H(X_i\mid X_{<i})$. Hence $H(X_S\mid S)\ge \mathbb{E}_S\big[\sum_{i\in S}H(X_i\mid X_{<i})\big]=\sum_{i=1}^n \Pr[i\in S]\,H(X_i\mid X_{<i})\ge \varepsilon\,H(X)$.

<a id="pdf-6d7577246334-p007-b008"></a>
<!-- pdf-source: page=7; block=8; confidence=0.85 -->
**Pinsker's Inequality.** Section heading; Pinsker's inequality bounds statistical distance between two distributions by their divergence.

<a id="pdf-6d7577246334-p007-b009"></a>
<!-- pdf-source: page=7; block=9; confidence=0.70 -->
**Lemma 6.6.** $D(p\|q)\ge \dfrac{2}{\ln 2}\,|p-q|^2$, where $|p-q|$ is the statistical distance.

<a id="pdf-6d7577246334-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.60 -->
**Figure 6.3.** Plot over $\varepsilon\in[0,1]$ (curves for $\gamma\approx0.1,0.2,0.5,0.8$) of $\varepsilon\log\tfrac{\varepsilon}{\gamma}+(1-\varepsilon)\log\tfrac{1-\varepsilon}{1-\gamma}-\tfrac{2}{\ln2}(\varepsilon-\gamma)^2$, illustrating that this quantity is nonnegative.

<a id="pdf-6d7577246334-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.70 -->
**Proof (Lemma 6.6).** Let $T$ maximize $p(T)-q(T)$ and set $x_T=\mathbf{1}[x\in T]$. Then $|p-q|=p(T)-q(T)=p(x_T{=}1)-q(x_T{=}1)$, and $D(p\|q)\ge D\big(p(x_T)\|q(x_T)\big)\ge \tfrac{2}{\ln2}\big(p(x_T{=}1)-q(x_T{=}1)\big)^2=\tfrac{2}{\ln2}|p-q|^2$. The first inequality is the chain rule for divergence; the second is the scalar case proved via (6.1).

<a id="pdf-6d7577246334-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.80 -->
**Proof step (eq. 6.1).** Set $p(x_T{=}1)=\varepsilon \ge q(x_T{=}1)=\gamma$. Show $\;\varepsilon\log\tfrac{\varepsilon}{\gamma}+(1-\varepsilon)\log\tfrac{1-\varepsilon}{1-\gamma}-\tfrac{2}{\ln2}(\varepsilon-\gamma)^2\ge0$ (6.1). It is $0$ when $\varepsilon=\gamma$, and its derivative with respect to $\gamma$ is $\tfrac{\gamma-\varepsilon}{\ln2}\big(\tfrac{1}{\gamma(1-\gamma)}-4\big)$. Since $\tfrac{1}{\gamma(1-\gamma)}$ is always at most $4$, the derivative is non-positive when $\gamma<\varepsilon$ and non-negative when $\gamma>\varepsilon$. This proves that (6.1) is always non-negative, as required.

<a id="pdf-6d7577246334-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.90 -->
**Figure 6.4.** Plots $f=\varepsilon\log\tfrac{\varepsilon}{2/3}+(1-\varepsilon)\log\tfrac{1-\varepsilon}{1/3}$ and $g=\tfrac{2}{\ln2}(\varepsilon-2/3)^2$ (i.e. $\gamma=2/3$).

<a id="pdf-6d7577246334-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.70 -->
**Corollary 6.7.** For random variables $A,B$, on average over $b$, $p(a\mid b)\approx_\varepsilon p(a)$ with $\varepsilon=\sqrt{\tfrac{\ln2}{2}\,I(A:B)}$.

<a id="pdf-6d7577246334-p009-b005"></a>
<!-- pdf-source: page=9; block=5; confidence=0.70 -->
**Corollary 6.8.** Let $A_1,\dots,A_n$ be independent random variables, jointly distributed with $B$; let $i\in[n]$ be uniformly random and independent of all other variables. Then on average over $b,i$, $p(a_i\mid b)\approx_\varepsilon p(a_i)$ with $\varepsilon\le\sqrt{\tfrac{H(B)\ln2}{2n}}$.

<a id="pdf-6d7577246334-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.95 -->
**Proof.** By subadditivity, $H(B)/n \ge I(A_1,\dots,A_n : B)/n \ge (1/n)\sum_{j=1}^n I(A_j : B)$. Hence for a uniformly random coordinate $i$, $\mathbb{E}[I(A_i : B)] \le H(B)/n$. The bound follows from Corollary 6.7.

<a id="pdf-6d7577246334-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.95 -->
**Some Examples from Combinatorics.** Entropy has combinatorial applications that yield simple proofs; several illustrative examples follow.

<a id="pdf-6d7577246334-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.95 -->
**On the Size of Projections.** Let $S$ be a set of $n^3$ points in $\mathbb{R}^3$, and let $S_{xy}, S_{yz}, S_{xz}$ denote the projections of $S$ onto the $xy$, $yz$, $xz$ planes.

<a id="pdf-6d7577246334-p010-b004"></a>
<!-- pdf-source: page=10; block=4; confidence=0.95 -->
**Claim 6.9.** At least one of the three projections has size at least $n^2$.

<a id="pdf-6d7577246334-p010-b005"></a>
<!-- pdf-source: page=10; block=5; confidence=0.93 -->
**Proof.** Let $X,Y,Z$ be the coordinates of a uniformly random point of $S$. By Shearer's inequality, $\dfrac{H(XY)+H(YZ)+H(XZ)}{3} \ge \dfrac{2}{3}\,H(XYZ) = 2\log n$, so some one of the three terms is $\ge 2\log n$, proving that projection has size at least $n^2$.

<a id="pdf-6d7577246334-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.92 -->
**On the Size of Triangle Intersecting Graphs.** Let $\mathcal{F}$ be a family of subsets of $[n]$ such that any two sets from $\mathcal{F}$ intersect.

<a id="pdf-6d7577246334-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.95 -->
**Claim 6.10.** $|\mathcal{F}| \le 2^{\,n-1}$.

<a id="pdf-6d7577246334-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.95 -->
**Proof.** For any $T \in \mathcal{F}$, its complement cannot be in $\mathcal{F}$, so at most half of all subsets can belong to $\mathcal{F}$.

<a id="pdf-6d7577246334-p011-b004"></a>
<!-- pdf-source: page=11; block=4; confidence=0.90 -->
Let $\mathcal{G}$ be a family of graphs on $n$ vertices such that every two graphs intersect in a triangle (a 3-cycle). Fixing one triangle yields $2^{\binom{n}{2}-3} = 2^{\binom{n}{2}}/8$ graphs; this bound is tight (Ellis et al., 2010). The following theorem gives a simple partial converse (Chung et al., 1986).

<a id="pdf-6d7577246334-p011-b005"></a>
<!-- pdf-source: page=11; block=5; confidence=0.93 -->
**Theorem 6.11.** $|\mathcal{G}| \le 2^{\binom{n}{2}}/4$.

<a id="pdf-6d7577246334-p011-b006"></a>
<!-- pdf-source: page=11; block=6; confidence=0.85 -->
**Proof.** Let $G$ be a uniformly random graph from $\mathcal{G}$, encoded as a binary vector of length $\binom{n}{2}$ (one bit per possible edge). Choose a random subset $S$ of $n/2$ vertices and let $G_S$ be $G$ with every edge crossing between $S$ and its complement deleted. Each edge is retained with probability exactly $1/2$, so Shearer's inequality gives $\mathbb{E}_S[H(G_S \mid S)] \ge H(G)/2$. Since any two family graphs intersect in a triangle, at least one triangle edge survives, so $G_S$ and $G'_S$ always share an edge for every $S$; by Claim 6.10 the number of such projections is at most half of all possible projections. Writing $e(S) = \binom{|S|}{2} + \binom{n-|S|}{2}$ for the total number of possible edges in $G_S$, this yields $H(G_S) + 1 \le e(S)$. In expectation exactly half the edges contribute, so $\tfrac12\binom{n}{2} = \mathbb{E}_S[e(S)] \ge \mathbb{E}_S[H(G_S \mid S)] + 1 \ge \tfrac12 H(G) + 1$, hence $H(G) \le \binom{n}{2} - 2$ and $|\mathcal{G}| \le 2^{\binom{n}{2}-2} = 2^{\binom{n}{2}}/4$. (A similar argument bounds any family intersecting in an $r$-clique by $2^{\binom{n}{2}}/2^{\,r-1}$; see Exercise 6.4.)

<a id="pdf-6d7577246334-p011-b007"></a>
<!-- pdf-source: page=11; block=7; confidence=0.90 -->
**An Isoperimetric Inequality in the Hypercube.** The hypercube is the graph with vertex set $\{0,1\}^n$ whose edges connect vertices that disagree in exactly one coordinate; it has $2^n$ vertices and $2^n n/2$ edges. A tight bound on the number of edges in any vertex subset follows (Samorodnitsky).

<a id="pdf-6d7577246334-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.92 -->
**Theorem 6.12.** If $S \subseteq \{0,1\}^n$, the number of edges contained in $S$ is at most $\dfrac{|S|}{2}\log|S|$.

<a id="pdf-6d7577246334-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.88 -->
**Proof.** Let $e(S)$ be the number of edges within $S$ and $X$ a uniformly random element of $S$. For $x \in S$, if $(x,y)$ is a hypercube edge flipping coordinate $i$, then $H(X_i \mid X_{-i} = x_{-i}) = 1$ if that edge is contained in $S$ and $0$ otherwise, where $X_{-i} = X_1,\dots,X_{i-1},X_{i+1},\dots,X_n$. Summing over $x\in S$ and $i$ counts each edge twice, so $\sum_{i=1}^n H(X_i \mid X_{-i}) = 2e(S)/|S|$. By subadditivity, $\log|S| = H(X) = \sum_{i=1}^n H(X_i \mid X_{<i}) \ge \sum_{i=1}^n H(X_i \mid X_{-i}) = 2e(S)/|S|$, proving $e(S) \le \dfrac{|S|}{2}\log|S|$.

<a id="pdf-6d7577246334-p012-b003"></a>
<!-- pdf-source: page=12; block=3; confidence=0.90 -->
**Lower bound for Indexing.** Alice holds a random $n$-bit string $x$ and Bob a random index $i \in [n]$; the protocol begins with one message from Alice, after which Bob must output $x_i$. The goal is to show $\Omega(n)$ bits are necessary even for average-case protocols. (A deterministic lower bound is immediate: Bob must learn the whole $n$-bit string, so Alice sends $n$ bits.)

<a id="pdf-6d7577246334-p012-b004"></a>
<!-- pdf-source: page=12; block=4; confidence=0.90 -->
**Proof.** Suppose Alice's message $M$ is $\ell$ bits long. By Corollary 6.8, averaged over $m$ and a random coordinate $i$, $p(x_i \mid m) \approx_\epsilon p(x_i)$ with $\epsilon = \sqrt{\dfrac{\ell \ln 2}{2n}}$. Since each $p(x_i)$ is uniform, Bob's error probability on coordinate $i$ is at least $1/2 - |p(x_i \mid m) - p(x_i)|$, so his overall error probability is at least $1/2 - \sqrt{\dfrac{\ell \ln 2}{2n}}$. Small error therefore forces $\ell = \Omega(n)$. (The square-root dependence is tight; see Exercise 6.2.)

<a id="pdf-6d7577246334-p012-b005"></a>
<!-- pdf-source: page=12; block=5; confidence=0.90 -->
**Randomized Communication of Disjointness.** Information theory yields optimal lower bounds on the randomized communication complexity of functions such as disjointness (Kalyanasundaram and Schnitger, 1992; Razborov, 1992; Bar-Yossef et al., 2004; Braverman and Moitra, 2013) — bounds not known by any other method. Many lower bounds in other models follow from Theorem 6.13.

<a id="pdf-6d7577246334-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.95 -->
**Theorem 6.13.** Any randomized protocol computing the set-disjointness function with error $1/2 - e$ must have communication $\Omega(e^2 n)$.

<a id="pdf-6d7577246334-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.85 -->
Standard randomized lower bounds use a hard input distribution (as for inner product, Thm 5.6, and pointer-chasing, Thm 6.16), where the uniform distribution is hard. For disjointness the uniform distribution fails: two uniform sets $A,B$ intersect with high probability, so outputting $0$ without communication has tiny error; in fact no distribution with $A,B$ independent gives a strong bound. Hence a hard distribution must have $A,B$ correlated — e.g. a convex combination of uniform disjoint pairs and pairs intersecting in exactly one element. This creates the difficulty that the events $i\in A\cap B$ and $j\in A\cap B$ are not independent, complicating subadditivity arguments.

<a id="pdf-6d7577246334-p013-b003"></a>
<!-- pdf-source: page=13; block=3; confidence=0.90 -->
**Proof (reduction).** Given a protocol with error $1/2 - e$, repeating it $O(1/e^2)$ times and taking the majority output reduces the error to an arbitrarily small constant. Thus it suffices to show that any protocol with error $< \tfrac{1}{32}$ requires communication $\Omega(n)$.

<a id="pdf-6d7577246334-p013-b004"></a>
<!-- pdf-source: page=13; block=4; confidence=0.90 -->
**Hard distribution.** View $A,B$ as $n$-bit strings with $A_i=1 \iff i\in A$. Pick an index $T\in[n]$ uniformly at random; let $A_T,B_T$ be random independent bits. For $i\neq T$, sample $(A_i,B_i)$ uniformly from $\{(0,0),(0,1),(1,0)\}$, independently of all other pairs. Then $A$ and $B$ intersect in at most one element, and they intersect with probability $\tfrac14$.

<a id="pdf-6d7577246334-p013-b005"></a>
<!-- pdf-source: page=13; block=5; confidence=0.82 -->
Let $S$ denote the messages (transcript) of a deterministic protocol with communication $\ell$. Let $Q$ be the random variable $(T,\,A_{<T},\,B_{>T})$. Conditioned on any fixing of $S,Q$, the variables $A,B$ become independent. (By Thm 3.3, Thm 6.13 is equivalent to the existence of such a hard distribution; note the coordinates $(A_1,B_1),\dots,(A_n,B_n)$ are not independent, which makes the proof subtle.)

<a id="pdf-6d7577246334-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.85 -->
**Claim 6.14.** For every $q,s$: $p(ab\mid qs) = p(a\mid qs)\cdot p(b\mid qs)$. **Proof.** After fixing $Q$, $A,B$ are independent ($p(ab\mid q)=p(a\mid q)p(b\mid q)$); fixing $S$ restricts the inputs to a rectangle, so independence is preserved: $p(ab\mid qs)=p(a\mid qs)p(b\mid qs)$. Moreover $p(a_t\mid q)$ and $p(b_t\mid q)$ are both uniform for every $q$.

<a id="pdf-6d7577246334-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.72 -->
Assume the protocol error on $A,B$ is at most $\tfrac1{32}$. For any $q,s$, if $p(a_t\mid qs)$ is $\nu_1$-close to uniform and $p(b_t\mid qs)$ is $\nu_2$-close to uniform, the conditional error given $q,s$ is at least $\tfrac14-\nu_1-\nu_2$ (the disjointness probability is within $\nu_1+\nu_2$ of $\tfrac14$). Set $\alpha_{qs}=|p(a_t\mid qs)-p(a_t\mid q)|$ and $\beta_{qs}=|p(b_t\mid qs)-p(b_t\mid q)|$. Then
$$\tfrac1{32} \ge \mathbb{E}_{p(q,s)}\!\big[\tfrac14-\alpha_{qs}-\beta_{qs}\big]\,p(a_t{=}0{=}b_t) \ge \mathbb{E}_{p(q,s\mid a_t=0=b_t)}\!\big[\tfrac14-\alpha_{qs}-\beta_{qs}\big],$$
which gives $\mathbb{E}_{p(q,s\mid a_t=0=b_t)}[\alpha_{qs}+\beta_{qs}] \ge \tfrac14-\tfrac18 = \tfrac18$. So one term is $\ge \tfrac1{16}$; WLOG $\mathbb{E}_{p(q,s\mid a_t=0=b_t)}[\alpha_{qs}] \ge \tfrac1{16}$. Hence
$$\mathbb{E}_{p(q,s\mid b_t=0)}[\alpha_{qs}] \ge p(a_t{=}0\mid b_t{=}0)\cdot \mathbb{E}_{p(q,s\mid a_t=0=b_t)}[\alpha_{qs}] \ge \tfrac1{32}. \qquad (6.2)$$
Intuitively, (6.2) says the protocol learns significant information about $a_t$ even conditioned on $b_t=0$; subadditivity of information will show this requires many communicated bits.

<a id="pdf-6d7577246334-p014-b003"></a>
<!-- pdf-source: page=14; block=3; confidence=0.90 -->
**Lemma 6.15.** Let $X=(X_1,\dots,X_n)$ and $Y=(Y_1,\dots,Y_n)$ be random variables such that the pairs $(X_1,Y_1),\dots,(X_n,Y_n)$ are mutually independent, and let $M$ be another random variable in the same space. Then
$$\sum_{i=1}^n I(X_i : M \mid X_{<i}Y_{\ge i}) \le I(X : M \mid Y),\qquad \sum_{i=1}^n I(Y_i : M \mid X_{\le i}Y_{>i}) \le I(Y : M \mid X).$$

<a id="pdf-6d7577246334-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.88 -->
**Proof.** By repeated application of the chain rule:
$$\sum_i I(X_i : M \mid X_{<i}Y_{\ge i}) \le \sum_i I(X_i : MY_{<i} \mid X_{<i}Y_{\ge i}) = \sum_i \big[I(X_i:Y_{<i}\mid X_{<i}Y_{\ge i}) + I(X_i:M\mid X_{<i}Y)\big] = \sum_i I(X_i:M\mid X_{<i}Y) = I(X:M\mid Y),$$
using $I(X_i:Y_{<i}\mid X_{<i}Y_{\ge i})=0$. The second bound is proved similarly.

<a id="pdf-6d7577246334-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.85 -->
Let $\mathcal{D}$ be the event that $A,B$ are disjoint. Then $p(ab\mid\mathcal D)$ satisfies the hypotheses of Lemma 6.15, and conditioned on $\mathcal D$, $T$ is independent of $A,B$. Lemma 6.15 gives
$$\tfrac{\ell}{n} \ge I(A_T : S \mid T\,A_{<T}B_{\ge T}\,\mathcal D) = I(A_T : S \mid Q\,B_T\,\mathcal D). \qquad (6.3)$$
Since $p(b_t=0\mid\mathcal D)=\tfrac23$, (6.3) implies $\tfrac{3\ell}{2n} \ge I(A_T : S \mid Q, B_T=0, \mathcal D) = I(A_T : S \mid Q, B_T=0)$ (because $B_T=0$ implies $\mathcal D$). By Pinsker's inequality (Corollary 6.7),
$$\sqrt{\tfrac{3\ell \ln 2}{4n}} \ge \mathbb{E}_{p(qs\mid b_t=0)}\big[\,|p(a_t\mid qs, b_t=0) - p(a_t\mid q, b_t=0)|\,\big] = \mathbb{E}_{p(qs\mid b_t=0)}[\alpha_{qs}].$$
Combining with (6.2), $\sqrt{3\ell\ln 2/(4n)} \ge \tfrac1{32}$, proving $\ell \ge \Omega(n)$, as required.

<a id="pdf-6d7577246334-p015-b003"></a>
<!-- pdf-source: page=15; block=3; confidence=0.85 -->
**Lower bound for number of rounds.** (Expository) A protocol with more rounds can use significantly less communication than one with fewer rounds. In the $k$-step pointer-chasing problem, Alice holds $x\in[n]^n$ and Bob holds $y\in[n]^n$. With $z_0=1$, define $z_1,z_2,\dots$ by
$$z_i = \begin{cases} x_{z_{i-1}} & i \text{ odd},\\ y_{z_{i-1}} & i \text{ even}. \end{cases}$$
(References: Yao 1983; Duris et al. 1987; Halstenberg–Reischuk 1993; Nisan–Wigderson 1993.)

<a id="pdf-6d7577246334-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.70 -->
Setup for the $k$-step pointer-chasing problem: inputs $x, y \in [n]^n$ are uniform; the parties must output whether $z_k > n/2$, where $z$ is the pointer-chasing sequence. Known protocols: (i) a deterministic protocol using $k$ rounds and $k\log n$ bits (each step a player announces $z_1, z_2, \dots, z_k$); (ii) a randomized protocol using $k-1$ rounds and $O((k + n/k)\log n)$ bits — in the first step Alice and Bob each announce the values $x_i, y_i$ for $i \le 10n/k$, then continue with the deterministic protocol but skip communication for any needed value already announced. In expectation this protocol uses $k+1-10$ rounds, and it has fewer than $k$ rounds with high probability, since for a uniformly random input most $z_i$ are distinct. Key idea (analogous to the indexing lower bound): argue by induction that $z_k$ stays close to uniform even after conditioning on the messages $m_{<k}$ of the first $k-1$ rounds, because a message $m_{k-1}$ sent by one player behaves like a random coordinate of the other player's input, keeping $z_k$ near-uniform.

<a id="pdf-6d7577246334-p016-b002"></a>
<!-- pdf-source: page=16; block=2; confidence=0.85 -->
**Theorem 6.16.** Any randomized (k−1)-round protocol for the k-step pointer-chasing problem that is correct with probability 1/2 + ε requires at least (ε² n)/(k−1)² − k log n bits of communication.

<a id="pdf-6d7577246334-p016-b003"></a>
<!-- pdf-source: page=16; block=3; confidence=0.90 -->
**Proof.** By induction on k, showing z_k stays close to uniform even conditioned on the messages sent in the first k−1 rounds (initially z_1 is uniform, with no conditioning). Let r_k denote the random variable (m_1,…,m_k, z_1,…,z_k). Prove by induction on k that, on average over r_{k−1}, p(z_k | r_{k−1}) is ε-close to uniform with ε ≤ (k−1)√((ℓ + log n)/n); rearranging yields ℓ ≥ ε²n/(k−1)² − k log n. The case k = 1 is trivial. For k ≥ 2 with k even (the odd case is identical): since (r_{k−2}, m_{k−1}) contains at most ℓ + k log n bits of information, Corollary 6.8 gives, for a uniformly random coordinate i independent of all other variables, on average over i: p(y_i | r_{k−2}) ≈_{ε'} p(y_i) ≈_{ε'} p(y_i | m_{k−1}, r_{k−2}), where ε' = √((ℓ + k log n)/n).

<a id="pdf-6d7577246334-p016-b004"></a>
<!-- pdf-source: page=16; block=4; confidence=0.75 -->
**Remark (margin note).** Theorem 6.16 in fact yields communication at least Ω(n/k²) in the randomized (k−1)-round setting: when k < 3√(n/log n), ε²n/(4(k−1)²) − k log n = Ω(n/k²); when k ≥ 3√(n/log n), the communication must be at least k, which is again Ω(n/k²).

<a id="pdf-6d7577246334-p017-b001"></a>
<!-- pdf-source: page=17; block=1; confidence=0.70 -->
**Proof (cont.).** With ε' = √((ℓ + k log n)/n), two cases. (i) Bob sends m_{k−1}: after fixing r_{k−2}, z_{k−1} is independent of y_i for every i; by induction p(z_{k−1} | r_{k−2}) is ε-close to uniform, so on average over r_{k−1}, i: p(z_k | r_{k−1}) = p(y_{z_{k−1}} | m_{k−1}, r_{k−2}) ≈_ε p(y_i | m_{k−1}, r_{k−2}) ≈_{ε'} p(y_i). (ii) Alice sends m_{k−1}: here p(y_i | r_{k−1}) = p(y_i | m_{k−1}, r_{k−2}) ≈_{ε'} p(y_i), since after fixing r_{k−2}, y_i is independent of m_{k−1}; hence p(z_k | r_{k−1}) = p(y_{z_{k−1}} | r_{k−2}) ≈_ε p(y_i | r_{k−2}) ≈_{ε'} p(y_i). Both cases give that p(z_k | r_{k−1}) is (k−1)√((ℓ + k log n)/n)-close to uniform, completing the induction.

<a id="pdf-6d7577246334-p017-b002"></a>
<!-- pdf-source: page=17; block=2; confidence=0.85 -->
Similar reasoning shows the deterministic communication of the pointer-chasing problem is Ω(n) when fewer than k rounds are used.

<a id="pdf-6d7577246334-p017-b003"></a>
<!-- pdf-source: page=17; block=3; confidence=0.90 -->
**Theorem 6.17.** Any (k−1)-round deterministic protocol that computes the k-step pointer-chasing problem requires at least n/16 − k bits of communication.

<a id="pdf-6d7577246334-p017-b004"></a>
<!-- pdf-source: page=17; block=4; confidence=0.80 -->
**Proof.** Consider any $(k-1)$-round deterministic protocol with communication complexity $\ell \le n/16 - k$, and let $m_1,\dots,m_{k-1}$ denote the messages of the protocol. Let $r_i$ denote $z_0, z_1,\dots,z_i, m_1,\dots,m_i$, and let $p$ denote the uniform distribution on inputs. We show by induction on $i$ that there is a fixed value of $r_i$ such that: (1) $z_0, z_1,\dots,z_i$ are all distinct; (2) $p(z_{i+1}\mid r_i)$ is $\varepsilon$-close to uniform with $\varepsilon = 2\sqrt{(\ell+k)/n} \le 1/4$; (3) $p(m_{\le i}\mid z_{\le i}) \ge 2^{-|m_{\le i}| - i}$. The first property applied to $i = k-1$ shows that the protocol cannot be correct, since $r_{k-1}$ contains all the messages in the first $k$ rounds, and so $p(z_k\mid r_{k-1})$ cannot be close to uniform. When $i = 0$ the claims are trivially satisfied. For even $i > 0$, $z_{i+1} = x_{z_i}$; by induction there is a setting of $r_{i-1}$ satisfying the conditions, and we extend it by choosing $z_i, m_i$. There are two cases; if Alice sends the $(i+1)$-st message, fixing $r_{i-1}$ leaves $m_i$ and $z_i$ independent.

<a id="pdf-6d7577246334-p018-b001"></a>
<!-- pdf-source: page=18; block=1; confidence=0.70 -->
**Proof (cont., Alice sends).** Choose m_i greedily, setting each bit to maximize its probability conditioned on r_{i−1} and all previous bits; this ensures p(m_i | r_{i−1}) ≥ 2^{−|m_i|}. To choose z_i, define: B1 = {z_0, z_1,…,z_{i−1}} (the already-used values); B2 = { j : p(x_j | m_i, r_{i−1}) / p(x_j) > 4·(ℓ+k)/n }; B3 = { j : p(Z_i = j | r_{i−1}) / p(Z_i = j | z_{≤i−1}) < 1/2 }.

<a id="pdf-6d7577246334-p018-b002"></a>
<!-- pdf-source: page=18; block=2; confidence=0.90 -->
**Claim 6.18.** |B1 ∪ B2 ∪ B3| < n.

<a id="pdf-6d7577246334-p018-b003"></a>
<!-- pdf-source: page=18; block=3; confidence=0.80 -->
**Proof.** $|B_1| \le k-1 < n/16 - \ell \le n/16$. $|B_3| \le 2\varepsilon n \le n/2$, for otherwise $p(Z_i \in B_3 \mid z_{\le i-1}) - p(Z_i \in B_3 \mid r_{i-1}) > 2\varepsilon - \varepsilon = \varepsilon$, contradicting that $p(z_i \mid r_{i-1})$ is $\varepsilon$-close to uniform. To bound $B_2$: $|B_2 - B_1|\cdot 4\cdot\tfrac{\ell+k}{n} \le \sum_{j \in B_2-B_1} \tfrac{p(x_j \mid m_i, r_{i-1})}{p(x_j)} = \sum_{j \in B_2-B_1} \tfrac{p(x_j \mid m_{\le i}, z_{\le i-1})}{p(x_j \mid z_{\le i-1})} \le \tfrac{p(x_{[n]-B_1} \mid m_{\le i}, z_{\le i-1})}{p(x_{[n]-B_1} \mid z_{\le i-1})}$ (Fact 6.4; $x_j$ is independent of $z_{\le i-1}$ for $j \notin B_1$, and $x_{[n]-B_1}$ denotes $x$ projected to the coordinates not in $B_1$). By the choice of $m_i$, $p(m_{\le i} \mid z_{\le i-1}) = p(m_i \mid r_{i-1})\cdot p(m_{\le i-1} \mid z_{\le i-1}) \ge 2^{-|m_i|}\cdot 2^{-|m_{\le i-1}|-i+1} \ge 2^{-\ell-k}$, so Fact 6.3 bounds the ratio by $\ell+k$, giving $|B_2 - B_1| \le n/4$. Thus $|B_1 \cup B_2 \cup B_3| < n/16 + n/2 + n/4 = n$.

<a id="pdf-6d7577246334-p019-b001"></a>
<!-- pdf-source: page=19; block=1; confidence=0.60 -->
**Proof (continued).** Set $z_i$ to be an arbitrary element outside of $B_1\cup B_2\cup B_3$. This completes the description of $r_i$. Since $z_i\notin B_1$, $z_0,\dots,z_i$ are distinct. Since after fixing $m_i, r_i$, $x$ is independent of $y$, the distribution of $p(x_{z_i}\mid r_i)$ is the same as that of $p(x_{z_i}\mid m_i\,r_{i-1})$; thus it is $2\sqrt{(\ell+k)/n}$-close to uniform by Pinsker's inequality and the fact that $z_i\notin B_2$. Finally,
$$p(m_{\le i}\mid z_{\le i}) = p(m_i\mid r_{i-1})\cdot p(m_{\le i-1}\mid z_{\le i}) \ge 2^{-|m_i|}\cdot\frac{p(z_i\mid m_{\le i-1}, z_{\le i-1})}{p(z_i\mid z_{\le i-1})}\cdot p(m_{\le i-1}\mid z_{\le i-1}) \ge 2^{-|m_{\le i}|-i}\cdot\tfrac12 = 2^{-|m_{\le i}|-(i+1)},$$
by the choice of $m_i$ and the fact that $z_i\notin B_3$.

<a id="pdf-6d7577246334-p019-b002"></a>
<!-- pdf-source: page=19; block=2; confidence=0.80 -->
**Case (Bob sends the $(i+1)$-st message).** Here $z_i$ is picked first. Define the sets:
- $B_1=\{z_0,z_1,\dots,z_{i-1}\}$,
- $B_2=\Big\{\,j:\ \dfrac{p(x_j\mid r_{i-1})}{p(x_j)} > 4\cdot\dfrac{\ell+k}{n}\,\Big\}$,
- $B_3=\Big\{\,j:\ \dfrac{p(Z_i=j\mid r_{i-1})}{p(Z_i=j\mid z_{\le i-1})} < \tfrac12\,\Big\}$.

<a id="pdf-6d7577246334-p019-b003"></a>
<!-- pdf-source: page=19; block=3; confidence=0.75 -->
**Claim 6.19.** $|B_1\cup B_2\cup B_3| < n$.

<a id="pdf-6d7577246334-p019-b004"></a>
<!-- pdf-source: page=19; block=4; confidence=0.85 -->
**Proof.** $|B_1|\le n/16$ and $|B_3|\le n/2$, as proved in Claim 6.18. We shall prove that $|B_2-B_1|\le n/4$. Observe that
$$|B_2-B_1|\cdot 4\cdot\tfrac{\ell+k}{n} \le \sum_{j\in B_2-B_1}\frac{p(x_j\mid r_{i-1})}{p(x_j)} = \sum_{j\in B_2-B_1}\frac{p(x_j\mid m_{\le i-1}, z_{\le i-1})}{p(x_j\mid z_{\le i-1})} \le \frac{p(x_{[n]-B_1}\mid m_{\le i-1}, z_{\le i-1})}{p(x_{[n]-B_1}\mid z_{\le i-1})} \le \ell+k,$$
giving that $|B_2-B_1|\le n/4$ (using that $x_j$ is independent of $z_{\le i-1}$ for $j\notin B_1$, together with Fact 6.4 and, since $p(m_{\le i-1}\mid z_{\le i-1})\ge 2^{-\ell-k}$, Fact 6.3). Thus $|B_1\cup B_2\cup B_3| < n/16 + n/2 + n/4 = n$.

<a id="pdf-6d7577246334-p019-b005"></a>
<!-- pdf-source: page=19; block=5; confidence=0.55 -->
**Proof (continued).** Let $z_i$ be an element not in $B_1\cup B_2\cup B_3$, and pick $m_i$ by greedily setting each bit so that the probability of that bit is maximized conditioned on $r_{i-1}$, $z_i$, and all previous bits. (Margin facts used: $x_j$ independent of $z_{\le i-1}$ for $j\notin B_1$ (Fact 6.4); $p(m_{i-1}\mid z_{\le i-1})\ge \ell\,2^{-k}$ (Fact 6.3).)

<a id="pdf-6d7577246334-p020-b001"></a>
<!-- pdf-source: page=20; block=1; confidence=0.75 -->
**Proof (continued).** Clearly, $z_0,\dots,z_i$ are all distinct. $p(x_{z_i}\mid r_i)$ has the same distribution as $p(x_{z_i}\mid r_{i-1})$, which is $2\sqrt{(\ell+k)/n}$-close to uniform by Pinsker's inequality and the fact that $z_i\notin B_2$. Finally,
$$p(m_{\le i}\mid z_{\le i}) \ge p(m_i\mid r_{i-1}, z_i)\cdot p(m_{\le i-1}\mid z_{\le i}) \ge 2^{-|m_i|}\cdot\frac{p(z_i\mid r_{i-1})}{p(z_i\mid z_{\le i-1})}\cdot p(m_{\le i-1}\mid z_{\le i-1}) \ge 2^{-|m_{\le i}|-(i+1)},$$
as required.

<a id="pdf-6d7577246334-p020-b002"></a>
<!-- pdf-source: page=20; block=2; confidence=0.80 -->
# Lower bounds on Non-Negative Rank

<a id="pdf-6d7577246334-p020-b003"></a>
<!-- pdf-source: page=20; block=3; confidence=0.90 -->
**Exercise 6.1.** For any two joint distributions $p(x,y),q(x,y)$ with the same support, show
$$\mathbb{E}_{p(y)}\!\left[\frac{p(x\mid y)}{p(x)}\right] \le \mathbb{E}_{p(y)}\!\left[\frac{p(x\mid y)}{q(x)}\right].$$

<a id="pdf-6d7577246334-p020-b004"></a>
<!-- pdf-source: page=20; block=4; confidence=0.90 -->
**Exercise 6.2.** For $n$ odd, let $x\in\{0,1\}^n$ be sampled uniformly at random from the strings having more 1's than 0's. Using Pinsker's inequality, show the expected number of 1's in $x$ is at most $n/2 + O(\sqrt{n})$.

<a id="pdf-6d7577246334-p020-b005"></a>
<!-- pdf-source: page=20; block=5; confidence=0.90 -->
**Exercise 6.3.** Let $X$ be a random variable supported on $[n]$ and $g:[n]\to[n]$ a function. Prove that
$$\Pr[X\ne g(X)] \ge \frac{H(X\mid g(X)) - 1}{\log n},$$
using that $\alpha\log\alpha \ge -\tfrac{\log e}{e} \ge -1$ for $\alpha>0$. Use this bound to show that if Alice has a uniformly random vector $y\in[n]^n$, Bob has a uniformly random input $i\in[n]$, and Alice sends Bob a message $M$ containing $\ell$ bits, then the probability that Bob guesses $y_i$ is at most $\frac{1+\ell/n}{\log n}$.

<a id="pdf-6d7577246334-p020-b006"></a>
<!-- pdf-source: page=20; block=6; confidence=0.95 -->
**Exercise 6.4.** Let $\mathcal{G}$ be a family of graphs on $n$ vertices such that every two vertices in the graph share a clique on $r$ vertices. Show that the number of graphs in the family is at most $2^{\binom{n}{2}/2^{\,r-1}}$.
