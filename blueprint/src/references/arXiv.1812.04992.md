<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: f300deb505d81092c17c30ca88b46f8962434aeae39439744921456a04576342 -->

<a id="pdf-f300deb505d8-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.95 -->
# Krawtchouk polynomials and quadratic semi-regular sequences

Derives lower and upper bounds on the degree of regularity of an overdetermined, zero-dimensional, homogeneous quadratic semi-regular system of polynomial equations, by interpreting the associated Hilbert series as the truncation of the generating function of values of the Krawtchouk orthogonal polynomials.

<a id="pdf-f300deb505d8-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.92 -->
Semi-regular sequences model generic homogeneous polynomial systems, generalizing regular sequences to the overdetermined case; they are designed to be as algebraically independent as possible in order to assess the complexity of Faugère's F5 Gröbner basis algorithm. The key complexity parameter is the degree of regularity $d_{reg}$, up to which algebraic independence holds. $d_{reg}$ essentially equals the Hilbert regularity and is obtained by expanding a rational function and truncating at the first non-positive coefficient; asymptotic estimates via the saddle-point method were given by Bardet et al. This work instead interprets the Hilbert series as the truncation of the generating function of values of the (binary) Krawtchouk polynomials, yielding descriptions of $d_{reg}$ from the location of extreme roots of these polynomials.

<a id="pdf-f300deb505d8-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.95 -->
For any overdetermined, zero-dimensional, homogeneous quadratic semi-regular system $f_1,\ldots,f_m \in \mathbf{K}[X_1,\ldots,X_n]$ with $m>n$ and degree of regularity $d_{reg}$, the following bounds are established.

**Lower bounds** (valid for any $m>n$):
- $d_{reg} \geq 1 + \lfloor \tfrac12(2m-n - 2\sqrt{m(m-n)}) \rfloor$ (Thm. bound-regularity-kz);
- $d_{reg} \geq 1 + \lfloor \tfrac12(w_4^6 - 1) \rfloor$ (Thm. bound-regularity-ls), where $w_4$ is the unique positive real root of the quartic $q(w) = w^4 - \frac{n}{\sqrt{2(2m-n)}}\,w - 6^{-1/3} i_1$ with $i_1 \approx 3.37213$.

**Upper bounds:**
- $d_{reg} \leq 1 + \lceil \tfrac12(2m-n+3 - \sqrt{(2m-n+1)^2 - 4n^2}) \rceil$ (Thm. upper-bound-regularity-ls);
- $d_{reg} \leq 1 + \lceil x_5^3 \rceil$ (Thm. upper-bound-regularity-l), where $x_5$ is a particular positive real root of the sextic $s(x) = x(x-1)^2(2m-n-x^3) - \tfrac14 n^2$.

The upper bounds require, respectively, $0 \leq (2m-n+1)^2 - 4n^2$, and $0 \leq \max_{x>1} s(x)$ together with $x_5^3 \leq \lfloor (2m-n)/2 \rfloor$.

<a id="pdf-f300deb505d8-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.97 -->
## Semi-regular sequences and Krawtchouk polynomials

<a id="pdf-f300deb505d8-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.94 -->
**Definition (semi-regular sequence).** Let $f_1,\ldots,f_m \in \mathbf{K}[X_1,\ldots,X_n]$ over a field $\mathbf{K}$ be zero-dimensional (so $S = \mathbf{K}[X_1,\ldots,X_n]/(f_1,\ldots,f_m)$ is finite-dimensional), overdetermined ($m>n$) and homogeneous quadratic ($\deg f_i = 2$). Writing $S(i-1) = \mathbf{K}[X_1,\ldots,X_n]/(f_1,\ldots,f_{i-1})$, the system is *semi-regular* if the multiplication map $S(i-1)_j \to S(i-1)_{j+2}$, $g \mapsto g f_i$, is injective for each $i=1,\ldots,m$ and each $j < d_{reg} - 2$.

The *degree of regularity* of the graded ideal $J=(f_1,\ldots,f_m)$ is
$$d_{reg} = \min\{\, d \geq 0 : \dim_{\mathbf{K}} J_d = \dim_{\mathbf{K}} \mathbf{K}[X_1,\ldots,X_n]_d \,\}.$$

<a id="pdf-f300deb505d8-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.94 -->
By BFSY2005 (Prop. 5(i)) and HMS2017 (Thm. 2.3(d)), $f_1,\ldots,f_m$ is semi-regular iff the Hilbert series of $S$ is
$$\mathrm{HS}_S(z) = \left|\frac{(1-z^2)^m}{(1-z)^n}\right|_+ = \left|(1-z)^{m-n}(1+z)^m\right|_+,$$
where $|\sum_{k\geq 0} a_k z^k|_+ = \sum_{\{k : \forall_{l\leq k}(a_l>0)\}} a_k z^k$ denotes truncation at the first non-positive coefficient. Consequently (BFSY2005, Prop. 5(iii)), $d_{reg}$ is the index of the first non-positive coefficient of $(1-z)^{m-n}(1+z)^m$, giving
$$d_{reg}(f_1,\ldots,f_m) = 1 + \deg(\mathrm{HS}_S(z)) \tag{eq:hilbert-regularity}$$
so $d_{reg}$ coincides with the Hilbert regularity of $S$.

<a id="pdf-f300deb505d8-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.93 -->
For semi-regular sequences the F5 Gröbner basis complexity is bounded (BFSY2005, Prop. 5(iv)) by
$$\mathcal{O}\!\left(m \cdot d_{reg} \cdot \binom{n+d_{reg}-1}{d_{reg}}^{\omega}\right),\quad \omega < 2.373.$$
The $k$-th coefficient, for $k=0,\ldots,2m-n$, is
$$[z^k](1-z)^{m-n}(1+z)^m = \sum_{j=0}^{k} (-1)^j \binom{m-n}{j}\binom{m}{k-j},$$
whose alternating sign makes it combinatorially unstable, so it is hard to derive conditions on $k$ ensuring positivity.

<a id="pdf-f300deb505d8-p002-b005"></a>
<!-- pdf-source: page=2; block=5; confidence=0.94 -->
Following Levenshtein, the general Krawtchouk polynomial of degree $k$ ($k=0,\ldots,N$) is
$$K_k^{N,r}(t) = \sum_{j=0}^{k} (-1)^j (r-1)^{k-j} \binom{t}{j}\binom{N-t}{k-j}.$$
**Ordinary generating function** (Levenshtein (43)):
$$(w-z)^x (w+(r-1)z)^{N-x} = \sum_{k=0}^{N} K_k^{N,r}(x)\, z^k w^{N-k}. \tag{eq:ogf-krawtchouk-general}$$
**Orthogonality** (binomial distribution weight; Levenshtein Cor. 2.3), for $l,k=0,\ldots,N$:
$$\sum_{i=0}^{N} K_l^{N,r}(i) K_k^{N,r}(i)(r-1)^i \binom{N}{i} = r^N (r-1)^l \binom{N}{l}\delta_{l,k}.$$
**Recurrence** (Levenshtein Cor. 3.3):
$$(k+1)K_{k+1}^{N,r}(t) = (N(r-1)-k(r-2)-rt)K_k^{N,r}(t) - (r-1)(N-k+1)K_{k-1}^{N,r}(t). \tag{eq:krawtchouk-recurrence}$$

<a id="pdf-f300deb505d8-p002-b006"></a>
<!-- pdf-source: page=2; block=6; confidence=0.93 -->
For the binary case $r=2$ (parameter dropped from notation), the generating function specializes to
$$(1-z)^{m-n}(1+z)^m = \sum_{k=0}^{2m-n} K_k^{2m-n}(m-n)\, z^k. \tag{eq:ogf-krawtchouk-binary}$$
First binary Krawtchouk polynomials (eq:few-krawtchouk), part 1:
$$K_1^{2m-n}(t) = 2m-n-2t,$$
$$K_2^{2m-n}(t) = \tfrac12\big[(K_1^{2m-n}(t))^2 - (2m-n)\big].$$

<a id="pdf-f300deb505d8-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.93 -->
Continuation of eq:few-krawtchouk:
$$K_3^{2m-n}(t) = \tfrac16\big[(K_1^{2m-n}(t))^3 - (3(2m-n)-2)\,K_1^{2m-n}(t)\big],$$
$$K_4^{2m-n}(t) = \tfrac1{24}\big[(K_1^{2m-n}(t))^4 - (6(2m-n)-8)(K_1^{2m-n}(t))^2 + 3(2m-n-2)(2m-n)\big].$$

<a id="pdf-f300deb505d8-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.30 -->
Figure 1 plots members of the family $K_k^{2m-n}(t)$ for $m=24,\ n=12$; a dashed line at $t=12$ marks their values, i.e. the first coefficients of $(1-z)^{12}(1+z)^{24} = \sum_{k=0}^{36} K_k^{36}(12)\,z^k$.

<a id="pdf-f300deb505d8-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.93 -->
Evaluations at $t=m-n$:
$$K_1^{2m-n}(m-n) = n,$$
$$K_2^{2m-n}(m-n) = \tfrac12[n^2 + n - 2m],$$
$$K_3^{2m-n}(m-n) = \tfrac16[n^3 + 3n^2 + 2n - 6mn],$$
$$K_4^{2m-n}(m-n) = \tfrac1{24}[n^4 + 6n^3 + (11-12m)n^2 + (6-12m)n + 12m(m-1)].$$

<a id="pdf-f300deb505d8-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.95 -->
## Roots of Krawtchouk polynomials and the degree of regularity

Roots of binary Krawtchouk polynomials are related to $d_{reg}$, the central observation of the article.

<a id="pdf-f300deb505d8-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.95 -->
**Theorem (Cf. Szegő, Thm. 3.3.1–3.3.2).** Let $d_k^N(1),\ldots,d_k^N(k)$ denote the roots of the binary Krawtchouk polynomial $K_k^N$, $k=1,\ldots,2m-n$. Then:
1. the roots of $K_k^N$ are real, distinct, and lie in the interior of $[0,N]$: $0 < d_k^N(1) < d_k^N(2) < \cdots < d_k^N(k) < N$;
2. the roots of $K_k^N$ and $K_{k+1}^N$ interlace: for $k=1,\ldots,N-1$ and $j=1,\ldots,k$, $\ d_{k+1}^N(j) < d_k^N(j) < d_{k+1}^N(j+1)$.

<a id="pdf-f300deb505d8-p003-b006"></a>
<!-- pdf-source: page=3; block=6; confidence=0.95 -->
**Lemma.** For an overdetermined, zero-dimensional, homogeneous quadratic semi-regular sequence $f_1,\ldots,f_m$, the degree of regularity is
$$d_{reg} = 1 + \max\{\, k : d_k^{2m-n}(1) > m-n \,\},$$
where $d_k^{2m-n}(1)$ is the smallest root of $K_k^{2m-n}$, $k=1,\ldots,2m-n$.

<a id="pdf-f300deb505d8-p003-b007"></a>
<!-- pdf-source: page=3; block=7; confidence=0.93 -->
**Proof.** Interlacing gives a strictly decreasing sequence of smallest roots $d_{2m-n}^{2m-n}(1) < \cdots < d_{k+1}^{2m-n}(1) < d_k^{2m-n}(1) < \cdots < d_1^{2m-n}(1)$. Thus $d_k^{2m-n}(1) > m-n$ implies $K_l^{2m-n}(m-n) > 0$ for all $l \leq k$.

Conversely, suppose $K_l^{2m-n}(m-n) > 0$ for all $l \leq k$ but $d_k^{2m-n}(1) \leq m-n$. Since $K_k^{2m-n}(0) = \binom{2m-n}{k} > 0$ and roots are distinct, there is an even $e$ with $d_k^{2m-n}(1) < \cdots < d_k^{2m-n}(e) < m-n \leq d_k^{2m-n}(e+1)$. Take minimal such $k$; then $k>1$ since $K_1^{2m-n}(t)=2m-n-2t$ has $d_1^{2m-n}(1) = \tfrac12(2m-n) > m-n$. By interlacing each of the intervals $[d_k^{2m-n}(1),d_k^{2m-n}(2)],\ldots,[d_k^{2m-n}(e-1),d_k^{2m-n}(e)]$ contains exactly one root of $K_{k-1}^{2m-n}$; since $e$ is even their number is odd and $K_{k-1}^{2m-n}(0) = \binom{2m-n}{k-1} > 0$, so either $K_{k-1}^{2m-n}(m-n) \leq 0$ (contradicting the assumption) or $d_k^{2m-n}(e) < d_{k-1}^{2m-n}(e) < m-n \leq d_k^{2m-n}(e+1)$ (contradicting minimality of $k$).

Hence $\{k : \forall_{l\leq k}(K_l^{2m-n}(m-n)>0)\} = \{k : d_k^{2m-n}(1) > m-n\}$, and
$$\mathrm{HS}_S(z) = |(1-z)^{m-n}(1+z)^m|_+ = \sum_{\{k : d_k^{2m-n}(1) > m-n\}} K_k^{2m-n}(m-n)\,z^k,$$
so $\deg(\mathrm{HS}_S(z)) = \max\{k : d_k^{2m-n}(1) > m-n\}$. $\square$

<a id="pdf-f300deb505d8-p003-b008"></a>
<!-- pdf-source: page=3; block=8; confidence=0.92 -->
**Theorem (Cf. Levenshtein, Thm. 6.1).** The smallest root of $K_k^{2m-n}$ satisfies
$$d_k^{2m-n}(1) = \frac{2m-n}{2} - \max_{\|w\|_2^2 = 1}\left(\sum_{i=0}^{k-2} w_i w_{i+1}\sqrt{(i+1)(2m-n-i)}\right).$$

<a id="pdf-f300deb505d8-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.70 -->
Closes a theorem carried over from the previous page (its statement is not on this page). States that determining the degree of regularity of a semi-regular sequence can be framed as an eigenvalue problem.

<a id="pdf-f300deb505d8-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.96 -->
**Lemma (regularity–eigenvalue).** For $f_1,\ldots,f_m \in \mathbf{K}[X_1,\ldots,X_n]$ as in the smallest-root lemma, the degree of regularity is
$$d_{reg} = 1 + \max\{k : \lambda_k^{2m-n} < n\},$$
where $\lambda_k^{2m-n}$ is the largest eigenvalue of the real symmetric tridiagonal matrix $A_k^{2m-n}\in\mathbf{R}^{k\times k}$ with $(A_k^{2m-n})_{ij}=\sqrt{(i+1)(2m-n-i)}$ for $|i-j|=1$ and $0$ otherwise, for $i,j=0,\ldots,k-1$ and $k=1,\ldots,2m-n$ (nonzero only on super/subdiagonal).

<a id="pdf-f300deb505d8-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.85 -->
**Proof.** Reformulation of the smallest-root lemma via the smallest-root/quadratic-form theorem plus linear algebra: $2\,d_k^{2m-n}(1)=2m-n-2\max_{\|w\|_2^2=1}(w^t\tilde A w)$, with $\tilde A\in\mathbf{R}^{k\times k}$ nonzero only on the superdiagonal, $(\tilde A)_{ij}=\sqrt{(i+1)(2m-n-i)}$ for $j-i=1$. Replacing $\tilde A$ by the symmetric matrix $\tfrac12(\tilde A+\tilde A)^t=\tfrac12 A_k^{2m-n}$ preserves the quadratic form, giving $2\,d_k^{2m-n}(1)=2m-n-\lambda_k^{2m-n}$. Hence $d_{reg}=1+\max\{k:d_k^{2m-n}(1)>m-n\}=1+\max\{k:2m-n-\lambda_k^{2m-n}>2(m-n)\}=1+\max\{k:\lambda_k^{2m-n}<n\}$.

<a id="pdf-f300deb505d8-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.90 -->
The tridiagonal matrix is a Golub–Kahan matrix; no explicit formulae for its eigenvalues are known, and Kouachi's general results on tridiagonal eigenvalues do not apply. Consequently the lemma is used only to translate lower/upper bounds on the smallest root of binary Krawtchouk polynomials into bounds on $d_{reg}$.

<a id="pdf-f300deb505d8-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.95 -->
**Lemma (regularity–bounds).** With $d_{reg}$ for $f_1,\ldots,f_m$:
$$d_{reg}\ge 1+\max\{k:\mathrm{LB}_k^{2m-n}(1)>m-n\},\qquad d_{reg}\le 1+\min\{k:\mathrm{UB}_k^{2m-n}(1)<m-n\},$$
where $\mathrm{LB}_k^{2m-n}(1)$, $\mathrm{UB}_k^{2m-n}(1)$ are (not necessarily strict) lower/upper bounds for the smallest root $d_k^{2m-n}(1)$ of the binary Krawtchouk polynomial $K_k^{2m-n}$, $k=1,\ldots,2m-n$. If the bounds are strict they may attain the threshold $m-n$: $d_{reg}\ge 1+\max\{k:\mathrm{LB}_k^{2m-n}(1)\ge m-n\}$ and $d_{reg}\le 1+\min\{k:\mathrm{UB}_k^{2m-n}(1)\le m-n\}$.

<a id="pdf-f300deb505d8-p004-b006"></a>
<!-- pdf-source: page=4; block=6; confidence=0.94 -->
**Proof.** Uses the set inclusions $\{k:\mathrm{LB}_k^{2m-n}(1)>m-n\}\subseteq\{k:d_k^{2m-n}(1)>m-n\}$ and $\{k:d_k^{2m-n}(1)>m-n\}\subseteq\{k:k\le\min\{k':\mathrm{UB}_{k'}^{2m-n}(1)<m-n\}\}$. The strict-bound threshold claims are immediate.

<a id="pdf-f300deb505d8-p004-b007"></a>
<!-- pdf-source: page=4; block=7; confidence=0.95 -->
**Lemma (smallest-root lower bounds)** [Krasikov–Zarkh 2009 Cor. 1; Levenshtein 1995 (125); Szegő (6.32.6)]. For the smallest root $d_k^{2m-n}(1)$ of $K_k^{2m-n}$:

(eq. smallest-root-lower-bounds-kz) for $1\le k<\tfrac12(2m-n)$ (Krasikov–Zarkh):
$$d_k^{2m-n}(1)>\tfrac12(2m-n)-\sqrt{k(2m-n-k)}\left(1-\tfrac32\left(\tfrac{2m-n-2k}{2k(2m-n-k)}\right)^{2/3}\right).$$

(eq. smallest-root-lower-bounds-ls) for each $k=1,\ldots,2m-n$ (Levenshtein 1995 (125) combined with Szegő's upper bound on the largest Hermite root $h_k$):
$$d_k^{2m-n}(1)>\tfrac12(2m-n)-\sqrt{\tfrac12(2m-n)}\left(\sqrt{2k+1}-6^{-1/3}i_1(2k+1)^{-1/6}\right),$$
where $i_1<i_2<\cdots$ are the real zeros of the Airy function $\mathcal A(x)$ solving $y''+\tfrac13 xy=0$, with $i_1\approx3.37213$ and $6^{-1/3}i_1\approx1.85575$.

<a id="pdf-f300deb505d8-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.95 -->
**Lemma (smallest-root upper bounds)** [Levenshtein 1983 (6.25); Levenshtein 1995 (124); Szegő (6.2.14)]. For the smallest root $d_k^{2m-n}(1)$ of $K_k^{2m-n}$:

(eq. smallest-root-upper-bounds-ls) for each $k=1,\ldots,2m-n$ (Levenshtein 1995 (124) with Szegő's lower bound on the largest Hermite root $h_k$):
$$d_k^{2m-n}(1)<\tfrac12(2m-n)-\tfrac12\sqrt{(2m-n-k+2)(k-1)}.$$

(eq. smallest-root-upper-bounds-l) for $1\le k\le\tfrac12(2m-n)$ (Levenshtein 1983 (6.25); cf. Krasikov 1999 (74)):
$$d_k^{2m-n}(1)<\tfrac12(2m-n)-\left(k^{1/2}-k^{1/6}\right)\sqrt{2m-n-k}.$$

<a id="pdf-f300deb505d8-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.90 -->
Each bound is treated separately to derive corresponding degree-of-regularity bounds. Further bounds exist (Area 2015; Paschoa et al.; Jooste–Jordaan 2014): Jooste–Jordaan Thm 3.2 gives only $d_k^{2m-n}(1)<\tfrac12(2m-n)$ (no extra information); Paschoa et al. Cor. 5.2 coincides with (eq. smallest-root-lower-bounds-ls); Paschoa et al. Thm 5.1/Cor. 5.1 and Area 2015 Thm 1 are left to future research.

<a id="pdf-f300deb505d8-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.90 -->
Two figures plot members of the family $K_k^{36}$ from $(1-z)^{12}(1+z)^{24}=\sum_{k=0}^{36}K_k^{36}(12)z^k$. Lower-bound figure: $K_4^{36}(12)<0$ while $K_3^{36}(12)>0$; first root $d_3^{36}(1)\approx12.85$, with Krasikov–Zarkh bound $\mathrm{KZ}_3\approx12.29$ and Levenshtein–Szegő $\mathrm{LS}_3\approx12.47$. Upper-bound figure: $K_4^{36},K_5^{36},K_6^{36}$ are negative at $12$; the first upper bounds below $12$ are those on $d_6^{36}(1)\approx8.45$, with $\mathrm{LS}^6\approx11.68$ and Levenshtein $\mathrm{L}^6\approx11.97$.

<a id="pdf-f300deb505d8-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.98 -->
# Lower bound on the regularity following Krasikov and Zarkh

<a id="pdf-f300deb505d8-p005-b005"></a>
<!-- pdf-source: page=5; block=5; confidence=0.97 -->
**Theorem (bound-regularity-kz).** For $f_1,\ldots,f_m$ as before, the smaller root of $p(k)=k^2-(2m-n)k+\tfrac14 n^2$ yields the lower bound
$$d_{reg}\ge 1+\left\lfloor\tfrac12\left(2m-n-2\sqrt{m(m-n)}\right)\right\rfloor.$$

<a id="pdf-f300deb505d8-p005-b006"></a>
<!-- pdf-source: page=5; block=6; confidence=0.93 -->
**Proof.** From the regularity–bounds lemma and (eq. smallest-root-lower-bounds-kz), $d_{reg}\ge1+\max\{k:m-n\le\tfrac12(2m-n)-\sqrt{k(2m-n-k)}(1-\tfrac32(\tfrac{2m-n-2k}{2k(2m-n-k)})^{2/3})\}$ over $k=1,\ldots,\lfloor(2m-n)/2\rfloor$. So seek the largest integer $1\le k\le\lfloor(2m-n)/2\rfloor$ with (eq. kz-largest-k) $0\le\tfrac n2-\sqrt{k(2m-n-k)}(1-\tfrac32(\tfrac{2m-n-2k}{2k(2m-n-k)})^{2/3})$. On $1\le k\le(2m-n)/2$ the factor $1-\tfrac32(\tfrac{2m-n-2k}{2k(2m-n-k)})^{2/3}$ is monotonically increasing (positive derivative for $m>n$) and, evaluated at $k=1$ and $k=(2m-n)/2$, lies in $(0,1]$; hence it suffices that $0\le\tfrac n2-\sqrt{k(2m-n-k)}$, i.e. $0\le k^2-(2m-n)k+\tfrac14 n^2$. The polynomial $p(k)$ has discriminant $\mathrm{Disc}_k(p)=m(m-n)>0$ and roots $k_{1,2}=\tfrac12(2m-n\pm2\sqrt{m(m-n)})$. Since $k\le\lfloor(2m-n)/2\rfloor$, the valid integer satisfies $k\le\lfloor\tfrac12(2m-n-2\sqrt{m(m-n)})\rfloor$.

<a id="pdf-f300deb505d8-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.98 -->
# Lower bound on the regularity following Levenshtein and Szegő

<a id="pdf-f300deb505d8-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.94 -->
**Theorem (bound-regularity-ls).** (Recall $i_1\approx3.37213$.) The quartic $q(w)=w^4-\tfrac{n}{\sqrt{2(2m-n)}}w-6^{-1/3}i_1$ has a unique positive real root $w_4$, and
$$d_{reg}\ge 1+\left\lfloor\tfrac12(w_4^6-1)\right\rfloor.$$
With $a=\tfrac{n}{\sqrt{2(2m-n)}}$ and $b=-6^{-1/3}i_1\approx-1.85575$,
$$w_4=\tfrac12\left(\sqrt{A}+\sqrt{\tfrac{2a}{\sqrt A}-A}\right),\quad A=B^{1/3}-\tfrac{4b}{3}B^{-1/3},\quad B=\tfrac12 a^2+\tfrac12\sqrt{a^4+\tfrac{256}{27}b^3}.$$

<a id="pdf-f300deb505d8-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.90 -->
**Proof.** From the regularity–bounds lemma and (eq. smallest-root-lower-bounds-ls), $d_{reg}\ge1+\max\{k:m-n\le\tfrac12(2m-n)-\sqrt{\tfrac12(2m-n)}(\sqrt{2k+1}-6^{-1/3}i_1(2k+1)^{-1/6})\}$ over $k=1,\ldots,2m-n$. Seek the largest integer $1\le k\le2m-n$ with $0\le\tfrac n2-\sqrt{\tfrac12(2m-n)}(\sqrt{2k+1}-6^{-1/3}i_1(2k+1)^{-1/6})$; since $m>n$ this reduces to $0\le\tfrac{n}{\sqrt{2(2m-n)}}-\sqrt{2k+1}-6^{-1/3}i_1(2k+1)^{-1/6}$. Substituting (eq. k-variable-substitution) $k\mapsto\tfrac12(w^6-1)$ gives the Laurent polynomial $-w^3+6^{-1/3}i_1\tfrac1w+\tfrac{n}{\sqrt{2(2m-n)}}$, i.e. the rational function $-\tfrac1w(w^4-\tfrac{n}{\sqrt{2(2m-n)}}w-6^{-1/3}i_1)$, whose numerator is $q(w)$. Its discriminant $\mathrm{Disc}_w(q)=-256(6^{-1/3}i_1)^3-27(\tfrac{n}{\sqrt{2(2m-n)}})^4<0$ for $m>n$, so $q$ has two complex-conjugate roots $w_1,w_2$ and two real roots $w_3\le w_4$; the negative constant term $\approx-1.85575$ forces a unique positive real root $w_4$. Undoing the substitution yields the claimed bound; the closed form for $w_4$ is obtained by symbolic computation in SageMath.

<a id="pdf-f300deb505d8-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.92 -->
Plot of $q(w)=w^4-\tfrac{n}{\sqrt{2(2m-n)}}w-6^{-1/3}i_1$ for $m=24$, $n=12$, i.e. $w^4-0.1179\,w-1.85575$. Real roots $w_3\approx-0.88$ and $w_4\approx1.40$, so $\tfrac12(w_4^6-1)\approx3.26$. The first non-positive coefficient in $(1-z)^{12}(1+z)^{24}$ is that of $z^4$, and $d_{reg}=4\ge1+\lfloor3.26\rfloor=4$.

<a id="pdf-f300deb505d8-p006-b005"></a>
<!-- pdf-source: page=6; block=5; confidence=0.95 -->
**Corollary.** If $m$ grows subquadratically, $m=o(n^2)$, then as $n\to\infty$ the lower bound of the Levenshtein–Szegő theorem satisfies
$$1+\left\lfloor\tfrac12(w_4^6-1)\right\rfloor\sim\frac{n^2}{4(2m-n)}.$$
($f\sim g$ iff $\lim_{x\to\infty}f(x)/g(x)=1$.)

<a id="pdf-f300deb505d8-p006-b006"></a>
<!-- pdf-source: page=6; block=6; confidence=0.93 -->
**Proof.** For $m=o(n^2)$: $a\to\infty$, $B\sim a^2$, $A\sim a^{2/3}$. Then $w_4\sim\tfrac12\sqrt{a^{2/3}}+\tfrac12\sqrt{\tfrac{2a}{\sqrt{a^{2/3}}}-a^{2/3}}=\tfrac12 a^{1/3}+\tfrac12\sqrt{2a^{2/3}-a^{2/3}}=a^{1/3}$, and $\tfrac12(w_4^6-1)\sim\tfrac12(a^2-1)=\tfrac12(\tfrac{n^2}{2(2m-n)}-1)\sim\tfrac{n^2}{4(2m-n)}$.

<a id="pdf-f300deb505d8-p006-b007"></a>
<!-- pdf-source: page=6; block=7; confidence=0.95 -->
**Corollary (asymptotic-cases-ls).** For real constants $\alpha,\beta>0$ and $\gamma\in(0,1)$, as $n\to\infty$ the Levenshtein–Szegő lower bound behaves as
$$1+\left\lfloor\tfrac12(w_4^6-1)\right\rfloor\sim\begin{cases}\tfrac{n}{4(1+2\alpha/n)} & m=n+\alpha,\\ \tfrac{n}{4(2\beta-1)} & m=\beta n,\\ \tfrac{n}{4(2\log(n)-1)} & m=n\log(n),\\ \tfrac18 n^{\gamma} & m=n^{2-\gamma}.\end{cases}$$
(A deeper monotonicity-based asymptotic analysis is omitted for brevity.)

<a id="pdf-f300deb505d8-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.95 -->
**Remark.** Corollary `cor:asymptotic-cases-ls` resembles the Gröbner basis computation cost summary in [BFS2003, §6], though the underlying polynomial equation systems differ.

<a id="pdf-f300deb505d8-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.95 -->
**Remark.** If $m$ grows quadratically ($m=\delta n^2$, $\delta\in\mathbf{R}_{>0}$) or superquadratically ($m=\omega(n^2)$), the lower bound of `thm:bound-regularity-ls` tends to $2$. Explanation: as the number of quadratic semi-regular (algebraically independent) equations grows, the Macaulay matrix already contains all homogeneous degree-2 entries, whose total count is $\binom{n+2+1}{n+1}\sim\tfrac12 n^2$.

<a id="pdf-f300deb505d8-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.99 -->
# Upper bound on the regularity following Levenshtein and Szegő

<a id="pdf-f300deb505d8-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.85 -->
**Theorem (upper bound, Levenshtein–Szegő).** Let $f_1,\ldots,f_m\in\mathbf{K}[X_1,\ldots,X_n]$ be as in `lem:regularity-smallest-root`. If the discriminant $\mathrm{Disc}_k(t)=(2m-n+1)^2-4n^2$ of $t(k)=k^2-(2m-n+3)k+2m-n+2+n^2$ is non-negative, then
$$d_{reg}\leq 1+\left\lceil\tfrac12\left(2m-n+3-\sqrt{(2m-n+1)^2-4n^2}\right)\right\rceil.$$
The bound comes from the smaller root of $t$.

<a id="pdf-f300deb505d8-p007-b005"></a>
<!-- pdf-source: page=7; block=5; confidence=0.92 -->
**Proof.** By `lem:regularity-bounds` and equation `eq:smallest-root-upper-bounds-ls` (from `lem:smallest-root-upper-bounds`),
$$d_{reg}\leq 1+\min\{k:\ m-n\geq\tfrac12(2m-n)-\tfrac12\sqrt{(2m-n-k+2)(k-1)}\},\quad k=1,\ldots,2m-n.$$
Equivalently, seek the smallest integer $1\leq k\leq 2m-n$ with
$$n\leq\sqrt{(2m-n-k+2)(k-1)}\quad(\text{eq:ls-smallest-k}).$$
Squaring gives $0\geq k^2-(2m-n+3)k+(2m-n+2+n^2)$. The roots of $t(k)=k^2-(2m-n+3)k+(2m-n+2+n^2)$ are $k_{1,2}=\tfrac12(2m-n+3\pm\sqrt{(2m-n+1)^2-4n^2})$, real iff $0\leq\mathrm{Disc}_k(t)=(2m-n+1)^2-4n^2$ (eq:ls-quadratic-discriminant). Taking the smallest such integer $k$ yields $d_{reg}\leq 1+\lceil\tfrac12(2m-n+3-\sqrt{(2m-n+1)^2-4n^2})\rceil$. $\qed$

<a id="pdf-f300deb505d8-p007-b006"></a>
<!-- pdf-source: page=7; block=6; confidence=0.93 -->
**Remark.** Unlike the lower bounds of `thm:bound-regularity-kz` and `thm:bound-regularity-ls`, which exist for all $m>n$, the upper bound of `thm:upper-bound-regularity-ls` requires the non-negative discriminant $\mathrm{Disc}_k(t)=(2m-n+1)^2-4n^2$, interpretable via the Krawtchouk polynomial family (the figure illustrates the non-negative case). For negative discriminant the set $\{k:\mathrm{UB}_k^{2m-n}(1)\leq m-n\}$ from `lem:regularity-bounds` is empty; i.e. the Levenshtein–Szegő upper bound never passes $m-n$ for any family member.

<a id="pdf-f300deb505d8-p007-b007"></a>
<!-- pdf-source: page=7; block=7; confidence=0.99 -->
# Upper bound on the regularity following Levenshtein

<a id="pdf-f300deb505d8-p007-b008"></a>
<!-- pdf-source: page=7; block=8; confidence=0.90 -->
**Theorem (upper bound, Levenshtein).** Let $f_1,\ldots,f_m\in\mathbf{K}[X_1,\ldots,X_n]$ be as in `lem:regularity-smallest-root`. The sextic
$$s(x)=x(x-1)^2(2m-n-x^3)-\tfrac14 n^2$$
has a global maximum at some $x'\in(1,(2m-n)^{1/3})$. If $s(x')\geq 0$, then $s$ has a unique real root $x_5\in(1,x']$. If $x_5^3\leq\lfloor(2m-n)/2\rfloor$, then
$$d_{reg}\leq 1+\lceil x_5^3\rceil.$$

<a id="pdf-f300deb505d8-p007-b009"></a>
<!-- pdf-source: page=7; block=9; confidence=0.92 -->
**Proof.** By `lem:regularity-bounds` and `eq:smallest-root-upper-bounds-l`,
$$d_{reg}\leq 1+\min\{k:\ m-n\geq\tfrac{2m-n}{2}-(k^{1/2}-k^{1/6})\sqrt{2m-n-k}\},\quad k=1,\ldots,\lfloor(2m-n)/2\rfloor.$$
Seek smallest integer $1\leq k\leq\lfloor(2m-n)/2\rfloor$ with
$$\tfrac{n}{2}\leq(k^{1/2}-k^{1/6})\sqrt{2m-n-k}=(k^{1/3}-1)\sqrt{k^{1/3}(2m-n-k)}\quad(\text{eq:l-smallest-k}).$$
Substituting $k\to x^3$ and squaring gives $\tfrac14 n^2\leq x(x-1)^2(2m-n-x^3)$ (eq:l-smallest-k-substitute), so consider roots of $s(x)=x(x-1)^2(2m-n-x^3)-\tfrac14 n^2$. By Rolle, $s$ has a local extremum at $1$ and further extrema in $(0,1)$ and $(1,(2m-n)^{1/3})$. The derivative is
$$s'(x)=(1-x)\big(6x^4-4x^3-3x(2m-n)+(2m-n)\big)\quad(\text{eq:l-quartic}).$$
The quartic factor $r$ has $\mathrm{Disc}_x(r)=-78732(2m-n)^4-39744(2m-n)^3-6912(2m-n)^2<0$ for $m>n$, so $r$ has two complex conjugate and two real roots $x'_3<x'_4$. Thus $s$ has exactly three local extrema: at $1$, $x'_3\in(0,1)$, $x'_4\in(1,(2m-n)^{1/3})$; a second-derivative test gives a local minimum at $1$ and local maxima at $x'_3,x'_4$ for $m>n$. Restrict to $(1,(2m-n)^{1/3})$ since $1\leq k\leq\lfloor(2m-n)/2\rfloor$ forces $x\in[1,\lfloor(2m-n)/2\rfloor^{1/3}]$. Since $s(1)=-n^2/4<0$, if $s(x'_4)\geq0$ the IVT gives a unique root $x_5\in(1,x'_4)$. Undoing the substitution, $k=x_5^3$ satisfies eq:l-smallest-k when $x_5^3\leq\lfloor(2m-n)/2\rfloor$, whence $d_{reg}\leq 1+\lceil x_5^3\rceil$. $\qed$

<a id="pdf-f300deb505d8-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.95 -->
**Figure (sextic).** Plot of $x(x-1)^2(2m-n-x^3)-n^2/4$ for $m=24$, $n=12$. Real roots $x_5\approx1.81$, $x_6\approx3.23$; the relevant root $x_5$ gives upper bound $1+\lceil x_5^3\rceil=7$. The first non-positive coefficient in $(1-z)^{12}(1+z)^{24}$ is that of $z^4$, so $d_{reg}=4\leq7$.

<a id="pdf-f300deb505d8-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.95 -->
**Remark.** The sextic of `thm:upper-bound-regularity-l` is irreducible with full Galois group $\mathfrak{S}_6$ for almost all $m>n$, so Hagedorn's [Hagedorn2000] solvable-sextic methods do not apply. For almost all remaining cases it factors into a linear and a quintic factor with Galois group $\mathfrak{S}_5$, so solvable-quintic methods [Dummit1991] also fail; in some such cases the linear factor coincides with the root giving the bound. Otherwise $x_5$ is found by numerical root-finding.

<a id="pdf-f300deb505d8-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.96 -->
**Remark.** The existence conditions for the upper bound in `thm:upper-bound-regularity-l`, namely $0\leq\max_{x>1}s(x)$ and $x_5^3\leq\lfloor(2m-n)/2\rfloor$, are interpreted in complete analogy to `rem:rausfliegen-family`.

<a id="pdf-f300deb505d8-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.96 -->
**Remark.** The position of the local maximum $x'$ of the sextic $s$ can be given explicitly by symbolic computation in SageMath applied to the quartic factor of `eq:l-quartic`.

<a id="pdf-f300deb505d8-p008-b005"></a>
<!-- pdf-source: page=8; block=5; confidence=0.99 -->
# Concrete values and comparisons

<a id="pdf-f300deb505d8-p008-b006"></a>
<!-- pdf-source: page=8; block=6; confidence=0.93 -->
The tables compare the lower bounds $\mathrm{LB_{KZ}}$, $\mathrm{LB_{LS}}$ (from `thm:bound-regularity-kz`, `thm:bound-regularity-ls`) and upper bounds $\mathrm{UB_{LS}}$, $\mathrm{UB_L}$ (from `thm:upper-bound-regularity-ls`, `thm:upper-bound-regularity-l`) against the asymptotic estimates of Bardet et al. [BFSY2005, Thm 1] (asymptotic term omitted). Note: the Airy function of [BFSY2005, (3)] solving $y''-xy=0$ differs from the Airy function used here in `eq:smallest-root-lower-bounds-ls`.

<a id="pdf-f300deb505d8-p008-b007"></a>
<!-- pdf-source: page=8; block=7; confidence=0.97 -->
**Table ($m=n+100$).** Columns: $n$, $d_{reg}$, [BFSY2005 (2)], $\mathrm{LB_{KZ}}$, $\mathrm{LB_{LS}}$, $\mathrm{UB_{LS}}$, $\mathrm{UB_L}$.

| $n$ | $d_{reg}$ | BFSY(2) | LBKZ | LBLS | UBLS | UBL |
|---|---|---|---|---|---|---|
| 256 | 48 | -0.86 | 40 | 44 | - | 75 |
| 512 | 121 | 71.48 | 109 | 103 | - | 184 |
| 1024 | 294 | 244.18 | 277 | 228 | - | 448 |
| 2048 | 684 | 634.64 | 661 | 485 | - | - |
| 4096 | 1534 | 1483.93 | 1501 | 1000 | - | - |
| 8192 | 3333 | 3282.76 | 3286 | 2029 | - | - |
| 16384 | 7075 | 7024.89 | 7009 | 4084 | - | - |
| 32768 | 14766 | 14715.35 | 14672 | 8189 | - | - |

<a id="pdf-f300deb505d8-p008-b008"></a>
<!-- pdf-source: page=8; block=8; confidence=0.97 -->
**Table ($m=n+256$).** Columns: $n$, $d_{reg}$, [BFSY2005 (2)], LBKZ, LBLS, UBLS, UBL.

| $n$ | $d_{reg}$ | BFSY(2) | LBKZ | LBLS | UBLS | UBL |
|---|---|---|---|---|---|---|
| 256 | 29 | -95.87 | 22 | 28 | 100 | 46 |
| 512 | 79 | -46.95 | 69 | 73 | 492 | 116 |
| 1024 | 210 | 83.65 | 196 | 184 | - | 294 |
| 2048 | 532 | 405.58 | 513 | 427 | - | 724 |
| 4096 | 1277 | 1150.14 | 1249 | 933 | - | 1741 |
| 8192 | 2977 | 2794.71 | 2882 | 1957 | - | - |
| 16384 | 6442 | 6314.05 | 6385 | 4009 | - | - |
| 32768 | 13814 | 13686.09 | 13733 | 8113 | - | - |

<a id="pdf-f300deb505d8-p008-b009"></a>
<!-- pdf-source: page=8; block=9; confidence=0.97 -->
**Table ($m=2n$).** Columns: $n$, $d_{reg}$, [BFSY2005 (3)], LBKZ, LBLS, UBLS, UBL.

| $n$ | $d_{reg}$ | BFSY(3) | LBKZ | LBLS | UBLS | UBL |
|---|---|---|---|---|---|---|
| 256 | 29 | 27.10 | 22 | 28 | 100 | 46 |
| 512 | 52 | 50.79 | 44 | 51 | 198 | 78 |
| 1024 | 98 | 96.87 | 88 | 96 | 393 | 139 |
| 2048 | 189 | 187.45 | 176 | 184 | 785 | 253 |
| 4096 | 368 | 366.58 | 352 | 358 | 1567 | 469 |
| 8192 | 724 | 722.29 | 703 | 703 | 3131 | 884 |
| 16384 | 1432 | 1430.51 | 1406 | 1391 | 6260 | 1687 |
| 32768 | 2844 | 2842.91 | 2812 | 2763 | 12519 | 3249 |

<a id="pdf-f300deb505d8-p008-b010"></a>
<!-- pdf-source: page=8; block=10; confidence=0.97 -->
**Table ($m=8n$).** Columns: $n$, $d_{reg}$, [BFSY2005 (3)], LBKZ, LBLS, UBLS, UBL.

| $n$ | $d_{reg}$ | BFSY(3) | LBKZ | LBLS | UBLS | UBL |
|---|---|---|---|---|---|---|
| 256 | 8 | 6.57 | 5 | 8 | 20 | 14 |
| 512 | 14 | 11.83 | 9 | 14 | 37 | 23 |
| 1024 | 23 | 21.61 | 18 | 23 | 71 | 37 |
| 2048 | 42 | 40.26 | 35 | 42 | 140 | 63 |
| 4096 | 78 | 76.41 | 69 | 78 | 277 | 111 |
| 8192 | 149 | 147.23 | 137 | 149 | 551 | 201 |
| 16384 | 289 | 287.05 | 274 | 288 | 1100 | 371 |
| 32768 | 566 | 564.37 | 547 | 565 | 2197 | 696 |

<a id="pdf-f300deb505d8-p008-b011"></a>
<!-- pdf-source: page=8; block=11; confidence=0.97 -->
**Table ($m=n\log_2 n$).** Columns: $n$, $d_{reg}$, [BFSY2005], LBKZ, LBLS, UBLS, UBL (BFSY column empty).

| $n$ | $d_{reg}$ | BFSY | LBKZ | LBLS | UBLS | UBL |
|---|---|---|---|---|---|---|
| 256 | 8 | - | 5 | 8 | 20 | 14 |
| 512 | 12 | - | 8 | 12 | 33 | 21 |
| 1024 | 19 | - | 14 | 19 | 57 | 31 |
| 2048 | 31 | - | 25 | 31 | 100 | 48 |
| 4096 | 53 | - | 45 | 53 | 181 | 78 |
| 8192 | 92 | - | 82 | 92 | 331 | 129 |
| 16384 | 164 | - | 152 | 164 | 610 | 220 |
| 32768 | 298 | - | 283 | 298 | 1134 | 382 |

<a id="pdf-f300deb505d8-p008-b012"></a>
<!-- pdf-source: page=8; block=12; confidence=0.98 -->
# Acknowledgements

Thanks to Max Gebhardt, Jernej Tonejc, and Andreas Wiemers for helpful discussions.

<a id="pdf-f300deb505d8-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.97 -->
Bibliography (ACM-Reference-Format style, `krawtchouk` database). No mathematical content.
