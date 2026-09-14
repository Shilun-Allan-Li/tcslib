<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: d59395db8359158c43964dec5232f4ca198d78b013f382980a9867f4fd9d47d9 -->

<a id="pdf-d59395db8359-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.80 -->
**Section 2. Rank.** A function g : X×Y → {0,1} is represented by an m×n matrix M (m = |X| rows, n = |Y| columns) with M_{i,j} = g(i,j); the alternative sign encoding (−1)^{g(i,j)} may be used. Inputs are unit column vectors e_i, e_j, and the parties compute e_i^T M e_j, letting linear-algebra tools apply to communication complexity. (Functions of k inputs are naturally k-tensors; "communication complexity of M" means that of its associated boolean function.)

<a id="pdf-d59395db8359-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.95 -->
**Basic Properties of Rank.** The rank of a matrix is the maximum size of a set of linearly independent rows; it has several equivalent interpretations.

<a id="pdf-d59395db8359-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.97 -->
**Fact 2.1.** For an m×n matrix M, rank(M) = r iff any (equivalently, each) of the following holds:
- r is the smallest number with M = AB, where A is m×r and B is r×n;
- r is the smallest number of rank-1 matrices summing to M;
- r is the largest number of linearly independent columns (or rows) of M.

<a id="pdf-d59395db8359-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.98 -->
**Fact 2.2.** If M' is a submatrix of M, then rank(M') ≤ rank(M).

<a id="pdf-d59395db8359-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.98 -->
**Fact 2.3.** |rank(A) − rank(B)| ≤ rank(A + B) ≤ rank(A) + rank(B).

<a id="pdf-d59395db8359-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.90 -->
For a boolean matrix M, define M' of the same dimensions by M'_{i,j} = (−1)^{M_{i,j}} (1 ↦ −1, 0 ↦ 1), so M' = J − 2M with J the all-1's matrix.

<a id="pdf-d59395db8359-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.97 -->
**Fact 2.4.** |rank(M') − rank(M)| ≤ rank(J) = 1.

<a id="pdf-d59395db8359-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.98 -->
**Fact 2.5.** rank(AB) ≤ min{rank(A), rank(B)}.

<a id="pdf-d59395db8359-p002-b005"></a>
<!-- pdf-source: page=2; block=5; confidence=0.96 -->
**Definition (tensor product).** For an m×n matrix M and an m'×n' matrix M', the tensor product T = M ⊗ M' is the (mm')×(nn') matrix with entries indexed by tuples (i,i'),(j,j') and T_{(i,i'),(j,j')} = M_{i,j} · M'_{i',j'}.

**Fact 2.6.** rank(M ⊗ M') = rank(M) · rank(M'). (Useful for lower bounds.)

<a id="pdf-d59395db8359-p002-b006"></a>
<!-- pdf-source: page=2; block=6; confidence=0.96 -->
**Lemma 2.7.** For a boolean matrix, its real rank equals its rational rank, and the real rank is always at least its rank over F_2. (Boolean entries may be viewed over the reals, rationals, or F_2, giving potentially three notions of rank.)

<a id="pdf-d59395db8359-p002-b007"></a>
<!-- pdf-source: page=2; block=7; confidence=0.90 -->
**Proof.** (Real = rational rank, via Gaussian elimination.) If the rational rank is r, apply a rational row transformation bringing M to reduced form: an r×r identity block in the first r pivot columns with arbitrary entries M_{i,r+1},…,M_{i,n} to the right and zero rows below. This does not change the real rank, and the form makes the rank exactly r. (Continued on next page.)

<a id="pdf-d59395db8359-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.92 -->
**Proof (continued).** If any set of rows is linearly dependent over the rationals, one can find an integer linear dependence among them, yielding a dependence over F_2. Hence the rank over F_2 is at most the rank over the reals.

<a id="pdf-d59395db8359-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.95 -->
Unless stated otherwise, rank means rank over the reals for the remainder of the book.

<a id="pdf-d59395db8359-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.97 -->
**Lemma 2.8.** A boolean matrix of rank r has at most 2^r distinct rows and at most 2^r distinct columns.

<a id="pdf-d59395db8359-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.95 -->
**Proof.** Since the rank over F_2 is at most r, every row is an F_2-linear combination of some r fixed rows. Only 2^r such combinations exist, so there are at most 2^r distinct rows (similarly for columns).

<a id="pdf-d59395db8359-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.90 -->
**Lower bounds using Rank.** Lemma 2.8 bounds communication via rank: a rank-r matrix has ≤ 2^r distinct rows, so Alice sends which of these her row is (r bits) and Bob replies with the function value.

<a id="pdf-d59395db8359-p003-b006"></a>
<!-- pdf-source: page=3; block=6; confidence=0.96 -->
**Theorem 2.9.** If a matrix has rank r, then its communication complexity is at most r + 1. (This is later improved to a bound closer to √r.)

<a id="pdf-d59395db8359-p003-b007"></a>
<!-- pdf-source: page=3; block=7; confidence=0.96 -->
**Lemma 2.10.** If a boolean matrix can be partitioned into 2^c monochromatic rectangles, then its rank is at most 2^c. (Holds even for matrices with +1, −1 entries.)

<a id="pdf-d59395db8359-p003-b008"></a>
<!-- pdf-source: page=3; block=8; confidence=0.93 -->
**Proof.** By Fact 2.1. For each rectangle R = A×B define the matrix with R_{i,j} = 1 if (i,j) ∈ R and 0 otherwise; each such R has rank 1. M is the sum of at most 2^c such matrices (those corresponding to 1-rectangles).

<a id="pdf-d59395db8359-p003-b009"></a>
<!-- pdf-source: page=3; block=9; confidence=0.94 -->
**Theorem 2.11.** If a matrix has rank r, then its communication complexity is at least log r. (Follows since low-communication functions yield monochromatic-rectangle partitions, Theorem 1.7, combined with Lemma 2.10.)

<a id="pdf-d59395db8359-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.90 -->
**Rank lower bound (Equality).** The equality function (def. (1.1)) has matrix equal to the identity. Its rows are linearly independent, so rank $= 2^n$, giving communication complexity $\geq n$ bits.

<a id="pdf-d59395db8359-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.80 -->
**Rank lower bound (Greater-than).** The greater-than function (def. (1.3)) has the upper-triangular matrix that is $1$ above the diagonal and $0$ elsewhere. Its rows are linearly independent, so the matrix has full rank; communication complexity $\geq \log n$.

<a id="pdf-d59395db8359-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.92 -->
**Rank lower bound (Disjointness).** Let $D_n$ be the boolean matrix for disjointness (def. (1.2)), with rows ordered lexicographically so that sets containing element $n$ come last. Partitioning rows and columns by whether the corresponding set contains $n$: when $n$ is in both, the block is $0$; when $n$ is in only rows or only columns, the block is a copy of $D_{n-1}$. Hence
$$D_n = \begin{bmatrix} D_{n-1} & D_{n-1} \\ D_{n-1} & 0 \end{bmatrix} = D_1 \otimes D_{n-1}.$$
By Fact 2.6, $\operatorname{rank}(D_n) = 2\operatorname{rank}(D_{n-1})$, so $\operatorname{rank}(D_n) = 2^n$; communication complexity of disjointness $\geq n$. (Attributed to Alexander Razborov, 1987.)

<a id="pdf-d59395db8359-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.80 -->
**Rank lower bound (k-disjointness).** Disjointness restricted to sets of size $\leq k$ gives matrix $D_{n,k}$ of dimensions $\left(\sum_{i=0}^{k}\binom{n}{i}\right) \times \left(\sum_{i=0}^{k}\binom{n}{i}\right)$. For sets $X,Y \subseteq [n]$ define the monomial $x = \prod_{i \in X} y_i$ and the string $y \in \{0,1\}^n$ with $y_i = 0$ iff $i \in Y$; then $\mathrm{Disj}(X,Y) = x(y)$. Any nonzero linear combination of rows corresponds to a nonzero polynomial $f$ in these monomials. Full rank requires exhibiting a set $Y$ (input $y$) with $f(y) \neq 0$. Take $X$ realizing a maximum-degree monomial of $f$; restrict all variables outside $X$ to $1$, making $f$ a nonzero polynomial in the variables of $X$. Since such polynomials biject with boolean functions on those variables, some setting exists giving...

<a id="pdf-d59395db8359-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.80 -->
**Proof (continued).** ...a setting of the variables of $X$ producing an assignment $y$ with $f(y) = 1$. This assignment has at most $k$ entries equal to $0$, so it corresponds to a valid restricted input, establishing full rank.

<a id="pdf-d59395db8359-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.85 -->
**Rank lower bound (Inner product).** Define $\mathrm{IP}: \{0,1\}^n \times \{0,1\}^n \to \{0,1\}$ by
$$\mathrm{IP}(x,y) = \langle x, y\rangle \bmod 2. \tag{2.1}$$
The trivial protocol uses $n$ bits, and largest-rectangle bounds give $\Omega(n)$. Using Fact 2.4: with $P_n$ the sign matrix (entries $(-1)^{\langle x,y\rangle}$) with rows/columns sorted lexicographically,
$$P_n = \begin{bmatrix} P_{n-1} & P_{n-1} \\ P_{n-1} & -P_{n-1} \end{bmatrix} = \begin{bmatrix} 1 & 1 \\ 1 & -1 \end{bmatrix} \otimes P_{n-1}.$$
By Fact 2.6, $\operatorname{rank}(P_n) = 2\operatorname{rank}(P_{n-1})$, so $\operatorname{rank}(P_n) = 2^n$; communication complexity of IP $\geq n$.

<a id="pdf-d59395db8359-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.90 -->
## Towards the Log-Rank Conjecture

Lovász and Saks conjectured that Theorem 2.11 is closer to the truth than Theorem 2.9.

<a id="pdf-d59395db8359-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.85 -->
**Conjecture 2.12.** There is a constant $\alpha$ such that the communication complexity of a matrix $M$ is at most $\log^{\alpha} \operatorname{rank}(M)$.

Kushilevitz (Nisan–Wigderson, 1995) showed $\alpha \geq \log_3 6$ is necessary, so communication complexity cannot equal rank exactly. (Conjecture: Lovász and Saks, 1988.)

<a id="pdf-d59395db8359-p005-b005"></a>
<!-- pdf-source: page=5; block=5; confidence=0.90 -->
**Theorem 2.13.** If a matrix has rank $r$, its communication complexity is at most $O(\sqrt{r}\,\log^2 r)$.

(Lovett, 2014, proves the stronger $O(\sqrt{r}\,\log r)$; the weaker bound is proved here. Proof relies on Rothvoß 2014 and John's theorem, John 1948.)

<a id="pdf-d59395db8359-p005-b006"></a>
<!-- pdf-source: page=5; block=6; confidence=0.85 -->
**Lemma 2.14.** Any $m \times n$ boolean matrix of rank $r > 1$ has a monochromatic rectangle of size at least $mn \cdot 2^{-20\sqrt{r}\log r}$.

To build a protocol, let $R$ be the rectangle from the lemma; rearranging rows and columns write the matrix as $\begin{bmatrix} R & A \\ B & C \end{bmatrix}$. It is then claimed that (continued next page)...

<a id="pdf-d59395db8359-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.85 -->
**Claim / Proof.** The rectangle rank bound is
$$\operatorname{rank}\!\begin{bmatrix} R \\ B \end{bmatrix} + \operatorname{rank}\!\begin{bmatrix} R & A \end{bmatrix} \leq \operatorname{rank}\!\begin{bmatrix} R & A \\ B & C \end{bmatrix} + 3.$$
Using the decompositions $\begin{bmatrix} R & A \\ B & C \end{bmatrix} = \begin{bmatrix} 0 & A \\ B & C \end{bmatrix} + \begin{bmatrix} R & 0 \\ 0 & 0 \end{bmatrix}$, $\begin{bmatrix} R & A \end{bmatrix} = \begin{bmatrix} 0 & A \end{bmatrix} + \begin{bmatrix} R & 0 \end{bmatrix}$, $\begin{bmatrix} R \\ B \end{bmatrix} = \begin{bmatrix} 0 \\ B \end{bmatrix} + \begin{bmatrix} R \\ 0 \end{bmatrix}$, Fact 2.3 gives
$$\operatorname{rank}\!\begin{bmatrix} R \\ B \end{bmatrix} + \operatorname{rank}\!\begin{bmatrix} R & A \end{bmatrix} \leq \operatorname{rank}(A)+\operatorname{rank}(B)+2 \leq \operatorname{rank}\!\begin{bmatrix} 0 & A \\ B & C \end{bmatrix}+2 \leq \operatorname{rank}\!\begin{bmatrix} R & A \\ B & C \end{bmatrix}+3. \tag{2.2}$$

<a id="pdf-d59395db8359-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.90 -->
**Proof (protocol).** Suppose $\begin{bmatrix} R \\ B \end{bmatrix}$ has the smaller rank. Bob sends $0$ if his input is consistent with $R$, else $1$. A consistent ($0$) step, while $\operatorname{rank}(M) > 9$, reduces rank by a factor of at least $2/3$ (using $(t+3)/2 \leq 2t/3$ for $t \geq 9$); an inconsistent ($1$) step reduces the matrix size by a factor $1 - 2^{-20\sqrt{r}\log r}$.

By Lemma 2.8 a rank-$r$ matrix has $\leq 2^r$ rows and columns. The number of $0$-transmissions is at most $2r \ln 2 \cdot 2^{20\sqrt{r}\log r}$: after that many, the number of entries drops below $1$ via $2^{2r}\bigl(1 - 2^{-20\sqrt{r}\log r}\bigr)^{2r\cdot 2^{20\sqrt{r}\log r}} < 2^{2r} e^{-2r \ln 2} = 1$ (using $1 - x \leq e^{-x}$). The number of $1$-transmissions is at most $O(\log_{3/2} r)$ (after which rank $< 6$). Hence the number of leaves is at most $\binom{2r \ln 2 \cdot 2^{20\sqrt{r}\log r}}{\log_{3/2} r} \leq 2^{O(\sqrt{r}\log^2 r)}$. By Theorem 1.3 the tree can be balanced to a protocol with communication $O(\sqrt{r}\log^2 r)$.

<a id="pdf-d59395db8359-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.80 -->
**Protocol (Figure 2.1, for low-rank matrices, $2^{O(\sqrt{r}\log^2 r)}$ leaves).** Input: Alice knows $i$, Bob knows $j$; Output: $M_{i,j}$.

- While $\operatorname{rank}(M) > 9$: find a monochromatic rectangle $R$ per Lemma 2.14; write $M = \begin{bmatrix} R & A \\ B & C \end{bmatrix}$.
  - If $\operatorname{rank}\begin{bmatrix} R \\ B \end{bmatrix} > \operatorname{rank}\begin{bmatrix} R & A \end{bmatrix}$: if $i$ is consistent with $R$, both replace $M$ with $\begin{bmatrix} R & A \end{bmatrix}$; else with $\begin{bmatrix} B & C \end{bmatrix}$.
  - Else: if $j$ is consistent with $R$, both replace $M$ with $\begin{bmatrix} R \\ B \end{bmatrix}$; else with $\begin{bmatrix} A \\ C \end{bmatrix}$.
- Finally the parties exchange at most $9$ bits to compute $M_{i,j}$ using Theorem 2.9.

<a id="pdf-d59395db8359-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.85 -->
**Definition (convex set).** It remains to prove Lemma 2.14 via John's theorem. A set $K \subseteq \mathbb{R}^r$ is *convex* if for all $x, y \in K$, every point on the segment from $x$ to $y$ also lies in $K$. (continued)

<a id="pdf-d59395db8359-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.95 -->
**Definition (symmetric set, ellipsoid).** A set $K$ is *symmetric* if $x\in K \Rightarrow -x\in K$. An ellipsoid centered at $0$ is $E=\{x\in\mathbb{R}^r : \sum_{i=1}^r \langle x,u_i\rangle^2/\alpha_i^2 \le 1\}$, where $u_1,\dots,u_r$ are a basis for $\mathbb{R}^r$.

<a id="pdf-d59395db8359-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.97 -->
**Theorem 2.15 (John's Theorem).** Let $K\subseteq\mathbb{R}^r$ be a symmetric convex body such that the unit ball is the most voluminous of all ellipsoids contained in $K$. Then every element of $K$ has length at most $\sqrt{r}$. (Attributed to John, 1948.)

<a id="pdf-d59395db8359-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.90 -->
Setup for scaling: if $E$ is the largest ellipsoid in $K$, multiply every element of $K$ by $e$ in the direction $u_i$, giving the convex body $K'=\{x' : \exists x\in K,\ \langle x',u_j\rangle = e\langle x,u_i\rangle \text{ if } j=i,\ \langle x,u_j\rangle \text{ otherwise}\}$. Scaling space by $\beta$ in a direction changes all volumes by the factor $\beta$, so the largest ellipsoid in $K'$ is the scaled largest ellipsoid of $K$.

<a id="pdf-d59395db8359-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.95 -->
**Fact 2.16.** The largest ellipsoid in $K'$ is $E'=\{x\in\mathbb{R}^r : \sum_{j=1}^r \langle x,u_j\rangle^2/\beta_j^2 \le 1\}$, where $\beta_j=\alpha_j$ for $j\ne i$ and $\beta_i = e\,\alpha_i$.

<a id="pdf-d59395db8359-p007-b005"></a>
<!-- pdf-source: page=7; block=5; confidence=0.93 -->
Lemma 2.14 is proved in two steps: (1) use John's theorem to show the matrix contains a large nearly monochromatic rectangle; (2) show any such low-rank rectangle contains a large monochromatic rectangle. Since $M$ has rank $r$, write $M=AB$ with $A$ an $m\times r$ matrix and $B$ an $r\times n$ matrix.

<a id="pdf-d59395db8359-p007-b006"></a>
<!-- pdf-source: page=7; block=6; confidence=0.95 -->
**Lemma 2.17.** Any boolean matrix $M$ of rank $r$ can be expressed as $M=AB$, where $A$ is an $m\times r$ matrix whose rows are vectors of length at most $\sqrt{r}$, and $B$ is an $r\times n$ matrix whose columns are vectors of length at most $1$. (The values $\sqrt{r}$ and $1$ may be replaced by any two numbers with product $\sqrt{r}$.)

<a id="pdf-d59395db8359-p007-b007"></a>
<!-- pdf-source: page=7; block=7; confidence=0.93 -->
**Proof.** Start with $M=AB$ where $A,B$ need not satisfy the length constraints. Let $v_1,\dots,v_m$ be the rows of $A$ and $w_1,\dots,w_n$ the columns of $B$. Let $K$ be the convex hull of $\{\pm v_1,\dots,\pm v_m\}$.

<a id="pdf-d59395db8359-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.90 -->
**Proof (continued).** Making the maximum-volume ellipsoid in $K$ the unit ball is equivalent to $\alpha_1=\cdots=\alpha_r=1$. If some $\alpha_i\ne 1$, scale every $v_j$ by $\alpha_i$ in direction $u_i$ and every $w_j$ by $1/\alpha_i$ in direction $u_i$; this preserves all pairwise inner products. Formally (footnote 10), writing $v_j=\sum_{i'} \gamma_{i'} u_{i'}$, $w_k=\sum_{i'}\beta_{i'}u_{i'}$, replace $\gamma_i$ by $\alpha_i\gamma_i$ and $\beta_i$ by $\beta_i/\alpha_i$, preserving $\langle v_j,w_k\rangle$. By Fact 2.16, repeating over all $i$ makes the unit ball the maximum-volume ellipsoid in $K$. Then John's theorem gives $\|v_i\|\le\sqrt{r}$ for every $i$.

<a id="pdf-d59395db8359-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.92 -->
**Proof (continued).** To show $\|w_i\|\le 1$ we use that $M$ is boolean. For $w_i$, let $e_i=w_i/\|w_i\|$; then $\|w_i\|=\langle w_i,e_i\rangle$. Since $e_i$ lies in the unit ball $\subseteq K$, write it as a convex combination $e_i=\sum_j \mu_j v_j + \sum_j \kappa_j(-v_j)$. Thus $\langle w_i,e_i\rangle = \sum_j \mu_j\langle w_i,v_j\rangle + \sum_j \kappa_j\langle w_i,-v_j\rangle \le \sum_j \mu_j + \sum_j \kappa_j = 1$, the inequality holding because $M$ is boolean. This completes the proof. $\square$

<a id="pdf-d59395db8359-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.94 -->
For the remainder assume $M$ has at least $mn/2$ zeros. Justification: if $M$ has more $1$'s than $0$'s, replace $M$ by $J-M$ ($J$ the all-ones matrix); this increases rank by at most $1$ and swaps the roles of $0$'s and $1$'s.

<a id="pdf-d59395db8359-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.92 -->
**Definition.** Set $\theta_{i,j}=\arccos\!\big(\langle v_i,w_j\rangle/(\|v_i\|\,\|w_j\|)\big)$. When $v_i,w_j$ are orthogonal the angle is $\pi/2$; when the inner product is $1$ the angle is at most $\arccos(1/\sqrt{r})\le \tfrac{\pi}{2}-\tfrac{2\pi}{7\sqrt{r}}$. Hence $\theta_{i,j} = \tfrac{\pi}{2}$ if $M_{i,j}=0$, and $\theta_{i,j} \le \tfrac{\pi}{2}-\tfrac{2\pi}{7\sqrt{r}}$ if $M_{i,j}=1$.

<a id="pdf-d59395db8359-p008-b005"></a>
<!-- pdf-source: page=8; block=5; confidence=0.93 -->
**Random experiment.** Sample $t$ length-1 vectors $z_1,\dots,z_t$ uniformly at random and define the rectangle $R=\{(i,j): \forall k,\ \langle v_i,z_k\rangle>0 \text{ and } \langle w_j,z_k\rangle<0\}$.

<a id="pdf-d59395db8359-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.92 -->
**Proof step.** For fixed $(i,j)$ and a single $k$, the probability that $\langle v_i,z_k\rangle>0$ and $\langle w_j,z_k\rangle<0$ equals $\tfrac14-\tfrac{\pi/2-\theta_{i,j}}{2\pi}$. By independence of the $z_k$, $\Pr_R[(i,j)\in R] = \big(\tfrac14-\tfrac{\pi/2-\theta_{i,j}}{2\pi}\big)^t$, which equals $(1/4)^t$ if $M_{i,j}=0$ and is $\le\big(\tfrac14-\tfrac{1}{7\sqrt{r}}\big)^t$ if $M_{i,j}=1$.

<a id="pdf-d59395db8359-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.83 -->
**Proof step.** Let $R_1$ be the number of $1$'s and $R_0$ the number of $0$'s in $R$. Set $t=7\sqrt{r}\log r$. Then $\mathbb{E}[R_0] \ge \tfrac{mn}{2}(1/4)^{t} = \tfrac{mn}{2}\,2^{-14\sqrt{r}\log r}$, and $\mathbb{E}[R_1] \le \tfrac{mn}{2}\big(\tfrac14-\tfrac{1}{7\sqrt{r}}\big)^{t} = \tfrac{mn}{2}\,2^{-14\sqrt{r}\log r}\big(1-\tfrac{4}{7\sqrt{r}}\big)^{7\sqrt{r}\log r} \le \tfrac{mn}{2}\,2^{-14\sqrt{r}\log r}\,r^{-4\log e}$, using $1-x\le e^{-x}$ for $x\ge 0$.

<a id="pdf-d59395db8359-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.95 -->
**Proof step.** Let $Q=R_0-r^4 R_1$. By linearity of expectation, $\mathbb{E}[Q] \ge \tfrac{mn}{2}\,2^{-14\sqrt{r}\log r}\,(1-1/r) \ge mn\cdot 2^{-16\sqrt{r}\log r}$, since $r>1$.

<a id="pdf-d59395db8359-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.80 -->
Figures: 2.2 illustrates $\arccos(\alpha)\le \tfrac{\pi}{2}-\tfrac{2\pi\alpha}{7}$ for $0\le\alpha\le 1$; 2.3 shows the region where all $z_k$ must fall to force $(i,j)\in R$ when $M_{i,j}=0$; 2.4 shows the analogous region when $M_{i,j}=1$.

<a id="pdf-d59395db8359-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.78 -->
**Proof (cont.).** Some rectangle $R$ realizes the value $Q$, and only a $1/r^3$ fraction of $R$ can consist of $1$-entries.

<a id="pdf-d59395db8359-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.90 -->
**Claim 2.18.** If at least half of the matrix is $0$'s, then there is a submatrix $T$ of size at least $mn\,2^{-16\sqrt{r\log r}}$ in which the fraction of $1$'s is at most $1/r^3$.

<a id="pdf-d59395db8359-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.90 -->
**Proof (conclusion of Lemma 2.14).** Call a row of $T$ *good* if it has at most a $2/r^3$ fraction of $1$'s; at least half the rows are good (else $T$ exceeds a $1/r^3$ fraction overall). Let $T'$ be $T$ restricted to good rows. Since $\operatorname{rank}(T')=r$, choose $r$ rows $A_1,\dots,A'_r$ spanning all rows of $T'$; each has $\le 2/r^3$ fraction $1$'s, so at most $2/r^2 \le 1/2$ of the columns contain a $1$ in these rows. Restrict $T'$ to the columns having no $0$ in $A_1,\dots,A_r$ to get $T''$; every row of $T''$ is a linear combination of all-$0$ rows, yielding a monochromatic submatrix of size at least $mn\,2^{-16\sqrt{r}\log r}/4 \ge mn\,2^{-18\sqrt{r}\log r}$. $\square$

<a id="pdf-d59395db8359-p010-b004"></a>
<!-- pdf-source: page=10; block=4; confidence=0.95 -->
**Open Problem 2.19.** Find a more direct geometric argument proving Lemma 2.14.

<a id="pdf-d59395db8359-p010-b005"></a>
<!-- pdf-source: page=10; block=5; confidence=0.98 -->
## Non-negative Rank and Covers

<a id="pdf-d59395db8359-p010-b006"></a>
<!-- pdf-source: page=10; block=6; confidence=0.90 -->
**Definition (non-negative rank).** The non-negative rank of an $m\times n$ matrix $M$ is the smallest $r$ with $M=AB$ where $A$ (size $m\times r$) and $B$ (size $r\times n$) have non-negative entries; equivalently, the least number of non-negative rank-$1$ matrices summing to $M$.

<a id="pdf-d59395db8359-p010-b007"></a>
<!-- pdf-source: page=10; block=7; confidence=0.95 -->
**Fact 2.20.** $\operatorname{rank}(M) \le \operatorname{rank}_+(M)$.

<a id="pdf-d59395db8359-p010-b008"></a>
<!-- pdf-source: page=10; block=8; confidence=0.90 -->
*Figure 2.5:* boolean matrix illustrating passage from a nearly monochromatic rectangle to a monochromatic one (regions $T$, $T'$, $A_1,\dots,A_{r'}$, $T''$).

<a id="pdf-d59395db8359-p010-b009"></a>
<!-- pdf-source: page=10; block=9; confidence=0.85 -->
**Example.** For $X=\{x_1,\dots,x_n\}$, the $n\times n$ matrix $M_{i,j}=(x_i-x_j)^2 = x_i^2 - 2x_ix_j + x_j^2$ is a sum of three rank-$1$ matrices, so $\operatorname{rank}(M)=3$, while $\operatorname{rank}_+(M)\ge \log n$.

<a id="pdf-d59395db8359-p010-b010"></a>
<!-- pdf-source: page=10; block=10; confidence=0.78 -->
**Proof (by induction on $n$).** If $\operatorname{rank}_+(M)=k$, write $M=R_1+\dots+R_k$ with non-negative rank-$1$ $R_i$. The support of $R_1$ is a rectangle $A\times B$ ($A,B\subseteq X$). Either $|A|\le |X|/2$ or $|B|\le |X|/2$; otherwise some $x\in A\cap B$ gives $M_{x,x}=0$, contradicting positivity of $R_1$ there. Taking $M'$ the submatrix on $X\setminus A$, we get $\operatorname{rank}_+(M')\le k-1$ and, by induction, $\ge \log(n/2)=\log n -1$, so $k\ge \log n$. $\square$

<a id="pdf-d59395db8359-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.90 -->
**Fact 2.21.** $M$ always has a $1$-cover with $\operatorname{rank}_+(M)$ rectangles. (If $M=R_1+\dots+R_r$ with non-negative rank-$1$ $R_i$, each support is a monochromatic value-$1$ rectangle.)

<a id="pdf-d59395db8359-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.92 -->
**Theorem 2.22.** If $M$ has a $1$-cover of size $r$, then there is a protocol computing $M$ with $O(\log r \cdot \log \operatorname{rank}(M))$ bits of communication.

<a id="pdf-d59395db8359-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.92 -->
**Proof.** As in Theorem 1.8, for each cover rectangle $R$ write $M=\begin{bmatrix}R&A\\B&C\end{bmatrix}$. By (2.2), either $\operatorname{rank}([R\ A]) \le (\operatorname{rank}(M)-3)/2$ (2.3) or $\operatorname{rank}\!\left(\begin{bmatrix}R\\B\end{bmatrix}\right) \le (\operatorname{rank}(M)-3)/2$ (2.4). At each step, Alice announces a name of an $R$ consistent with her input satisfying (2.3), or Bob announces one consistent with his input satisfying (2.4); both restrict to the corresponding submatrix, halving the rank. This lasts at most $O(\log \operatorname{rank}(M))$ steps until rank $1$. If neither finds such an $R$, no cover rectangle covers their input, so they safely output $1$. $\square$

<a id="pdf-d59395db8359-p011-b004"></a>
<!-- pdf-source: page=11; block=4; confidence=0.92 -->
**Corollary 2.23.** The communication complexity of $M$ is at most $O(\log(\operatorname{rank}_+ M)\cdot \log \operatorname{rank}(M)) \le O(\log^2 \operatorname{rank}_+(M))$.

<a id="pdf-d59395db8359-p011-b005"></a>
<!-- pdf-source: page=11; block=5; confidence=0.90 -->
**Exercise 2.1.** For $f:X\times Y\to\{0,1\}$ whose communication matrix $M_f$ has exactly $t$ ones in every row and column, cover the zeros of $M_f$ using $O(t(\log|X|+\log|Y|))$ monochromatic rectangles.

<a id="pdf-d59395db8359-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.90 -->
**Exercise 2.2.** Show the Nisan–Wigderson protocol (proof of Lemma 2.13) still works if Lemma 2.14 is weakened to guarantee only a rectangle of rank at most $r/8$ (instead of rank $\le 1$ / monochromatic).

<a id="pdf-d59395db8359-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.92 -->
**Exercise 2.3.** For a simple undirected graph $G$, $\chi(G)$ is the least number of colors to color vertices so adjacent ones differ. Show $\log \chi(G)$ is at most the deterministic communication complexity of $G$'s adjacency matrix.

<a id="pdf-d59395db8359-p012-b003"></a>
<!-- pdf-source: page=12; block=3; confidence=0.90 -->
**Exercise 2.4.** For any symmetric $M\in\{0,1\}^{n\times n}$ with all diagonal entries $1$, show $2^c \ge n^2/|M|$, where $c$ is the deterministic communication complexity of $M$ and $|M|$ is its number of ones.

<a id="pdf-d59395db8359-p012-b004"></a>
<!-- pdf-source: page=12; block=4; confidence=0.90 -->
**Exercise 2.5.** Define $\operatorname{rank}_2(M)$ as the rank of $M$ over $\mathbb{F}_2$. Exhibit an explicit family $M\in\{0,1\}^{n\times n}$ with $c \ge \operatorname{rank}_2(M)/10$ ($c$ = deterministic communication complexity), and conclude this falsifies the log-rank conjecture analogue for $\operatorname{rank}_2$.

<a id="pdf-d59395db8359-p012-b005"></a>
<!-- pdf-source: page=12; block=5; confidence=0.92 -->
**Exercise 2.6.** Show that if $f$ has a fooling set of size $s$, then $\operatorname{rk}(M_f) \ge \sqrt{s}$. Hint: tensor product.
