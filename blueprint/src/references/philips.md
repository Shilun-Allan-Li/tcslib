<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: 24e94ad30862bd5bfdcf7bc92b779a2cf08729fe673e43ecda7378fe593c36f6 -->

<a id="pdf-24e94ad30862-p018-b001"></a>
<!-- pdf-source: page=18; block=1; confidence=0.82 -->
Defines the inner-distribution component $a_i=|Y|^{-1}\phi_Y^{T}D_i\phi_Y$ (3.3) and the matrix $B=[D_0\phi_Y,\;D_1\phi_Y,\;\dots,\;D_n\phi_Y]$ (3.4). Consequently $a=|Y|^{-1}\phi_Y^{T}B$. The following three results relate $a$ and $B$ for association schemes.

<a id="pdf-24e94ad30862-p018-b002"></a>
<!-- pdf-source: page=18; block=2; confidence=0.70 -->
**Theorem 3.1.** Let $(X,R)$ be an association scheme and let $Y\subseteq X$. Then the inner and outer distributions of $Y$ with respect to $R$ satisfy
$$B^{T}B=|X|^{-1}|Y|\,\bar P\,\Delta_{aQ}\,P\quad(3.5)$$
where $P,Q$ are the eigenmatrices of the scheme and $\Delta$ is the diagonal-matrix operator defined in (2.20).

<a id="pdf-24e94ad30862-p018-b003"></a>
<!-- pdf-source: page=18; block=3; confidence=0.85 -->
**Proof.** For $i,j\in N$, compute the $(i,j)$-entry of $B^{T}B$ from (3.4). Using (2.5) and (3.3), for $R_i=R_i^{-1}$ one obtains $(B^{T}B)(i,j)=\phi_Y^{T}D_i^{T}D_j\phi_Y=|Y|\sum_k p_{i,j}^{(k)}a_k$ (3.6). Defining $b=aQ$, we have $|X|a=bP$ by (2.15). Hence, according to (2.19), $(B^{T}B)(i,j)=|X|^{-1}|Y|\sum_u b_u P_i(u)P_j(u)$. Since $P_i(u)=P_i^{*}(u)$ for $R_i=R_i^{-1}$, this is exactly (3.5).

<a id="pdf-24e94ad30862-p018-b004"></a>
<!-- pdf-source: page=18; block=4; confidence=0.90 -->
**Corollary 3.2.** The rank of $B$ equals the number of nonzero components of $aQ$.

<a id="pdf-24e94ad30862-p018-b005"></a>
<!-- pdf-source: page=18; block=5; confidence=0.85 -->
**Proof.** $P$ is nonsingular, so by (3.5) $\operatorname{rank}(B)=\operatorname{rank}(B^{T}B)=\operatorname{rank}(\Delta_{aQ})$, from which the claim follows.

<a id="pdf-24e94ad30862-p018-b006"></a>
<!-- pdf-source: page=18; block=6; confidence=0.90 -->
**Theorem 3.3.** The components $(aQ)_k$ of the row vector $aQ$ are nonnegative real numbers. Moreover, for a given $k$, $(aQ)_k=0$ if and only if $BQ_k$ is the zero vector.

<a id="pdf-24e94ad30862-p018-b007"></a>
<!-- pdf-source: page=18; block=7; confidence=0.80 -->
**Proof.** Multiply (3.5) on the left by $Q$ and the right by $Q$: by (2.15), $QB^{T}BQ=|X||Y|\,\Delta_{aQ}$. Equating corresponding diagonal entries gives
$$\|BQ_k\|^2=|X||Y|\,(aQ)_k,\quad\forall k\in N,\quad(3.7)$$
with $\|\cdot\|$ the Hermitian norm, which yields both conclusions.

<a id="pdf-24e94ad30862-p018-b008"></a>
<!-- pdf-source: page=18; block=8; confidence=0.20 -->
**Remark.** The inequalities $(aQ)_k\ge0$ can be derived more directly: from (2.9) and (2.16), $(aQ)_k=|X||Y|^{-1}\phi_Y^{T}(\dots)$ for an orthogonal matrix $S$ diagonalizing a certain matrix, which forces $(aQ)_k\ge0$; and for a given $k$ four conditions ($aQ_k=0$, $BQ_k=0$, …) are equivalent. [Source text truncated.]

<a id="pdf-24e94ad30862-p018-b009"></a>
<!-- pdf-source: page=18; block=9; confidence=0.75 -->
**3.2 Linear programming.** The conditions $(aQ)_k\ge0$ motivate a linear-programming study of subsets $Y\subseteq X$; standard LP duality is recalled (cf. Simonnard) with adapted notation.

<a id="pdf-24e94ad30862-p018-b010"></a>
<!-- pdf-source: page=18; block=10; confidence=0.25 -->
**Definition (primal $(A,M)$).** For a matrix $A\in\mathbb{R}(N,N)$ with $A_0(\cdot)$ normalized and $M\subseteq N$, the LP $(A,M)$ has variables $b_i$ ($i\in M^{*}$) and $n$ inequalities of the form $\sum_{i\in M} b_i A_k(i)\ (3.9)$, together with $b_i\ge0\ (3.10)$, maximizing $g\ (3.11)$. An $(n+1)$-tuple $b=(b_0,\dots,b_n)$ is a *program* if it satisfies (3.9),(3.10) with $b_0=1$; $(1,0,\dots,0)$ is a program with $g=1$. A *maximal* program maximizes $g$; $g(A,M)$ denotes that maximum, and $g(A,M)\ge1$.

<a id="pdf-24e94ad30862-p019-b001"></a>
<!-- pdf-source: page=19; block=1; confidence=0.60 -->
**Definition (dual $(A,M)'$).** Variables $\beta_k$ ($k\in N^{*}$), $m$ inequalities $\sum_k\beta_k A_k(i)\le0$, $i\in M^{*}$ (3.12); $\beta_k\ge0$, $k\in N^{*}$ (3.13); minimize $y=\sum_k\beta_k A_k(0)$ (3.14). An $(n+1)$-tuple $\beta=(\beta_0,\dots,\beta_n)$ is a *program* if it satisfies (3.12),(3.13) with $\beta_0=1$; it is *minimal* if it minimizes $y$.

<a id="pdf-24e94ad30862-p019-b002"></a>
<!-- pdf-source: page=19; block=2; confidence=0.90 -->
**Theorem 3.4.** For a bounded set of programs: (i) $(A,M)$ and $(A,M)'$ each admit an extremal program (maximal, resp. minimal); every pair $b$ of $(A,M)$ and $\beta$ of $(A,M)'$ satisfies $g\le\gamma$, and the extremal values of $g$ and $\gamma$ are equal. (ii) For each pair of extremal programs $(b,\beta)$ the following two sets of equations hold:
$$\beta_k\Big(\sum_{i\in M} b_i A_k(i)\Big)=0,\ \forall k\in N^{*}\ (3.15);\qquad b_i\Big(\sum_{k\in N}\beta_k A_k(i)\Big)=0,\ \forall i\in M^{*}\ (3.16).$$
Conversely, any pair of programs satisfying (3.15) and (3.16) is a pair of extremal programs.

<a id="pdf-24e94ad30862-p019-b003"></a>
<!-- pdf-source: page=19; block=3; confidence=0.80 -->
Two results follow for $(P,M)$ and $(Q,M)$ when $A$ is an eigenmatrix $P$ or $Q$ of a symmetric $n$-class association scheme.

<a id="pdf-24e94ad30862-p019-b004"></a>
<!-- pdf-source: page=19; block=4; confidence=0.55 -->
**Lemma 3.5.** The set of programs of $(P,M)$ is bounded by $b_i\le\mu_i$, and that of $(Q,M)$ by $b_i\le v_i$, for all $i\in M$.

**Proof.** (Second part.) From (2.15) one obtains, for an arbitrary $(n+1)$-tuple $b$, the identity $\sum_k(v_i-P_i(k))\sum_j b_j Q_k(j)=|X|(b_0 v_i-b_i)$. By (2.29) and (3.9) the left-hand member is $\ge0$ when $b$ is a program of $(Q,M)$; hence, with $b_0=1$, $b_i\le v_i$.

<a id="pdf-24e94ad30862-p019-b005"></a>
<!-- pdf-source: page=19; block=5; confidence=0.25 -->
**Lemma 3.6.** Each minimal program $\beta$ of $(P,M)'$ satisfies $\beta_j\le1$ for all $j\in N$; and $\beta_j=1$ for a given $j$ iff a stated relation ($\mu_j\propto\sum_i b_i P_j(i)$) holds for every maximal program of $(P,M)$. The same statement holds with $Q$ in place of $P$.

**Proof.** For extremal $b,\beta$, (3.14),(3.16),(2.19) give $y=\sum(\dots)$; since $\sum b_i=g=y$, one obtains $\sum_j(1-\beta_j)(\dots)=y$, and each summand being nonnegative yields the result. The $(Q,M)'$ case is analogous, based on the preceding lemma.

<a id="pdf-24e94ad30862-p019-b006"></a>
<!-- pdf-source: page=19; block=6; confidence=0.50 -->
**3.3 Cliques in association schemes.** For a family of relations $R=\{R_i\mid i\in N\}$ (of type $A2$, sec. 2.1) and $M\subseteq N$, a subset $Y\subseteq X$ is an *$M$-clique* with respect to $R$ if $R_i\cap Y^2=\varnothing$ for $i\notin M$ (equivalently, any two points of $Y$ are $R_i$-related only for $i\in M$). The main problem is the maximum number of points in $M$-cliques.

<a id="pdf-24e94ad30862-p019-b007"></a>
<!-- pdf-source: page=19; block=7; confidence=0.75 -->
**3.3.1 The Elias theorem.** Here the relations $R_i$ need not form a scheme; information about cliques $Y\subseteq X$ is obtained from restrictions to subsets of $X$, adapting Elias's bound in coding theory (cf. Berlekamp).

<a id="pdf-24e94ad30862-p020-b001"></a>
<!-- pdf-source: page=20; block=1; confidence=0.85 -->
**Definition (crown).** For nonempty $L\subseteq N$ and $e\in X$, set $C_L(e)=\bigcup_{i\in L}\{z\in X\mid(e,z)\in R_i\}$. Its cardinality is independent of $e$: with $v_i$ the valence of $R_i$,
$$|C_L(e)|=\sum_{i\in L} v_i.\quad(3.18)$$

<a id="pdf-24e94ad30862-p020-b002"></a>
<!-- pdf-source: page=20; block=2; confidence=0.88 -->
**Theorem 3.7.** Let $L,M\subseteq N$ with $0\in M$. If $Y$ is an $M$-clique w.r.t. $R$, then there exist a crown $X'=C_L(e)$ and an $M$-clique $Y'\subseteq X'$ satisfying $|X|^{-1}|Y|\le|X'|^{-1}|Y'|$.

<a id="pdf-24e94ad30862-p020-b003"></a>
<!-- pdf-source: page=20; block=3; confidence=0.85 -->
**Proof.** First, for any $Y\subseteq X$: $\sum_{x\in X}|Y\cap C_L(x)|=|Y|\sum_{i\in L}v_i$ (3.19); the LHS counts pairs $(x,y)$ with $y\in C_L(x)$, and by symmetry of $R_i$, $y\in C_L(x)\Leftrightarrow x\in C_L(y)$, so it equals $\sum_{y\in Y}|C_L(y)|$, which by (3.18) is the RHS. Then $|X|\max_x|Y\cap C_L(x)|\ge|Y|\sum_{i\in L}v_i$ (3.20). Choosing $e$ maximizing $|Y\cap C_L(e)|$ and setting $X'=C_L(e)$, $Y'=Y\cap X'$, (3.20) becomes $|X||Y'|\ge|Y||X'|$. Since $Y'$ is an $M$-clique whenever $Y$ is, the theorem follows.

<a id="pdf-24e94ad30862-p020-b004"></a>
<!-- pdf-source: page=20; block=4; confidence=0.80 -->
**Example.** In the Hamming scheme $H(n,2)=(F^n,R)$, $|F|=2$: for $1\le n'\le n/2$ and $L=\{n'\}$, the crown $C_L(e)$ is the sphere of centre $e$ and radius $n'$ in Hamming metric. Its nonempty restricted relations are $R_i'=\{(x',y')\in(X')^2\mid d_H(x',y')=i\}$, $i=0,1,\dots,n'$, and $(X',\{R_i'\})$ is an $n'$-class association scheme, independent of $e$ up to isomorphism — the Johnson scheme $J(n',n)$ (sec. 4.2). This illustrates how Theorem 3.7 transfers clique upper bounds to the Hamming setting.

<a id="pdf-24e94ad30862-p020-b005"></a>
<!-- pdf-source: page=20; block=5; confidence=0.75 -->
**3.3.2 The linear-programming bound.** By (3.1) and (3.17), an $M$-clique is characterized through its inner distribution $a$ by $a_i=0$ for $i\notin M$ (3.21). Henceforth assuming $(X,R)$ to be an association scheme, theorem 3.3 yields a strong necessary condition for $Y$ to be an $M$-clique.

<a id="pdf-24e94ad30862-p020-b006"></a>
<!-- pdf-source: page=20; block=6; confidence=0.78 -->
**Theorem 3.8.** Let $Q$ be the second eigenmatrix of the scheme. Then the inner distribution of an $M$-clique $Y$ is a program of $(Q,M)$ with $g=|Y|$.

**Proof.** Immediate from $(aQ)_k\ge0$ (Theorem 3.3) and the conditions $a_0=1$, $a_i=0$ ($i\notin M$) satisfied by the inner distribution $a$.

By Lemma 3.5 the programs of $(Q,M)$ are bounded, so $g(Q,M)$ is well defined and
$$|Y|\le g(Q,M)\quad(3.22)$$
for every $M$-clique $Y$ — the *linear-programming bound* for cliques.

<a id="pdf-24e94ad30862-p020-b007"></a>
<!-- pdf-source: page=20; block=7; confidence=0.20 -->
**Example.** Applying (3.22) to strongly regular graphs (sec. 2.4, $n=2$): a clique (complete subgraph) is an $M$-clique w.r.t. $R=\{R_0,R_1,\dots\}$; using (2.30) the bound reads $|Y|\le 1+(\dots)$. Verifying Theorem 3.4, the stated $b$ and $\beta=(1,0,-v_1/s,\dots)$ are programs satisfying (3.15),(3.16) with $A=Q$, giving extremal value $g=y=1-v_1/s$. [Text continues.]

<a id="pdf-24e94ad30862-p021-b001"></a>
<!-- pdf-source: page=21; block=1; confidence=0.90 -->
**Theorem 3.9.** Let $M\subseteq N$ with $0\in M$, and let $\bar M=N-M^{*}$. If $Y$ is an $M$-clique and $Z$ an $\bar M$-clique in an association scheme, then $|Y|\,|Z|\le|X|$.

<a id="pdf-24e94ad30862-p021-b002"></a>
<!-- pdf-source: page=21; block=2; confidence=0.72 -->
**Proof.** Let $b,c$ be the inner distributions of $Y,Z$. From eigenmatrix $Q$ and multiplicities $\mu_k$ define $\beta_k = (|Z|\,\mu_k)^{-1}\sum_i c_i Q_k(i)$ (3.24). The $\beta_k \ge 0$ with $\beta_0 = 1$. By (2.22), $\sum_k \beta_k Q_k(i) = |Z|\,|X|\,v_i^{-1} c_i$ (3.25), where $v_i$ is the valence of $R_i$. Since $Z$ is an $\bar M$-clique, $c_i = 0$ for $i \in M^{*}$, so $\beta$ is a program of $(Q,M)'$ satisfying (3.12) with equality. By Theorem 3.8, $b$ is a program of $(Q,M)$ with $g = |Y|$. The inequality $g \le \gamma$ then gives $|Y| \le \sum_k \beta_k Q_k(0) = |Z|^{-1}|X|$ (3.26), using (3.25) at $i=0$. $\square$

<a id="pdf-24e94ad30862-p021-b003"></a>
<!-- pdf-source: page=21; block=3; confidence=0.68 -->
Classical coding bounds (e.g. the Hamming bound) follow from Theorem 3.9. The linear-programming method also gives necessary conditions on $b,c$ for pairs $(Y,Z)$ attaining equality in (3.26): equality holds iff $(b,\beta)$ is a pair of extremal programs, whence Theorem 3.4(ii) with $\Lambda = Q$ yields $\big(\sum_k b_k Q_k\big)\big(\sum_i c_i Q_i\big) = 0$ for $k=1,\dots,n$. These conditions relate to the Lloyd theorem on perfect codes.

<a id="pdf-24e94ad30862-p021-b004"></a>
<!-- pdf-source: page=21; block=4; confidence=0.95 -->
## 3.4. Designs in association schemes

<a id="pdf-24e94ad30862-p021-b005"></a>
<!-- pdf-source: page=21; block=5; confidence=0.82 -->
**Definition ($T$-design).** For a symmetric association scheme $(X,R)$ with $n$ classes and $T \subseteq N^{*} = \{1,2,\dots,n\}$, a nonempty $Y \subseteq X$ is a $T$-design w.r.t. $R$ if its inner distribution $a$ satisfies $\sum_i a_i Q_k(i) = 0$ for all $k \in T$ (3.27), where $Q$ is the second eigenmatrix of the scheme.

<a id="pdf-24e94ad30862-p021-b006"></a>
<!-- pdf-source: page=21; block=6; confidence=0.60 -->
No general combinatorial interpretation of $T$-designs is given, but in the Hamming and Johnson schemes they coincide with classical designs. There is a formal duality between the clique notion (3.21) and the design notion (3.27).

<a id="pdf-24e94ad30862-p021-b007"></a>
<!-- pdf-source: page=21; block=7; confidence=0.70 -->
**Theorem 3.10.** Let $J_0, J_1, \dots, J_n$ be the minimal (primitive) idempotents of the Bose–Mesner algebra of $(X,R)$. Then a subset $Y$ is a $T$-design iff $J_k\, a_Y = 0$ for each $k \in T$ (where $a_Y$ is the characteristic vector of $Y$).

<a id="pdf-24e94ad30862-p021-b008"></a>
<!-- pdf-source: page=21; block=8; confidence=0.72 -->
**Proof.** By (3.8) the defining equations of a $T$-design are $aQ_k = 0$, which is equivalent to $J_k a_Y = 0$ since $J_k$ is positive semidefinite. $\square$

<a id="pdf-24e94ad30862-p021-b009"></a>
<!-- pdf-source: page=21; block=9; confidence=0.55 -->
The condition $a_Y^{T} J_k a_Y = 0$ ($\forall k \in T$) is compared with the earlier definition; by analogy with sec. 3.2.2 the LP method is applied to obtain a lower bound on $|Y|$.

<a id="pdf-24e94ad30862-p021-b010"></a>
<!-- pdf-source: page=21; block=10; confidence=0.20 -->
**Theorem 3.11.** Let $Y$ be a $T$-design in an association scheme with eigenmatrices $P,Q$ and inner distribution $a$. Then $b = |Y|\,|X|^{-1}\, aQ$ (3.28) is a program of $(P, N-T)$ with $g = |Y|$. [The exact form of $b$ in (3.28) is OCR-truncated.]

<a id="pdf-24e94ad30862-p021-b011"></a>
<!-- pdf-source: page=21; block=11; confidence=0.68 -->
**Proof.** From (2.15) and (3.28), $bP_k \ge 0$ for all $k$; the components of $b$ are nonnegative by Theorem 3.3. Hence $b$ is a program of $(P, N-T)$, and for this program $g = |Y|$. $\square$

<a id="pdf-24e94ad30862-p021-b012"></a>
<!-- pdf-source: page=21; block=12; confidence=0.72 -->
By Lemma 3.5 the maximal value $g(P,M)$ is well defined, giving the LP bound for designs: $|Y| \ge |X| / g(P, N-T)$ (3.29). An Example is then begun (continued on p.22).

<a id="pdf-24e94ad30862-p022-b001"></a>
<!-- pdf-source: page=22; block=1; confidence=0.75 -->
**Example (cont.).** For the regular graph $(X,R_1)$: a bipartition $\{Y,Z\}$ of $X$ with $(Y, R_1\cap Y^2)$ and $(Z, R_1\cap Z^2)$ regular subgraphs and $\operatorname{val}(R_1\cap Y^2) + \operatorname{val}(R_1\cap Z^2) > \operatorname{val}(R_1)$ is a *regular bipartition*. For $T=\{2\}$ in the scheme $R=\{R_0,R_1,R_2\}$, a subset $Y \ne X$ is a $T$-design iff $\{Y, X-Y\}$ is a regular bipartition of $X$.

<a id="pdf-24e94ad30862-p022-b002"></a>
<!-- pdf-source: page=22; block=2; confidence=0.60 -->
Using (2.30) we obtain the maximal value of $g$ for the problem $(P,M)$ with $M=\{0,1\}$: $g(P,M)=1-v_2/r_2$. Using the identity $(v_1-s_1)(v_2-r_2)=v\,s_1\,r_2$, (3.29) can be written as $|Y|\ge 1+v_1/(-s_1)$ (3.30). The unique maximal program $b$ of $(P,M)$ satisfies $bP_2=0$; hence, if a regular bipartition $\{Y,X-Y\}$ achieves (3.30), the inner distribution of $Y$ is $a=(1,-v_1/s_1,0)$, i.e. $Y$ is a clique in $(X,R_1)$ attaining the linear-programming bound (3.23).

<a id="pdf-24e94ad30862-p022-b003"></a>
<!-- pdf-source: page=22; block=3; confidence=0.74 -->
**Remark (generalized $T$-designs).** For a nonzero $\phi \in \mathbb{R}(X)$ with integral nonnegative components $\phi(x)$, define its distribution $a=(a_0,\dots,a_n)$ by $a_k = (\phi^{T}\phi)^{-1}(\phi^{T} D_k \phi)$ (3.31), $D_k$ = adjacency matrix of $R_k$. When each $\phi(x)\in\{0,1\}$ this is the inner distribution (3.3) of the $Y$ with $\phi_Y = \phi$; for any $\phi$ the numbers $aQ_k$ are nonnegative. Given $T \subseteq N^{*}$, $\phi$ is a $T$-design if $a$ satisfies (3.27); it is *simple* (no repeated points) when $\phi = \phi_Y$. Interpreting $\phi(x)$ as the multiplicity of $x$, the total point count is $h = \sum_x \phi(x)$.

<a id="pdf-24e94ad30862-p022-b004"></a>
<!-- pdf-source: page=22; block=4; confidence=0.62 -->
As in Theorem 3.11, $b = h^{-2}(\phi^{T}\phi)\, aQ$ is a program of $(P, N-T)$ with $g = h^{-1}(\phi^{T}\phi)|X|$. Hence bound (3.29) holds in general with $|Y|$ replaced by $h$: $\; h = h^{-1}(\phi^{T}\phi) \ge |X|/g(P, N-T)$.

<a id="pdf-24e94ad30862-p022-b005"></a>
<!-- pdf-source: page=22; block=5; confidence=0.95 -->
## 3.5. Characteristic matrices

<a id="pdf-24e94ad30862-p022-b006"></a>
<!-- pdf-source: page=22; block=6; confidence=0.55 -->
For $(X,R)$ with an orthogonal matrix diagonalizing the Bose–Mesner algebra, and with the classes of a partition $(X',S)$, for a subset $Y \subseteq X$ denote by $H_k$ the characteristic matrices (submatrices indexed over $X \times X'$); $H_0$ is all-ones. These are used later for $T$-designs (sec. 5.3). An equivalent formulation of Theorem 3.10 follows.

<a id="pdf-24e94ad30862-p022-b007"></a>
<!-- pdf-source: page=22; block=7; confidence=0.58 -->
**Theorem 3.12.** Let $H_0, H_1, \dots, H_n$ be the characteristic matrices of $Y$ for a symmetric association scheme. Then $Y$ is a $T$-design w.r.t. $R$ iff $H_k^{T} H_0 = 0$ for each $k \in T$. [Exact RHS OCR-uncertain.]

<a id="pdf-24e94ad30862-p022-b008"></a>
<!-- pdf-source: page=22; block=8; confidence=0.60 -->
Notation: $D_i \mid Y$ denotes the restriction of the adjacency matrix $D_i$ to $Y^2$ (cf. ch. 1). Formulas relating the $H_k$ to the $D_i \mid Y$ are derived next.

<a id="pdf-24e94ad30862-p022-b009"></a>
<!-- pdf-source: page=22; block=9; confidence=0.20 -->
**Theorem 3.13.** The characteristic matrices $H_k$ and the restricted adjacency matrices $D_i \mid Y$ satisfy a relation of the form $H_k \Lambda_i = (\dots)$ (3.33). [Precise form OCR-corrupted.]

<a id="pdf-24e94ad30862-p022-b010"></a>
<!-- pdf-source: page=22; block=10; confidence=0.45 -->
**Proof.** Immediate from the eigenmatrix $Q$, since by (2.9) $H_k H_k^{T}$ is the corresponding primitive idempotent. $\square$

<a id="pdf-24e94ad30862-p022-b011"></a>
<!-- pdf-source: page=22; block=11; confidence=0.20 -->
**Lemma 3.14.** Let $a$ be the inner distribution of $Y$. The characteristic matrices of $Y$ satisfy $\lVert D_i H_k \rVert^2 = |Y| \sum (\dots)$ (formula OCR-corrupted).

<a id="pdf-24e94ad30862-p022-b012"></a>
<!-- pdf-source: page=22; block=12; confidence=0.50 -->
**Proof.** Substitute $\phi_Y$ for $\phi$ in (3.31) and use (3.8) and the restriction of $S_k$ to $Y \times X'$ to obtain the result. $\square$

<a id="pdf-24e94ad30862-p022-b013"></a>
<!-- pdf-source: page=22; block=13; confidence=0.70 -->
**Theorem 3.15.** For given integers $i,t$, the inner distribution satisfies $q_{i,t}^{(k)}(aQ_k)=0$ for $k=1,2,\dots,n$ if and only if a condition (3.34) holds (stated on p.23).

<a id="pdf-24e94ad30862-p023-b001"></a>
<!-- pdf-source: page=23; block=1; confidence=0.60 -->
**Theorem 3.15 (cont.).** The condition (3.34) holds, for $Q_j=Q_j^{*}$:
$$\bar H_i H_j=\begin{cases}0 & \text{if } i\ne j,\\ |Y|\,I & \text{if } i=j.\end{cases}\quad(3.34)$$
Conversely, (3.34) implies $q_{i,t}^{(k)}(aQ_k)=0$ for $Q_t=Q_j^{*}$ and all $k\ge1$.

<a id="pdf-24e94ad30862-p023-b002"></a>
<!-- pdf-source: page=23; block=2; confidence=0.50 -->
**Proof.** Assuming $q_{ij}^{(t)}(aQ_k) = 0$ for $k = 1,\dots,n$, rewrite (3.33) using (2.27) to get (3.34) for $i \ne j$. For $i = j$: by Theorem 3.13, $\operatorname{tr}(H_k^{T} H_k) = \operatorname{tr}(H_k \Lambda_k) = a_k |Y|$, which with (3.35) gives $\lVert \Lambda_k H_k - |Y|\, Z \rVert = 0$. Conversely, every term of the sum (3.33) is a nonnegative real (Lemma 2.4, Theorem 3.3); condition (3.34) forces the sum to reduce to its $k=0$ term $|Y|\,a_k \delta_{k0}$, so all $k \ge 1$ terms vanish. $\square$

<a id="pdf-24e94ad30862-p023-b003"></a>
<!-- pdf-source: page=23; block=3; confidence=0.65 -->
To conclude the section it is indicated, without proof, that the distribution matrix $B$ (sec. 3.1) can be expressed in terms of $S$, $P$ and the $H_k$ by
$$B=|X|^{-1}S\,(\bar H_0 H_0\oplus\bar H_1 H_0\oplus\dots\oplus\bar H_n H_0)\,P,$$
where $\oplus$ denotes the direct sum. Together with (3.8) this could be used to give another proof of theorem 3.1.

<a id="pdf-24e94ad30862-p023-b004"></a>
<!-- pdf-source: page=23; block=4; confidence=0.15 -->
# 4. An introduction to [the Hamming and Johnson schemes]

<a id="pdf-24e94ad30862-p023-b005"></a>
<!-- pdf-source: page=23; block=5; confidence=0.60 -->
This chapter studies spaces carrying an association-scheme structure — the Hamming and Johnson schemes — as natural frameworks for combinatorial questions.

<a id="pdf-24e94ad30862-p023-b006"></a>
<!-- pdf-source: page=23; block=6; confidence=0.95 -->
## 4.1. The Hamming schemes

<a id="pdf-24e94ad30862-p023-b007"></a>
<!-- pdf-source: page=23; block=7; confidence=0.80 -->
**Definition (Hamming scheme).** Let $F$ be a finite set with $|F| = q$ and $X = F^n$. For $x = (x_1,\dots,x_n)$, $y = (y_1,\dots,y_n)$ the Hamming distance is $d_H(x,y) = |\{i : 1 \le i \le n,\ x_i \ne y_i\}|$ (4.1), i.e. the number of coordinates in which they differ. Define relations $R_l = \{(x,y) \in X^2 : d_H(x,y) = l\}$ (4.2). Then $R = \{R_0, R_1, \dots, R_n\}$ is an association scheme, the Hamming scheme $H(n,q)$.

<a id="pdf-24e94ad30862-p023-b008"></a>
<!-- pdf-source: page=23; block=8; confidence=0.90 -->
### 4.1.1. Eigenmatrices and Krawtchouk polynomials

<a id="pdf-24e94ad30862-p023-b009"></a>
<!-- pdf-source: page=23; block=9; confidence=0.62 -->
Give $F$ the structure of an abelian group (additive notation, identity $0$). The Hamming weight $w_H(x)$ of $x \in X = F^n$ is its number of nonzero coordinates, so (4.1) becomes $d_H(x,y) = w_H(x - y)$ (4.3). The relations (4.2) are translation-invariant and satisfy (2.43); the characters of $X$ diagonalize the Bose–Mesner algebra. To obtain the eigenmatrices, let $(\alpha,\beta) \mapsto \langle \alpha,\beta \rangle$ be an inner product / pairing $F^2 \to \mathbb{C}$ such that, as $\alpha$ varies, $\beta \mapsto \langle \alpha,\beta \rangle$ runs through the character group.

<a id="pdf-24e94ad30862-p024-b001"></a>
<!-- pdf-source: page=24; block=1; confidence=0.90 -->
**Definition (natural product).** Continuation referencing sec. 6.1 / theorem 6.2. States the identity (4.4):
$$\sum_{\beta\in F}\langle\alpha,\beta\rangle=\begin{cases}q-1 & \text{for } \alpha=0,\\ -1 & \text{for } \alpha\in F^{*}=F-\{0\}.\end{cases}\quad(4.4)$$
The component inner product $\langle x_i,y_i\rangle$ on $F$ is extended to the group $X=F^{n}$ by, for $x=(x_1,\dots,x_n)$ and $y=(y_1,\dots,y_n)$,
$$\langle x,y\rangle=\prod_{i=1}^{n}\langle x_i,y_i\rangle.\quad(4.5)$$
This is verified to be itself an inner product on $X$, called the **natural product** on $X$.

<a id="pdf-24e94ad30862-p024-b002"></a>
<!-- pdf-source: page=24; block=2; confidence=0.80 -->
Illustrative binary case $q=2$, $F=\{0,1\}$: $\langle\alpha,\beta\rangle=(-1)^{\alpha\beta}$, so the natural product of binary $n$-tuples is $\langle x,y\rangle=(-1)^{[x,y]}$ where $[x,y]=x_1y_1+\dots+x_ny_n\ (\mathrm{mod}\ 2)$ is the scalar product over the binary field.

<a id="pdf-24e94ad30862-p024-b003"></a>
<!-- pdf-source: page=24; block=3; confidence=0.85 -->
**Definition.** For arbitrary $q\ge2$ the **weight partition** $\sigma=\{X_0,X_1,\dots,X_n\}$ is formed by the classes of elements of constant weight:
$$X_k=\{x\in X\mid w_H(x)=k\},\quad k=0,1,\dots,n.\quad(4.6)$$
The cardinality of $X_k$ (valence of $R_k$) is $v_k=\binom{n}{k}(q-1)^k$. With a normalization adapted to the problem, the **Krawtchouk polynomial** of degree $k$ (cf. Szegő) is, for given $n,q$ and $k=0,1,\dots,n$,
$$K_k(u)=\sum_{j=0}^{k}(-1)^j(q-1)^{k-j}\binom{u}{j}\binom{n-u}{k-j}\quad(4.7)$$
in the indeterminate $u$ (with $\binom{u}{j}=u(u-1)\cdots(u-j+1)/j!$); it is a polynomial of degree $k$ in $u$. An equivalent expression, whose verification is left to the reader, is
$$K_k(u)=\sum_{i=0}^{k}(-q)^i(q-1)^{k-i}\binom{n-i}{k-i}\binom{u}{i}.\quad(4.8)$$

<a id="pdf-24e94ad30862-p024-b004"></a>
<!-- pdf-source: page=24; block=4; confidence=0.60 -->
**Theorem 4.1.** The natural product (4.5) and the Krawtchouk polynomials are related by, for $x'$ of weight $u=w(x')$,
$$\sum_{x\in X_k}\langle x,x'\rangle=K_k(u).\quad(4.9)$$

<a id="pdf-24e94ad30862-p024-b005"></a>
<!-- pdf-source: page=24; block=5; confidence=0.40 -->
**Proof.** Fix a $k$-subset $J$ of coordinate positions and compute the contribution $c(J)$ to the sum from the $(q-1)^k$ elements $x'\in X_k$ supported on $J$, as a product over $i\in J$. By (4.4) each bracketed factor takes one of two values according to whether the component $x_i$ is zero or nonzero; grouping by the zero components indexed in $J$ gives $c(J)$. The number of choices of $J$ meeting the support of $x$ (with $w(x)=u$) equals a product of binomial coefficients $\binom{u}{\cdot}\binom{n-u}{\cdot}$, and summing yields exactly the right-hand member of (4.9). $\square$

<a id="pdf-24e94ad30862-p024-b006"></a>
<!-- pdf-source: page=24; block=6; confidence=0.60 -->
**Theorem 4.2.** The eigenmatrices $P$ and $Q$ of the Hamming scheme are given in terms of Krawtchouk polynomials by
$$P_k(i)=Q_k(i)=K_k(i).$$
Moreover $H(n,q)$ is self-dual with respect to the matrix $S\in C(X,X)$ defined from the natural product.

<a id="pdf-24e94ad30862-p024-b007"></a>
<!-- pdf-source: page=24; block=7; confidence=0.25 -->
**Proof.** Consider the weight partition and the submatrices $S_k\in C(X,X_k)$, and derive a formula for the $(x,y)$-entry $(S S_k)(x,y)$. By (4.2)-(4.3), $w_H(x-y)$ determines membership in $R_k$, so using the incidence matrices one obtains $S S_k=\sum(\dots)$ (4.10). The matrices $J_k$ form a set of mutually orthogonal idempotents… (continues on next page).

<a id="pdf-24e94ad30862-p025-b001"></a>
<!-- pdf-source: page=25; block=1; confidence=0.55 -->
**Proof (cont.).** Since the $J_k$ lie in the Bose–Mesner algebra, they are its minimal idempotents; comparing (4.10) with the definition (2.16) of the eigenmatrix $Q$ gives $Q_k(i)=K_k(i)$ for all $i,k$. Using sec. 2.6, $(X,R)$ is dual to itself with respect to $e=0$ and to $S$ (both partitions $\pi(X,S)$ and $\pi(X,e)$ equal the weight partition $\omega$; details omitted). By theorem 2.8, $P=Q$, concluding the proof. $\square$

<a id="pdf-24e94ad30862-p025-b002"></a>
<!-- pdf-source: page=25; block=2; confidence=0.85 -->
Applying theorem 2.3 to $H(n,q)$ gives the orthogonality relations for the Krawtchouk polynomials:
$$\sum_{i=0}^{n}K_r(i)K_s(i)\binom{n}{i}(q-1)^i=q^{n}\binom{n}{s}(q-1)^s\,\delta_{r,s},\quad r,s=0,1,\dots,n.$$
Thus $K_0(u),\dots,K_n(u)$ form the orthogonal polynomials on $N=\{0,1,\dots,n\}$ for the weight $w(i)=v_i=\mu_i=\binom{n}{i}(q-1)^i$. A classical result (Szegő, p.42) yields the recurrence
$$(k+1)K_{k+1}(u)=\big[(q-1)(n-k)+k-qu\big]K_k(u)-(q-1)(n-k+1)K_{k-1}(u).\quad(4.11)$$

<a id="pdf-24e94ad30862-p025-b003"></a>
<!-- pdf-source: page=25; block=3; confidence=0.75 -->
**Definition (code).** A code of length $n$ over alphabet $F$ is a nonempty subset $Y\subseteq X=F^n$ with the Hamming distance (4.1); its elements are codewords. If the pairwise distances are restricted to a set $M$ of values, such a code is exactly an $M$-clique in the Hamming scheme, and the linear-programming bound (3.22) upper-bounds $|Y|$. The important cases are
$$M=\{0,\delta,\delta+1,\dots,n\},\quad 1\le\delta\le n,\quad(4.12)$$
for which an $M$-clique in $H(n,q)$ is a $q$-ary code of length $n$ with minimum distance $\ge\delta$.

<a id="pdf-24e94ad30862-p025-b004"></a>
<!-- pdf-source: page=25; block=4; confidence=0.70 -->
Expository: the best code of given $n,q,\delta$ maximizes the number of words; many authors sought upper bounds. Numerical values $|Y|\le g(Q,M)$ are promising (cf. sec. 4.3); McEliece and others applied the LP bound with encouraging results, but a general closed form seems out of reach and large $n$ requires computation.

<a id="pdf-24e94ad30862-p025-b005"></a>
<!-- pdf-source: page=25; block=5; confidence=0.50 -->
**Definition.** A simplification for the binary case: a subset $M\subseteq N=\{0,1,\dots,n\}$ is called **odd** according to a parity condition on its elements ($i\equiv0$ vs $i\equiv1\pmod 2$); e.g. the set (4.12) is odd for appropriate $\delta$. On $N'=\{0,1,\dots,n+1\}$ one associates to each odd $M$ the even subset
$$M'=\{i\in N'\mid i\equiv 0\pmod 2,\ \dots\}.\quad(4.13)$$
The map $M\mapsto M'$ is a bijection between odd subsets of $N$ and even subsets of $N'$, with cardinalities related by $m'=\lfloor(m+1)/2\rfloor$.

<a id="pdf-24e94ad30862-p025-b006"></a>
<!-- pdf-source: page=25; block=6; confidence=0.55 -->
**Theorem 4.3.** Let $M$ be an odd subset of $N$ with associated even subset $M'$ (4.13) of $N'$. Then, for $q=2$, the linear-programming values of the two Hamming schemes coincide: $g(Q,M)=g(Q',M')$.

<a id="pdf-24e94ad30862-p025-b007"></a>
<!-- pdf-source: page=25; block=7; confidence=0.25 -->
**Proof.** Establishes a two-way correspondence between programs. From a program $b$ of $(Q,M)$ one builds an $(n+2)$-tuple $b'=(b_0',\dots)$ (with $b_{-1}=b_{n+1}=0$) that is a program of $(Q',M')$. Conversely, from any program $b'$ of $(Q',M')$ one builds an $(n+1)$-tuple (involving factors $(n-i+1)$ and $(i+1)b_{i+1}'$) that is a program of $(Q,M)$ with equal objective $\sum b_i$. (Continues on next page.)

<a id="pdf-24e94ad30862-p026-b001"></a>
<!-- pdf-source: page=26; block=1; confidence=0.90 -->
**Proof (cont.).** The transformations rely on properties of the $q=2$ Krawtchouk polynomials (details omitted). Such a double correspondence with $\sum b_i=\sum b_i'$ between the programs of $(Q,M)$ and $(Q',M')$ shows that the maximal values $g=\sum b_i$ and $g'=\sum b_i'$ are equal, which proves the theorem.

<a id="pdf-24e94ad30862-p026-b002"></a>
<!-- pdf-source: page=26; block=2; confidence=0.55 -->
Consequence: for $q=2$ and odd $M$, the LP problem $(Q,M)$ may be replaced by the simpler $(Q',M')$ when only $g(Q,M)$ and one maximal program are wanted. For even $M'\subseteq N'$, any $(n+2)$-tuple $b'$ with $b_i'=0$ for $i\in N'-M'$ satisfies $b'Q_k'=b'Q_{n+1-k}'$; hence $(Q',M')$ effectively has only $\lfloor(n+1)/2\rfloor$ inequalities in $\lfloor(n+1)/2\rfloor$ variables.

<a id="pdf-24e94ad30862-p026-b003"></a>
<!-- pdf-source: page=26; block=3; confidence=0.75 -->
**Example.** Consider the binary codes $Y$ of length $n=13$ and designed minimum distance $\delta=5$, i.e. the $M$-cliques in $H(13,2)$ with $M=\{0,5,6,\dots,13\}$. To the odd subset $M$ of $N$ corresponds the even subset $M'=\{0,6,8,10,12,14\}$ of $N'$, and by theorem 4.3 $|Y|\le g(Q',M')$. The inequalities $b'Q_k'\ge0$ of the problem $(Q',M')$ are
$$\begin{aligned}
2b_6'-2b_8'-6b_{10}'-10b_{12}'-14b_{14}'&\ge-14,\\
-5b_6'-5b_8'+11b_{10}'+43b_{12}'+91b_{14}'&\ge-91,\\
-12b_6'+12b_8'+4b_{10}'-100b_{12}'-364b_{14}'&\ge-364,\\
9b_6'+9b_8'-39b_{10}'+121b_{12}'+1001b_{14}'&\ge-1001,\\
30b_6'-30b_8'+38b_{10}'-22b_{12}'-2002b_{14}'&\ge-2002,\\
-5b_6'-5b_8'+27b_{10}'-165b_{12}'+3003b_{14}'&\ge-3003,\\
-40b_6'+40b_8'-72b_{10}'+264b_{12}'-3432b_{14}'&\ge-3432,
\end{aligned}$$
the function to be maximized being $g'=1+b_6'+\dots+b_{14}'$. The coefficients $Q_k'(i)$ follow from recurrence (4.11) in the form $(k+1)Q_{k+1}'(i)=(14-2i)Q_k'(i)-(15-k)Q_{k-1}'(i)$. Solving $(Q',M')$ by the simplex algorithm gives a unique maximal program $b'=(1,0,0,0,0,0,42,0,7,0,14,0,0,0,0)$, whence $g(Q',M')=64$. The bound $|Y|\le64$ is best possible: there exists a binary code of length 13 and minimum distance 5 with 64 codewords, derivable from the Nordstrom–Robinson code (cf. also Goethals).

<a id="pdf-24e94ad30862-p026-b004"></a>
<!-- pdf-source: page=26; block=4; confidence=0.45 -->
**Section 4.1.3. Orthogonal arrays.** Because the eigenmatrices $P$ and $Q$ of the Hamming scheme are identical, the code problem is (at least formally) dual to the problem of $T$-designs with $T=\{1,2,\dots,n-1\}$; in particular the LP bound $|Y|\ge q^n/g(Q,M)$ for $M$ as in (4.12). This section shows $T$-designs correspond to the orthogonal arrays introduced by Rao.

<a id="pdf-24e94ad30862-p026-b005"></a>
<!-- pdf-source: page=26; block=5; confidence=0.60 -->
**Definition (orthogonal array).** Form an array whose rows are the words of a code $Y$ of length $n$ over $F$. With $\tau$ (strength) and $\lambda$ (index) positive integers, $Y$ forms an **orthogonal array of strength $\tau$** if, for every choice of $\tau$ distinct columns, each $\tau$-tuple over $F$ occurs exactly $\lambda$ times; then $|Y|=\lambda q^{\tau}$. For a $\tau$-tuple of symbols $(\omega_1,\dots,\omega_\tau)$ and a tuple $L=(i_1,\dots,i_\tau)$ of distinct positions, $m_L(\omega_1,\dots,\omega_\tau)$ denotes the number of codewords $x\in Y$ with $x_{i_1}=\omega_1,\dots,x_{i_\tau}=\omega_\tau$. Then $Y$ is an orthogonal array if and only if $m_L(\omega_1,\dots,\omega_\tau)$ is constant over all choices of $\omega_j\in F$ and $L$ (using the Abelian-group structure of $F$).

<a id="pdf-24e94ad30862-p026-b006"></a>
<!-- pdf-source: page=26; block=6; confidence=0.40 -->
**Theorem 4.4.** For a given set $T=\{1,2,\dots,t\}$, a subset $Y$ is a $T$-design in $H(n,q)$ if and only if it forms an orthogonal array (of the corresponding strength).

<a id="pdf-24e94ad30862-p026-b007"></a>
<!-- pdf-source: page=26; block=7; confidence=0.25 -->
**Proof.** For a $t$-tuple $L=(i_1,\dots,i_t)$ and integer $k$ with $0\le k\le t$, define $X_k(L)=\{x\in X\mid \dots\}$ in terms of the weight class $X_k$ of (4.6). The union $X_0(L)\cup\dots\cup X_t(L)$ is the set of elements $x'$ with $x_i'=0$ for $i\notin\{i_1,\dots,i_t\}$… (continues beyond supplied pages).
