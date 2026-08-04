<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: b372a20892cea7ca1dcfae2d0910754a5e92dbc0efc67a20cebea38ecac22abe -->

<a id="pdf-b372a20892ce-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.98 -->
# A Near-Cubic Lower Bound for 3-Query Locally Decodable Codes from Semirandom CSP Refutation

Authors: Omar Alrabiah, Venkatesan Guruswami (UC Berkeley); Pravesh K. Kothari, Peter Manohar (Carnegie Mellon University).

<a id="pdf-b372a20892ce-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.95 -->
A $q$-locally decodable code (LDC) $\mathcal{C}\colon\{\pm1\}^k\to\{\pm1\}^n$ lets any message bit $b_i$ be recovered with good confidence by querying the (corrupted) encoding in at most $q$ coordinates. Known: $2$-LDCs achieve $n=\exp(O(k))$, which is tight. For $q=3$, best constructions give $n=\exp(k^{o(1)})$ while the best prior lower bound was quadratic, $n\ge\tilde\Omega(k^2)$. This paper proves a near-cubic lower bound $n\ge\tilde\Omega(k^3)$, a polynomial-in-$k$ improvement, via a new connection between LDCs and refuting CSPs with limited randomness, building on semirandom-CSP refutation techniques of [GuruswamiKM22, HsiehKM23] and spectral bounds on Kikuchi matrices.

<a id="pdf-b372a20892ce-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.97 -->
## 1. Introduction

<a id="pdf-b372a20892ce-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.94 -->
**Definition (q-locally decodable code).** A binary LDC $\mathcal{C}\colon\{\pm1\}^k\to\{\pm1\}^n$ is $q$-locally decodable if, for any $i\in[k]$, the decoder makes at most $q$ queries to a corrupted codeword $y$ and outputs $b_i$ with probability $1/2+\varepsilon$, provided $\Delta(y,\mathcal{C}(b)):=|\{v\in[n]:y_v\ne\mathcal{C}(b)_v\}|\le\delta n$, where $\delta,\varepsilon$ are constants. LDCs were central to the PCP theorem and connect to worst-case/average-case reductions, private information retrieval, secure multiparty computation, derandomization, matrix rigidity, data structures, and fault-tolerant computation.

<a id="pdf-b372a20892ce-p001-b005"></a>
<!-- pdf-source: page=1; block=5; confidence=0.93 -->
For $q=2$: Hadamard code gives $n=2^k$ with matching lower bound $n=2^{\Omega(k)}$ [KdW04, GKST06, Bri16, Gop18]. For $q\ge3$ a large gap remains: matching-vector-code constructions [Yek08, Efremenko09, DGY11] give $n=2^{k^{o(1)}}$. Lower bounds: Katz–Trevisan [KT00] $n\ge\Omega(k^{q/(q-1)})$; Kerenidis–de Wolf [KdW04] via a quantum argument $n\ge k^{q/(q-2)}/\mathrm{polylog}(k)$ for even $q$ and $n\ge k^{(q+1)/(q-1)}/\mathrm{polylog}(k)$ for odd $q$, giving $n\ge\Omega(k^2/\log^2 k)$ at $q=3$; Woodruff [Woo07, Woo12] improved to $n\ge\Omega(k^2/\log k)$ (nonlinear) and $n\ge\Omega(k^2)$ (linear); Bhattacharya–Chandran–Ghoshal [BCG20] reproved $n\ge\Omega(k^2/\log k)$ combinatorially under extra assumptions.

<a id="pdf-b372a20892ce-p001-b006"></a>
<!-- pdf-source: page=1; block=6; confidence=0.96 -->
**Main Theorem.** Let $\mathcal{C}\colon\{\pm1\}^k\to\{\pm1\}^n$ be $(3,\delta,\varepsilon)$-locally decodable. Then $k^3\le n\cdot O\big((\log^6 n)/(\varepsilon^{32}\delta^{16})\big)$. In particular, for constant $\delta,\varepsilon$, $n\ge\Omega(k^3/\log^6 k)$. This improves the previous best bound by a $\tilde O(k)$ factor.

<a id="pdf-b372a20892ce-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.90 -->
The $\varepsilon,\delta$ dependence is unoptimized; binary linear codes get slightly better $\log k,\varepsilon,\delta$ dependence (Thm thm:linreduction, Cor cor:linlb). The result extends to nonbinary alphabets with polynomial loss in alphabet size (Thm thm:main-gen-alpha). Via known LCC-to-LDC relations (e.g. [BGT17, Thm A.6]), the Main Theorem yields a similar lower bound for $3$-query LCCs.

<a id="pdf-b372a20892ce-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.92 -->
The main tool is a connection between existence of LDCs and refutation of Boolean CSPs with limited randomness, analogous to the PCP/hardness-of-approximation link (each verifier query set becomes a local constraint). Refutation builds on the spectral analysis of Kikuchi matrices from [GuruswamiKM22] (refined in [HsiehKM23]), which gave strong refutation for semirandom/smoothed CSPs and proved Feige's hypergraph Moore bound conjecture up to one logarithmic factor.

<a id="pdf-b372a20892ce-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.90 -->
The prior odd-$q$ bound $n\ge k^{(q+1)/(q-1)}/\mathrm{polylog}(k)$ follows (up to polylog) by treating a $q$-LDC as a $(q+1)$-LDC. The improvement here obtains, for $q=3$, the stronger even-$q$-type tradeoff. The proof does not extend to odd $q\ge5$ (the natural generalization fails, noted at the end of the proof-overview section); proving $n\ge k^{q/(q-2)}/\mathrm{polylog}(k)$ for all odd $q\ge5$ is left open.

<a id="pdf-b372a20892ce-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.96 -->
### 1.1. Proof overview

<a id="pdf-b372a20892ce-p002-b005"></a>
<!-- pdf-source: page=2; block=5; confidence=0.91 -->
**Overview (key insight).** For any $q$, a $q$-LDC yields a collection of $q$-XOR instances (one per message), and a typical instance has high value: some assignment satisfies a $(1/2+\varepsilon)$-fraction of constraints. To lower-bound $n$ for $3$-LDCs it suffices to show that for any construction with $n\ll k^3$, the $3$-XOR instance for a uniformly random message has low value, established by producing a refutation (a low-value certificate).

<a id="pdf-b372a20892ce-p002-b006"></a>
<!-- pdf-source: page=2; block=6; confidence=0.92 -->
**Overview (normal form).** Assume $\mathcal{C}\colon\mathbb{F}_2^k\to\mathbb{F}_2^n$ is a linear $q$-LDC. By standard reductions (Lemma 6.2 in [Yek12]) it may be put in normal form: there exist $q$-uniform hypergraph matchings $\mathcal{H}_1,\dots,\mathcal{H}_k$, each with $\Omega(n)$ (disjoint) hyperedges, and the decoder on input $i$ picks a uniformly random $C\in\mathcal{H}_i$ and outputs $\prod_{v\in C}x_v$. When $x=\mathcal{C}(b)$, decoding recovers $b_i$ with probability $1$; equivalently, for every $b\in\mathbb{F}_2^k$ the assignment $x=\mathcal{C}(b)$ satisfies the $q$-XOR constraints $\forall i\in[k],\,C\in\mathcal{H}_i:\ \prod_{v\in C}x_v=b_i$.

<a id="pdf-b372a20892ce-p002-b007"></a>
<!-- pdf-source: page=2; block=7; confidence=0.92 -->
**Overview (the XOR instance).** Draw $b\in\mathbb{F}_2^k$ at random and form the $q$-XOR instance $\forall i,\,C\in\mathcal{H}_i:\ \prod_{v\in C}x_v=b_i$. By linearity it is satisfiable for every $b$, so proving it is unsatisfiable with high probability over random $b$ yields a contradiction.

<a id="pdf-b372a20892ce-p002-b008"></a>
<!-- pdf-source: page=2; block=8; confidence=0.91 -->
**Overview (main challenge).** If the instance were fully random (both $\mathcal{H}_i$ and $b_i$ uniform) or even semirandom (worst-case $\mathcal{H}_i$ but independent uniform right-hand sides per constraint), a union bound proves unsatisfiability. Here randomness is much more limited: all constraints $C\in\mathcal{H}_i$ share the same right-hand side $b_i$, so the $n$-variable instance has only $k\ll n$ independent random bits. Unsatisfiability is established by constructing a subexponential-size SDP-based certificate of low value, adapting the semirandom-refutation techniques of [GuruswamiKM22] to exploit the combinatorial structure.

<a id="pdf-b372a20892ce-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.90 -->
**Overview (warmup, even $q$).** Certifying unsatisfiability is easier for even $q$. Let $\ell$ be a parameter and $N:=\binom{n}{\ell}$. For $C\in\binom{[n]}{q}$, define the Kikuchi (symmetric-difference) matrix $A^{(C)}\in\mathbb{R}^{N\times N}$ [WeinAM19] indexed by $S\in\binom{[n]}{\ell}$, with $A^{(C)}(S,T)=1$ iff $S\oplus T=C$ (else $0$); equivalently $S=C_1\cup Q$, $T=C_2\cup Q$ where $C_1,C_2$ are the two halves of $C$ and $Q\subseteq[n]\setminus C$, $|Q|=\ell-q/2$. Set $A=\sum_{i=1}^k b_i\sum_{C\in\mathcal{H}_i}A^{(C)}$. Using the quadratic form $y^\top A y$ with $y_S:=\prod_{v\in S}x_v$ for $x=\mathcal{C}(b)$, one gets $\lVert A\rVert_2\ge(\ell/n)^{q/2}\sum_i|\mathcal{H}_i|\ge(\ell/n)^{q/2}\,\Omega(kn)$, independent of the draw of $b$.

<a id="pdf-b372a20892ce-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.89 -->
**Overview (upper bound).** Write $A=\sum_{i=1}^k b_i A_i$ with $A_i:=\sum_{C\in\mathcal{H}_i}A^{(C)}$, a sum of $k$ independent mean-$0$ matrices. Matrix Khintchine gives $\lVert A\rVert_2\le O(\Delta)\sqrt{k\ell\log n}$ w.h.p. over $b$, where $\Delta$ is the max $\ell_1$-norm of a row of any $A_i$. Some rows have $\ell_1$-norm as large as $\Omega(\ell)$; for $\ell\le n^{1-2/q}$ one "zeroes out" rows so each row/column of $A_i$ has at most one nonzero entry (set $A_i(S,T)=1$ iff $S\oplus T=C\in\mathcal{H}_i$ and $|S\oplus C'|,|T\oplus C'|\ne\ell$ for all other $C'\in\mathcal{H}_i$), giving $\Delta=1$. This explicit variant of the [GuruswamiKM22] row-pruning (via [schudysviridenko] polynomial concentration), following [HsiehKM23], saves a $\mathrm{polylog}(n)$ factor.

<a id="pdf-b372a20892ce-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.91 -->
**Overview (combining).** For $\ell\le n^{1-2/q}$: $(\ell/n)^{q/2}\,\Omega(kn)\le\lVert A\rVert_2\le O(\sqrt{k\ell\log n})$. Taking $\ell=n^{1-2/q}$ (the largest valid value) yields $k\le n^{1-2/q}\cdot\mathrm{polylog}(n)$.

<a id="pdf-b372a20892ce-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.90 -->
**Overview (odd $q$ obstruction).** For odd $q$ (e.g. $q=3$) the condition $S\oplus T=C$ never holds, so $A^{(C)}$ is meaningless. Indexing columns by sets of size $\ell+1$ instead of $\ell$ makes the matrix asymmetric, yielding the suboptimal bound $k\le n^{1-2/(q+1)}\mathrm{polylog}(n)$ — matching the current odd-$q$ state of the art, since the asymmetric matrix effectively treats $q$ as $q+1$.

<a id="pdf-b372a20892ce-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.90 -->
**Overview (the $q=3$ idea).** Transform the $3$-LDC into a $4$-XOR instance and refute it with an appropriate Kikuchi matrix. Randomly partition $[k]$ into $L,R$ and fix $b_j=1$ for all $j\in R$. For each intersecting pair $C_i\in\mathcal{H}_i$ ($i\in L$), $C_j\in\mathcal{H}_j$ ($j\in R$), add the derived constraint $C_i\oplus C_j$ with right-hand side $b_i$. (If $|C_i\cap C_j|=2$ the derived constraint is $2$-XOR, a minor issue that is ignored in the overview.) Satisfiability of the $3$-XOR instance implies satisfiability of the $4$-XOR instance, which has $\sim k^2 n$ constraints, since a typical $v\in[n]$ lies in $\sim k$ hyperedges of $\cup_i\mathcal{H}_i$ and can be canceled to form $\sim k^2$ derived constraints.

<a id="pdf-b372a20892ce-p003-b006"></a>
<!-- pdf-source: page=3; block=6; confidence=0.90 -->
**Overview (partition rationale).** The $(L,R)$ partition produces $\sim k^2 n$ constraints while keeping $k$ independent random bits in the right-hand sides. Using all derived constraints (not just those crossing $(L,R)$) could create correlated right-hand sides — e.g. three constraints with sides $b_ib_j,\ b_jb_t,\ b_ib_t$, which are pairwise but not $3$-wise independent. With the partition, any two constraints' right-hand sides are either equal or independent, avoiding nontrivial correlations.

<a id="pdf-b372a20892ce-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.95 -->
Producing extra constraints in the 4-XOR instance is essential; otherwise only the $q=4$ warmup bound would follow. The reduction does not yield the structure of a 4-XOR instance from a 4-LDC: letting $\cH'_i$ ($i\in L$) be the derived constraints with right-hand side $b_i$, $\cH'_i$ is not a matching. Typically $|\cH'_i|=\Omega(nk)$, whereas a matching has at most $n/q$ hyperedges.

<a id="pdf-b372a20892ce-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.95 -->
CSP refutation still applies, but since $\cH'_i$ is not a matching the "zeroing out" step requires that each vertex pair $p=(u,v)$ appears in at most $\polylog(n)$ hyperedges of the 3-uniform $\cup_{i=1}^k\cH_i$. Under this assumption the even-$q$ blueprint gives $n\geq k^3/\polylog(k)$. A recent work [BCG20] reproved $n\geq k^2/\polylog(k)$ under a similar pair assumption.

<a id="pdf-b372a20892ce-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.95 -->
The assumption is removed by bounding heavy pairs. For heavy pairs $p=(u,v)$ appearing in $\gg\log n$ clauses of $\cH:=\cup_{i=1}^k\cH_i$, transform the 3-XOR into a bipartite 2-XOR instance by replacing each heavy pair with a new variable $y_p$: a 3-XOR clause $C=(u,v,w)$ in $\cH_i$ becomes the 2-XOR clause $(p,w)$, i.e. $x_u x_v x_w=b_i$ becomes $y_p x_w=b_i$. Each 2-XOR clause uses one heavy-pair variable and one original variable in $[n]$. Too many heavy pairs give enough constraints to refute the instance, contradicting satisfiability. For odd $q\geq5$ this heavy-pair argument breaks down, blocking generalization of the main theorem to all odd $q$.

<a id="pdf-b372a20892ce-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.98 -->
**Discussion: LDCs and the CSP perspective.**

<a id="pdf-b372a20892ce-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.90 -->
Prior work reduces even-$q$ LDCs to 2-query LDCs and applies tight 2-LDC lower bounds (odd $q$ handled by noting a $q$-LDC is a $(q+1)$-LDC). The even-$q$ CSP-refutation warmup mirrors the $q$-LDC-to-2-LDC reduction of [KdW04], whose tensor-product 2-LDC matrix relates closely to the Kikuchi matrix $A$ of [WeinAM19]. The CSP viewpoint enables odd-$q$ analysis via a modified Kikuchi matrix, producing a 4-XOR instance that does not correspond to a 4-LDC. The main lower bound can also be obtained by black-box reduction to 2-LDC bounds, but only for linear 3-LDCs, requiring two invocations (vs. one for even $q$) and not extending to non-linear codes.

<a id="pdf-b372a20892ce-p004-b006"></a>
<!-- pdf-source: page=4; block=6; confidence=0.97 -->
**Section: Preliminaries.** *Basic notation.*

<a id="pdf-b372a20892ce-p004-b007"></a>
<!-- pdf-source: page=4; block=7; confidence=0.96 -->
$[n]:=\{1,\dots,n\}$. For $S,T\subseteq[n]$, $S\oplus T$ is the symmetric difference. ${[n]\choose t}$ is the collection of size-$t$ subsets of $[n]$. For $A\in\R^{m\times n}$, the spectral norm is $\|A\|_2:=\max_{\|x\|_2=\|y\|_2=1}x^\top A y$.

<a id="pdf-b372a20892ce-p004-b008"></a>
<!-- pdf-source: page=4; block=8; confidence=0.97 -->
**Definition.** A hypergraph $\cH$ on vertices $[n]$ is a collection of hyperedges $C\subseteq[n]$. $\cH$ is $q$-uniform if $|C|=q$ for all $C\in\cH$, and a matching if all hyperedges are disjoint. For $Q\subseteq[n]$, $\deg_\cH(Q):=|\{C\in\cH:Q\subseteq C\}|$.

<a id="pdf-b372a20892ce-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.96 -->
**Definition (Locally Decodable Code).** $\cC:\Bits^k\to\Bits^n$ is $(q,\delta,\eps)$-locally decodable if there is a randomized decoder $\Dec$ with oracle access to $y\in\Bits^n$ and input $i\in[k]$ that (1) makes at most $q$ queries to $y$, and (2) for all $b\in\Bits^k$, $i\in[k]$, and $y$ with $\Delta(y,\cC(b))\leq\delta n$, $\Pr[\Dec^y(i)=b_i]\geq\tfrac12+\eps$, where $\Delta$ is Hamming distance.

<a id="pdf-b372a20892ce-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.96 -->
**Definition (Normal LDC).** $\cC:\Fits^k\to\Fits^n$ is $(q,\delta,\eps)$-normally decodable if for each $i\in[k]$ there is a $q$-uniform hypergraph matching $\cH_i$ with at least $\delta n$ hyperedges such that for every $C\in\cH_i$, $\Pr_{b\gets\Fits^k}[b_i=\prod_{v\in C}\cC(b)_v]\geq\tfrac12+\eps$.

<a id="pdf-b372a20892ce-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.96 -->
**Fact (Reduction to Normal Form, [Yek12] Lem 6.2).** If $\cC:\Bits^k\to\Bits^n$ is $(q,\delta,\eps)$-locally decodable, then there is $\cC':\Fits^k\to\Fits^{O(n)}$ that is $(q,\delta',\eps')$-normally decodable with $\delta'\geq\eps\delta/(3q^2 2^{q-1})$ and $\eps'\geq\eps/2^{2q}$.

<a id="pdf-b372a20892ce-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.95 -->
**Fact (Rectangular Matrix Khintchine, [Tropp15] Thm 4.1.1).** For fixed $d_1\times d_2$ matrices $X_1,\dots,X_k$ and i.i.d. $b_1,\dots,b_k\gets\Fits$, with $\sigma^2\geq\max(\|\sum_{i=1}^k X_iX_i^\top\|_2,\ \|\sum_{i=1}^k X_i^\top X_i\|_2)$, one has $\E[\|\sum_{i=1}^k b_i X_i\|_2]\leq\sqrt{2\sigma^2\log(d_1+d_2)}$.

<a id="pdf-b372a20892ce-p005-b005"></a>
<!-- pdf-source: page=5; block=5; confidence=0.96 -->
**Fact.** For positive integers $n,\ell,q$ with $n/2\geq\ell\geq q$, $e^{3q}(\ell/n)^q\geq {n-2q\choose\ell-q}\big/{n\choose\ell}\geq e^{-3q}(\ell/n)^q$.

<a id="pdf-b372a20892ce-p005-b006"></a>
<!-- pdf-source: page=5; block=6; confidence=0.93 -->
**Proof.** The ratio equals $\frac{(n-2q)!}{(\ell-q)!(n-\ell-q)!}\cdot\frac{\ell!(n-\ell)!}{n!}={n-\ell\choose q}{\ell\choose q}\big/\big[{2q\choose q}{n\choose 2q}\big]$. Using $(n/k)^k\leq{n\choose k}\leq(en/k)^k$ gives the upper bound $\leq e^{3q}(\ell/n)^q$ and the lower bound $\geq e^{-3q}(\ell/n)^q$ (the latter using $\ell\leq n/2$).

<a id="pdf-b372a20892ce-p005-b007"></a>
<!-- pdf-source: page=5; block=7; confidence=0.96 -->
**Section: Lower Bound for 3-Query Locally Decodable Codes.** *Setup.*

<a id="pdf-b372a20892ce-p005-b008"></a>
<!-- pdf-source: page=5; block=8; confidence=0.93 -->
By the normal-form Fact, to show $k^3\leq n\cdot O(\log^6 n)/(\eps^{32}\delta^{16})$ it suffices to show, for any $(3,\delta,\eps)$-normally decodable $\cC:\Fits^k\to\Fits^n$, that $k^3\leq n\cdot O(\log^6 n)/(\eps^{16}\delta^{16})$. This yields 3-uniform matchings $\cH_1,\dots,\cH_k$ satisfying the Normal LDC property; set $m:=\sum_{i=1}^k|\cH_i|$ and $\cH:=\cup_{i=1}^k\cH_i$. Idea: define a 3-XOR instance from the decoder that has high value; if $n\ll k^3$ it must have small value, a contradiction.

<a id="pdf-b372a20892ce-p005-b009"></a>
<!-- pdf-source: page=5; block=9; confidence=0.95 -->
**Definition (Key 3-XOR Instances).** For each $b\in\Fits^k$, the instance $\Psi_b$ has variables $x_1,\dots,x_n\in\Fits$ and constraints $\prod_{v\in C}x_v=b_i$ for each $i\in[k]$, $C\in\cH_i$. $\val(\Psi_b)$ is the max fraction of constraints satisfiable. Associate the polynomial $\psi_b(x):=\tfrac1m\sum_{i=1}^k b_i\sum_{C\in\cH_i}\prod_{v\in C}x_v$ with $\val(\psi_b):=\max_{x\in\Fits^n}\psi_b(x)$; then $\val(\Psi_b)=\tfrac12+\tfrac12\val(\psi_b)$.

<a id="pdf-b372a20892ce-p005-b010"></a>
<!-- pdf-source: page=5; block=10; confidence=0.94 -->
Every $\Psi_b$ has non-trivially large value: $\E_{b\gets\Fits^k}[\val(\psi_b)]\geq\E_{b\gets\Fits^k}[\psi_b(\cC(b))]\geq 2\eps$ (eq. vallowerbound); the first inequality is by definition of $\val$, the second by the Normal LDC definition (each constraint is satisfied by $\cC(b)$ with probability $\tfrac12+\eps$).

<a id="pdf-b372a20892ce-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.93 -->
**Overview.** It suffices to show $\E_{b\gets\Fits^k}[\val(\psi_b)]$ is small, via a CSP refutation algorithm inspired by [GuruswamiKM22], in two steps. (1) Decomposition: replace any pair $Q=\{u,v\}$ appearing in $\gg\log n$ hyperedges of $\cH:=\cup_{i=1}^k\cH_i$ with a new variable $y_Q$, giving a bipartite 2-XOR instance plus a residual 3-XOR instance where every pair appears in $\leq O(\log n)$ constraints. (2) Refutation: strongly refute each, bounding the average value over $b\sim\{-1,1\}^k$, hence bounding the original 3-XOR's expected value.

<a id="pdf-b372a20892ce-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.97 -->
**Definition (Degree).** For a $q$-uniform hypergraph $\cH$ on $n$ vertices and $Q\subseteq[n]$, $\deg_\cH(Q)$ is the number of $C\in\cH$ with $Q\subseteq C$.

<a id="pdf-b372a20892ce-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.95 -->
**Lemma (Hypergraph Decomposition).** Given 3-uniform $\cH_1,\dots,\cH_k$ on $n$ vertices, $\cH:=\cup_{i=1}^k\cH_i$, threshold $d\in\N$, and $P:=\{\{u,v\}:\deg_\cH(\{u,v\})>d\}$, there exist 3-uniform $\cH'_1,\dots,\cH'_k$ and bipartite graphs $G_1,\dots,G_k$ such that: (1) each $G_i$ has left vertices $[n]$, right vertices $P$; (2) $\cH'_i\subseteq\cH_i$; (3) a one-to-one correspondence between $C\in\cH_i\setminus\cH'_i$ and edges $e$ in $G_i$ via $e=(w,\{u,v\})\mapsto C=\{u,v,w\}$; (4) with $\cH':=\cup_{i=1}^k\cH'_i$, $\deg_{\cH'}(\{u,v\})\leq d$ for all $u\neq v$; (5) if $\cH_i$ is a matching, then $\cH'_i$ and $G_i$ are matchings.

<a id="pdf-b372a20892ce-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.95 -->
**Lemma (2-XOR refutation).** Fix $n$. For bipartite matchings $G_1,\dots,G_k$ with left vertices $[n]$ and right vertex set $P$ with $|P|\leq nk/d$, and $g_b(x,y):=\sum_{i=1}^k b_i\sum_{e=\{v,p\}:v\in[n],p\in P}x_v y_p$ with $\val(g_b):=\max_{x\in\Fits^n,y\in\Fits^P}g_b(x,y)$, one has $\E_{b\gets\Fits^k}[\val(g_b)]\leq O(nk\sqrt{(\log n)/d})$.

<a id="pdf-b372a20892ce-p006-b005"></a>
<!-- pdf-source: page=6; block=5; confidence=0.95 -->
**Lemma (3-XOR refutation).** For 3-uniform matchings $\cH_1,\dots,\cH_k$ on $n$ vertices, $\cH:=\cup_{i=1}^k\cH_i$, with $\deg_\cH(\{u,v\})\leq d$ for all pairs, and $f_b(x):=\sum_{i=1}^k b_i\sum_{C\in\cH_i}\prod_{v\in C}x_v$, one has $\E_{b\gets\Fits^k}[\val(f_b)]\leq n\sqrt{k}\cdot O(d)\cdot(nk)^{1/8}\log^{1/4}n$.

<a id="pdf-b372a20892ce-p006-b006"></a>
<!-- pdf-source: page=6; block=6; confidence=0.93 -->
**Proof (of main theorem).** Apply the Decomposition Lemma with $d=O((\log n)/(\eps^2\delta^2))$ (large constant), splitting $\Psi_b$ into 2-XOR and 3-XOR subinstances. Since $m\leq nk$, $|P|\leq m/d\leq nk/d$. By the correspondence, $m\,\val(\psi_b)\leq\val(f_b)+\val(g_b)$, and $m\geq\delta nk$. The 2-XOR Lemma with large constant gives $\E_b[\val(g_b)]\leq\eps\delta nk/3$. Combining with eq. vallowerbound and the 3-XOR Lemma: $2\eps\delta nk\leq 2\eps m\leq m\,\E_b[\val(\psi_b)]\leq\E_b[\val(f_b)+\val(g_b)]\leq \tfrac{\eps\delta nk}{3}+n\sqrt{k}\cdot O(\sqrt{\log n}/(\eps\delta))\cdot(nk)^{1/8}\log^{1/4}n$, which yields $\eps^2\delta^2\sqrt{k}\leq O(\sqrt{\log n})\cdot(nk)^{1/8}\log^{1/4}n$ and hence $k^3\leq n\cdot O(\log^6 n)/(\eps^{16}\delta^{16})$.

<a id="pdf-b372a20892ce-p006-b007"></a>
<!-- pdf-source: page=6; block=7; confidence=0.96 -->
**Subsection: Hypergraph decomposition — proof of the Decomposition Lemma.**

<a id="pdf-b372a20892ce-p006-b008"></a>
<!-- pdf-source: page=6; block=8; confidence=0.94 -->
**Proof (of Decomposition Lemma).** Greedy algorithm: initialize $\cH'_i=\cH_i$ and $P=\{\{u,v\}:\deg_{\cH'}(\{u,v\})>d\}$ (with $\cH'=\cup_{i}\cH'_i$). While $P\neq\emptyset$: choose $p=\{u,v\}\in P$ arbitrarily; for each $i\in[k]$ and $C\in\cH'_i$ with $p\in C$, remove $C$ from $\cH'_i$ and add edge $(C\setminus p,\,p)$ to $G_i$; recompute $P$. Output $\cH'_1,\dots,\cH'_k,G_1,\dots,G_k$. Properties (1),(2),(5) hold trivially; (4) holds since otherwise $P$ would be nonempty and the algorithm would not have terminated; (3) holds since each $C\in\cH_i$ starts in $\cH'_i$ and is either removed exactly once (added to $G_i$ as $(C\setminus p,p)$) or remains in $\cH'_i$ throughout.

<a id="pdf-b372a20892ce-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.97 -->
**Subsection.** Refuting the 2-XOR instance: proof of Lemma (2xor).

<a id="pdf-b372a20892ce-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.95 -->
**Proof (Lemma 2xor).** For each $e=\{v,p\}$ ($v\in[n]$, $p\in P$) define $A^{(e)}\in\mathbb{R}^{n\times P}$ with $A^{(e)}(v',p')=1$ iff $v'=v,p'=p$. Set $A_i:=\sum_{e\in G_i}A^{(e)}$ (bipartite adjacency matrix of $G_i$) and $A:=\sum_{i=1}^k b_iA_i$.

- $\mathrm{val}(g_b)\le\sqrt{n|P|}\,\|A\|_2$: for $x\in\{\pm1\}^n,y\in\{\pm1\}^P$, $g_b(x,y)=x^\top Ay\le\|x\|_2\|y\|_2\|A\|_2=\sqrt{n|P|}\|A\|_2$; so bounding $\mathbb{E}_b[\mathrm{val}(g_b)]$ reduces to bounding $\mathbb{E}_b[\|A\|_2]$.
- Each $\|A_i\|_2\le1$ (each row/column of $A_i$ has $\le1$ nonzero of magnitude $1$, since $G_i$ is a matching), so $\max(\|\sum_i A_iA_i^\top\|,\|\sum_i A_i^\top A_i\|)\le k$.
- Since the $b_i$ are i.i.d. from $\{\pm1\}$, Matrix Khintchine gives $\mathbb{E}[\|A\|_2]\le O(\sqrt{k\log n})$.

Hence $\mathbb{E}[\mathrm{val}(g_b)]\le\sqrt{n|P|}\,O(\sqrt{k\log n})\le O(nk\sqrt{(\log n)/d})$. $\square$

<a id="pdf-b372a20892ce-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.97 -->
**Section.** Refuting the 3-XOR instance: proof of Lemma (3xor).

<a id="pdf-b372a20892ce-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.93 -->
Write $f$ for $f_b$; set $m:=|\mathcal{H}|=\sum_{i=1}^k|\mathcal{H}_i|$. Notation $(u,C):=\{u\}\cup C$. Assume WLOG $k\le n/c$ for a large constant $c$ (else partition $[k]$ into $\le c$ blocks of size $\le n/c$ and refute separately). Strategy ("Cauchy–Schwarz trick"): build a 4-XOR instance by canceling each $x_u$ appearing in two clauses. Assign each $i\in[k]$ independently to $L$ or $R$; for $(u,C)\in\mathcal{H}_i$ ($i\in L$) and $(u,C')\in\mathcal{H}_j$ ($j\in R$) form the derived clause $C\oplus C'$. Relate the derived instance's value to the original 3-XOR and give a spectral refutation via a subexponential-sized matrix, bounding the expected value over the $b_i$.

<a id="pdf-b372a20892ce-p007-b005"></a>
<!-- pdf-source: page=7; block=5; confidence=0.94 -->
**Definition.** For a partition $(L,R)$ of $[k]$ into equal halves of size $k/2$, define
$$f_{L,R}(x):=\sum_{\substack{i\in L\\ j\in R}}\sum_{u\in[n]}\sum_{\substack{(u,C)\in\mathcal{H}_i\\(u,C')\in\mathcal{H}_j}}b_ib_j\,x_Cx_{C'},\qquad x_C:=\prod_{v\in C}x_v.$$
Since the $\mathcal{H}_i$ are matchings, after fixing $i,j,u$ there is at most one pair $(C,C')$ in the inner sum. Working only with cross-partition derived clauses preserves $\sim k$ independent random bits while eliminating correlations, enabling Matrix Khintchine.

<a id="pdf-b372a20892ce-p007-b006"></a>
<!-- pdf-source: page=7; block=6; confidence=0.95 -->
**Lemma (Cauchy–Schwarz Trick).** Let $f$ be as in Lemma 3xor and let $L,R\subseteq[k]$ be formed by placing each element of $[k]$ into $L$ independently w.p. $1/2$, $R=[k]\setminus L$. Then
$$9\cdot\mathrm{val}(f)^2\le 3nm+4n\,\mathbb{E}_{(L,R)}\mathrm{val}(f_{L,R}).$$
In particular $\mathbb{E}_{b\in\{\pm1\}^k}[9\,\mathrm{val}(f)^2]\le 3nm+4n\,\mathbb{E}_{(L,R)}\mathbb{E}_b[\mathrm{val}(f_{L,R})].$

<a id="pdf-b372a20892ce-p007-b007"></a>
<!-- pdf-source: page=7; block=7; confidence=0.93 -->
**Proof.** Fix $x\in\{\pm1\}^n$. Then
$$(3f(x))^2=\Big(\sum_{u}x_u\sum_{i}\sum_{(u,C)\in\mathcal{H}_i}b_ix_C\Big)^2\le\Big(\sum_u x_u^2\Big)\Big(\sum_u\big(\sum_i\sum_{(u,C)\in\mathcal{H}_i}b_ix_C\big)^2\Big)$$
$$=n\sum_u\sum_{i,j}\sum_{\substack{(u,C)\in\mathcal{H}_i\\(u,C')\in\mathcal{H}_j}}b_ib_jx_Cx_{C'}=n\Big(3\sum_i|\mathcal{H}_i|+\sum_u\sum_{i\ne j}\sum_{\substack{(u,C)\in\mathcal{H}_i\\(u,C')\in\mathcal{H}_j}}b_ib_jx_Cx_{C'}\Big)=3nm+4n\,\mathbb{E}_{(L,R)}f_{L,R}(x).$$
The first factor equality uses the $3$ ways to split $C_i\in\mathcal{H}_i$ with $|C_i|=3$ into $(u,C)$; the inequality is Cauchy–Schwarz; the last uses $\Pr[i\in L,j\in R]=1/4$. Finally $\max_x\mathbb{E}_{(L,R)}f_{L,R}(x)\le\mathbb{E}_{(L,R)}\max_x f_{L,R}(x)=\mathbb{E}_{(L,R)}\mathrm{val}(f_{L,R})$, giving $9\,\mathrm{val}(f)^2\le 3nm+4n\,\mathbb{E}_{(L,R)}\mathrm{val}(f_{L,R})$. $\square$

<a id="pdf-b372a20892ce-p007-b008"></a>
<!-- pdf-source: page=7; block=8; confidence=0.92 -->
**Subsection.** Bounding $\mathrm{val}(f_{L,R})$ using CSP refutation. Plan: for each $b$ and partition $(L,R)$ introduce a matrix $A$ (depending on $b,(L,R)$), relate $\mathrm{val}(f_{L,R})$ to $\|A\|_2$, and bound $\mathbb{E}_b[\|A\|_2]$.

<a id="pdf-b372a20892ce-p007-b009"></a>
<!-- pdf-source: page=7; block=9; confidence=0.95 -->
**Definition.** For $u\in[n]$, $u^{(1)}=(u,1)$ and $u^{(2)}=(u,2)$ in $[n]\times[2]$ (first/second copy of $[n]$). For $C\subseteq[n]$, $C^{(b)}:=\{(i,b):i\in C\}$ for $b\in[2]$.

<a id="pdf-b372a20892ce-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.95 -->
**Definition (Half clauses).** For $i\in L,j\in R$, $P_{i,j}$ is the set of pairs $(v^{(1)},w^{(2)})$ such that there exist clauses $(u,C)\in\mathcal{H}_i$ and $(u,C')\in\mathcal{H}_j$ with $v\in C$ and $w\in C'$. Set $P_i:=\bigcup_{j\in R}P_{i,j}$.

<a id="pdf-b372a20892ce-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.90 -->
The matrix is defined in two steps: first a matrix $B$, then modifications yielding the final matrix $A$.

<a id="pdf-b372a20892ce-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.94 -->
**Definition (Initial Kikuchi matrix).** Let $\ell:=(\sqrt{n/k})/c$ (large constant $c$) and $N:=\binom{2n}{\ell}$. For $S,T\subseteq[n]\times[2]$ and $C,C'\in\binom{[n]}{2}$, write $S\overset{C,C'}{\leftrightarrow}T$ iff (1) $S\oplus T=C^{(1)}\oplus C'^{(2)}$ and (2) $|S\cap C^{(1)}|=|S\cap C'^{(2)}|=|T\cap C^{(1)}|=|T\cap C'^{(2)}|=1$. (Here $C^{(1)}\oplus C'^{(2)}=C^{(1)}\cup C'^{(2)}$, disjoint.) For $i\in L$ and $C,C'$, define $N\times N$ matrix $B^{(i,C,C')}$ indexed by size-$\ell$ sets $S\subseteq[n]\times[2]$: $B^{(i,C,C')}(S,T)=1$ iff (1) $S\overset{C,C'}{\leftrightarrow}T$ and (2) each of $S,T$ contains at most one half clause from $P_i$; else $0$. Then
$$B_{i,j}:=\sum_u\sum_{(u,C)\in\mathcal{H}_i,(u,C')\in\mathcal{H}_j}B^{(i,C,C')},\quad B_i:=\sum_{j\in R}b_jB_{i,j},\quad B:=\sum_{i\in L}b_iB_i.$$
Well-definedness needs $\ell\ge2$, which holds because $k\le n/c'$ (the only use of that assumption).

<a id="pdf-b372a20892ce-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.90 -->
The matrices $B_i$ give a reduction from the 3-XOR instance $f$ to a 2-LDC, yielding the 3-LDC lower bound in the special case of linear codes (cf. Theorem linreduction).

<a id="pdf-b372a20892ce-p008-b005"></a>
<!-- pdf-source: page=8; block=5; confidence=0.93 -->
**Remark (edge count).** For fixed $(u,C)\in\mathcal{H}_i$, $(u,C')\in\mathcal{H}_j$ ($j\in R$), ignoring the half-clause condition, $B^{(i,C,C')}$ has exactly $4\binom{2n-4}{\ell-2}$ nonzero entries: $S\overset{C,C'}{\leftrightarrow}T$ iff $S,T$ each contain one entry of $C$ and one of $C'$ ($2$ choices per clause) and share the same remaining set $Q\subseteq([n]\times[2])\setminus(C^{(1)}\oplus C'^{(2)})$ of size $\ell-2$ ($\binom{2n-4}{\ell-2}$ choices). Using $[n]\times[2]$ (rather than $[n]$) keeps $|C^{(1)}\oplus C'^{(2)}|=4$ always, independent of $|C\oplus C'|$.

<a id="pdf-b372a20892ce-p008-b006"></a>
<!-- pdf-source: page=8; block=6; confidence=0.92 -->
If $S\overset{C,C'}{\leftrightarrow}T$ then each of $S,T$ already contains at least one half clause from $P_i$ (from $(C,C')$); the extra condition requires no other half clauses. This makes $B_i$ have $\le 2d$ nonzero entries per row, so $\|B_i\|_2\le 2d$ ($d$ from Lemma 3xor), without meaningfully reducing each $B^{(i,C,C')}$'s nonzeros. Without the condition, $\|B_i\|_2\ge\Omega(\ell)$.

<a id="pdf-b372a20892ce-p008-b007"></a>
<!-- pdf-source: page=8; block=7; confidence=0.95 -->
**Lemma (Nonzero entry bound).** For $i\in L$, $B_i$ (Def. Kikuchi matrix) has at most $2d$ nonzero entries per row/column. (Proof postponed to spectral-bound section.)

<a id="pdf-b372a20892ce-p008-b008"></a>
<!-- pdf-source: page=8; block=8; confidence=0.94 -->
**Lemma (Counting nonzero entries).** For $(u,C)\in\mathcal{H}_i$ and $(u,C')\in\mathcal{H}_j$ ($j\in R$), $B^{(i,C,C')}$ has at least $2\binom{2n-4}{\ell-2}$ nonzero entries (half of $4\binom{2n-4}{\ell-2}$); the extra condition costs only a factor $2$ per derived constraint. (Proof postponed.)

<a id="pdf-b372a20892ce-p008-b009"></a>
<!-- pdf-source: page=8; block=9; confidence=0.94 -->
**Definition (Final Kikuchi matrix).** For each $i\in L$ and clauses $(u,C)\in\mathcal{H}_i$, $(u,C')\in\mathcal{H}_j$ ($j\in R$), obtain $A^{(i,C,C')}$ from $B^{(i,C,C')}$ by arbitrarily zeroing entries until it has exactly $D:=2\binom{2n-4}{\ell-2}$ nonzero entries (the "equalizing step" of HsiehKM23). Then
$$A_{i,j}:=\sum_u\sum_{(u,C)\in\mathcal{H}_i,(u,C')\in\mathcal{H}_j}A^{(i,C,C')},\quad A_i:=\sum_{j\in R}b_jA_{i,j},\quad A:=\sum_{i\in L}b_iA_i.$$

<a id="pdf-b372a20892ce-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.93 -->
**Derivation.** Fix $x\in\{\pm1\}^n$ and define $z\in\{\pm1\}^N$ by $z_S:=\prod_{u\in S_1}x_u\prod_{v\in S_2}x_v$ for $S=S_1^{(1)}\cup S_2^{(2)}$, $|S|=\ell$. Then $D\cdot f_{L,R}(x)=z^\top A z$, because: (1) if $S\oplus T=C^{(1)}\oplus C'^{(2)}$ then $z_Sz_T=\prod_{u\in S_1\oplus T_1}x_u\prod_{v\in S_2\oplus T_2}x_v=\prod_{u\in C}x_u\prod_{v\in C'}x_v$; (2) each clause pair yields exactly $D=2\binom{2n-4}{\ell-2}$ nonzero entries $(S,T)$ of $A^{(i,C,C')}$, all with $S\oplus T=C^{(1)}\oplus C'^{(2)}$. Hence
$$\mathrm{val}(f_{L,R})\le\frac{N}{D}\|A\|_2.\qquad\text{(eq. boolnorm)}$$

<a id="pdf-b372a20892ce-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.96 -->
**Lemma (Spectral norm bound).** $\mathbb{E}_{b\in\{\pm1\}^k}[\|A\|_2]\le d\cdot O(\sqrt{k\ell\log n})$. (Proof postponed to spectral-bound section.)

<a id="pdf-b372a20892ce-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.94 -->
**Proof (Lemma 3xor).** By eq. boolnorm and the spectral-norm lemma,
$$\mathbb{E}_b[\mathrm{val}(f_{L,R})]\le\tfrac{N}{D}\mathbb{E}_b[\|A\|_2]\le\tfrac{N}{D}\,d\,O(\sqrt{k\ell\log n})\le\tfrac{n^2}{\ell^2}d\,O(\sqrt{k\ell\log n})=nkd\cdot O((nk)^{1/4}\sqrt{\log n}),$$
using $\ell=(\sqrt{n/k})/c$ and the binomial-ratio fact for $N/D$. Combining with the Cauchy–Schwarz lemma and $m\le nk$,
$$\mathbb{E}[\mathrm{val}(f)]^2\le\mathbb{E}[\mathrm{val}(f)^2]\le\tfrac19\big(3n^2k+4n\,\mathbb{E}_{(L,R)}\mathbb{E}_b[\mathrm{val}(f_{L,R})]\big)\le n^2kd\cdot O((nk)^{1/4}\sqrt{\log n}).$$
Hence $\mathbb{E}[\mathrm{val}(f)]\le n\sqrt{kd}\cdot O((nk)^{1/8}\log^{1/4}n)$. $\square$

<a id="pdf-b372a20892ce-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.96 -->
**Subsection.** Counting nonzero entries: proof of Lemma (rowpruning).

<a id="pdf-b372a20892ce-p009-b005"></a>
<!-- pdf-source: page=9; block=5; confidence=0.93 -->
**Proof (Lemma rowpruning).** Fix $j\in R$, $(u,C)\in\mathcal{H}_i$, $(u,C')\in\mathcal{H}_j$. By the edge-count remark there are exactly $4\binom{2n-4}{\ell-2}$ pairs $(S,T)$ with $S\overset{C,C'}{\leftrightarrow}T$; each size-$(\ell-2)$ set $Q\subseteq([n]\times[2])\setminus(C^{(1)}\oplus C'^{(2)})$ corresponds to $4$ pairs $(S,T)$, i.e. the $4$ half clauses of $P_i$ from $(C,C')$. Show for $\ge\tfrac12\binom{2n-4}{\ell-2}$ choices of $Q$, all $4$ pairs contain exactly one derived clause from $P_i$.

Call $Q$ **bad** if some identified $(S,T)$ has $S$ or $T$ containing more than one half clause from $P_i$. Since each of $S,T$ already has exactly one from $C^{(1)}\oplus C'^{(2)}$, $Q$ is bad in three ways: (1) $Q$ contains a half clause from $P_i$; (2) some $v^{(1)}\in C^{(1)}$, $w^{(2)}\in Q$ with $(v^{(1)},w^{(2)})\in P_i$; (3) some $v^{(1)}\in Q$, $w^{(2)}\in C'^{(2)}$ with $(v^{(1)},w^{(2)})\in P_i$. So
$$\#\{\text{bad }Q\}\le p_0\binom{2n-6}{\ell-4}+p_1\binom{2n-5}{\ell-3}+p_2\binom{2n-5}{\ell-3},$$
with $p_0=|P_i|$, $p_1=|\{(v^{(1)},w^{(2)})\in P_i:v^{(1)}\in C^{(1)}\}|$, $p_2=|\{(v^{(1)},w^{(2)})\in P_i:w^{(2)}\in C'^{(2)}\}|$.

Bounds (using matchings and $|R|\le k$): $p_0\le 4nk$ (per $u$: one $C_1$ in $\mathcal{H}_i$, $\le k$ choices of $(u,C_2)$, each pair gives $4$ half clauses); $p_1\le 8k$ ($2$ choices of $v$ from $C$, one $C_i\ni v$ with $|C_i|=3$, $2$ choices of $u=C_i\setminus\{v\}$, $\le k$ edges $(u,C_2)$, $2$ choices of $w$); $p_2\le 8k$ (symmetric). Hence $\#\{\text{bad }Q\}\le 4nk\binom{2n-6}{\ell-4}+16k\binom{2n-5}{\ell-3}$, and
$$\frac{4nk\binom{2n-6}{\ell-4}+16k\binom{2n-5}{\ell-3}}{\binom{2n-4}{\ell-2}}=4nk\frac{(\ell-2)(\ell-3)}{(2n-4)(2n-5)}+16k\frac{\ell-2}{2n-4}\le\tfrac12,$$
since $\ell\le(\sqrt{n/k})/c$ and $k\le\sqrt{nk}$ (as $k\le n$). $\square$

<a id="pdf-b372a20892ce-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.95 -->
Subsection proving `lem:degbound` and `lem:specbound` (the spectral norm bound).

<a id="pdf-b372a20892ce-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.93 -->
**Proof of Lemma (lem:degbound).** Fix $i \in L$; show each row/column of $B_i$ has at most $2d$ nonzero entries. A nonzero row/column $S$ contains at most one half clause from $P_i$. If $(C,C')$ is a derived clause with $S \overset{C,C'}{\leftrightarrow} T$, then $S$ contains a half clause of $P_i$ inside $C^{(1)} \oplus C'^{(2)}$. Since $S$ has at most one half clause, the nonzero entries of row $S$ are bounded by the maximum over half clauses of the number of derived clauses $(C,C')$ containing that half clause, which is $2d$: fixing $v^{(1)}$ and $w^{(2)}$, at most one clause $C \in \mathcal{H}_i$ contains $v$; two choices for $u \in C \setminus \{v\}$; the second clause is $(u,C') \in \mathcal{H}_j$, $j \in R$, with $C'$ containing $w$; at most $d$ choices for $C'$ since at most $d$ hyperedges in $\cup_{i=1}^k \mathcal{H}_i$ contain $\{u,w\}$. Hence $2 \cdot d = 2d$.

<a id="pdf-b372a20892ce-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.94 -->
**Proof of Lemma (lem:specbound).** $A = \sum_{i \in L} b_i A_i$ with $b_i$ i.i.d.\ from $\{\pm 1\}$. By lem:degbound each row/column of $B_i$ has at most $2d$ nonzeros; since $A_i$ zeros out entries of $B_i$, the same holds for $A_i$, so each row/column of $A_i$ has $\ell_1$-norm $\le 2d$ and $\|A_i\|_2 \le 2d$. Thus $\|\sum_{i \in L} A_i A_i^\top\|_2 \le |L|(2d)^2 \le k(2d)^2$ and likewise for $\sum_{i \in L} A_i^\top A_i$. Matrix Khintchine (fact:matrinxkhintchine) gives $\mathbb{E}[\|A\|_2] \le d \cdot O(\sqrt{k \log N})$; since $\log N = O(\ell \log n)$, the lemma follows.

<a id="pdf-b372a20892ce-p010-b004"></a>
<!-- pdf-source: page=10; block=4; confidence=0.95 -->
Section proving existing LDC lower bounds via the connection between LDCs and CSP refutation.

<a id="pdf-b372a20892ce-p010-b005"></a>
<!-- pdf-source: page=10; block=5; confidence=0.96 -->
**Theorem (thm:knownlowerbound).** Let $\mathcal{C} : \{\pm 1\}^k \to \{\pm 1\}^n$ be $(q,\delta,\eps)$-locally decodable for constant $q \ge 2$. Then: (1) if $q$ is even, $k \le n^{1-2/q}\, O((\log n)/\eps^4 \delta^2)$; (2) if $q$ is odd, $k \le n^{1-2/(q+1)}\, O((\log n)/\eps^4 \delta^2)$.

<a id="pdf-b372a20892ce-p010-b006"></a>
<!-- pdf-source: page=10; block=6; confidence=0.90 -->
**Proof.** By fact:normalform it suffices to prove for $(q,\delta,\eps)$-normally decodable $\mathcal{C} : \{\pm 1\}^k \to \{\pm 1\}^n$ that (1) $k \le n^{1-2/q} O((\log n)/\eps^2\delta^2)$ for $q$ even, and (2) $k \le n^{1-2/(q+1)} O((\log n)/\eps^2\delta^2)$ for $q$ odd. Any $\mathcal{C}$ can be transformed into $\mathcal{C}'$ that is $(q+1,\delta/2,\eps)$-normally decodable, so it suffices to handle even $q$; the odd case can be done directly with asymmetric matrices (see remark:oddmatrix), not presented.

<a id="pdf-b372a20892ce-p010-b007"></a>
<!-- pdf-source: page=10; block=7; confidence=0.95 -->
**Claim.** If $\mathcal{C} : \{\pm 1\}^k \to \{\pm 1\}^n$ is $(q,\delta,\eps)$-normally decodable, then there is a code $\mathcal{C}' : \{\pm 1\}^k \to \{\pm 1\}^{2n}$ that is $(q+1,\delta/2,\eps)$-normally decodable.

<a id="pdf-b372a20892ce-p010-b008"></a>
<!-- pdf-source: page=10; block=8; confidence=0.94 -->
**Proof.** Set $\mathcal{C}'(b) = \mathcal{C}(b)\| 1^n$ (original encoding concatenated with $n$ ones). For each $\mathcal{H}_i$ pick an arbitrary ordering $\pi_i : \mathcal{H}_i \to [n]$ and set $\mathcal{H}'_i = \{C \cup \{n + \pi_i(C)\} : C \in \mathcal{H}_i\}$: each hyperedge gets a distinct appended new coordinate, so $\mathcal{H}'_i$ stays a matching. Then $\mathcal{C}'$ is $(q+1,\delta/2,\eps)$-normally decodable.

<a id="pdf-b372a20892ce-p010-b009"></a>
<!-- pdf-source: page=10; block=9; confidence=0.90 -->
It remains to show for $(q,\delta,\eps)$-normally decodable $\mathcal{C}$ with $q$ even that $n \ge \tilde\Omega(k^{q/(q-2)})$ for $q \ge 4$ and $n \ge \exp(\Omega(k))$ for $q=2$. WLOG all $\mathcal{H}_i$ have size exactly $\delta n$. Construct a $q$-XOR instance for $\mathcal{C}'$: for $b \in \{\pm 1\}^k$, $\Psi_b$ has variables $x \in \{\pm 1\}^n$ and constraints $\prod_{v \in C} x_v = b_i$ for $i \in [k], C \in \mathcal{H}_i$. Let $m := \sum_{i=1}^k |\mathcal{H}_i|$, $\psi_b(x) := \frac{1}{m}\sum_{i=1}^k b_i \sum_{C \in \mathcal{H}_i} \prod_{v \in C} x_v$, and $\val(\psi_b) := \max_x \psi_b(x)$. def:normalLDC implies $\mathbb{E}_b[\val(\psi_b)] \ge 2\eps$. It remains to upper bound $\mathbb{E}_b[\val(\psi_b)]$ via a matrix $A$ (depending on $b$, suppressed) with $\|A\|_2$ related to $\val(\psi_b)$, then bounding $\mathbb{E}_b[\|A\|_2]$.

<a id="pdf-b372a20892ce-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.95 -->
**Definition (def:kikuchiqeven).** Let $\ell := n^{1-2/q}/c$ for an absolute constant $c \ge e^{16}$, and $N := \binom{n}{\ell}$. For each $q$-uniform matching $\mathcal{H}_i$, define $A_i \in \mathbb{R}^{N \times N}$ indexed by $S,T \in \binom{[n]}{\ell}$ with $A_i(S,T)=1$ iff (1) $S \oplus T = C \in \mathcal{H}_i$, and (2) $|S \oplus C'| \ne \ell$ and $|T \oplus C'| \ne \ell$ for every $C' \in \mathcal{H}_i$ with $C' \ne C$; otherwise $A_i(S,T)=0$. Set $A := \sum_{i=1}^k b_i A_i$.

<a id="pdf-b372a20892ce-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.93 -->
**Remark (remark:oddmatrix).** For odd $q$, use $A_i$ indexed by rows $S \in \binom{[n]}{\ell}$ and columns $T \in \binom{[n]}{\ell+1}$, with $A_i(S,T)=1$ if $S \oplus T = C \in \mathcal{H}_i$ and $|S \oplus C'| \ne \ell+1$, $|T \oplus C'| \ne \ell$ for all $C' \ne C$ in $\mathcal{H}_i$; again $A = \sum_{i=1}^k b_i A_i$.

<a id="pdf-b372a20892ce-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.95 -->
**Lemma (lem:qevenrowpruning).** There is an integer $D$ such that: fixing $i \in [k]$ and $A_i$ from def:kikuchiqeven, for any $C \in \mathcal{H}_i$ the number of pairs $(S,T)$ with $S \oplus T = C$ and $A_i(S,T)=1$ is exactly $D$. Moreover $D/N \ge \frac{1}{2}\binom{q}{q/2} e^{-3q} (\ell/n)^{q/2}$.

<a id="pdf-b372a20892ce-p011-b004"></a>
<!-- pdf-source: page=11; block=4; confidence=0.90 -->
Proof of lem:qevenrowpruning postponed. As in sec:3xor, $\val(\psi_b) \le \frac{N}{mD}\|A\|_2$ with $D$ from lem:qevenrowpruning and $m := \sum_{i=1}^k |\mathcal{H}_i|$. It remains to bound $\mathbb{E}_b[\|A\|_2]$.

<a id="pdf-b372a20892ce-p011-b005"></a>
<!-- pdf-source: page=11; block=5; confidence=0.96 -->
**Lemma (lem:qevenspecbound, spectral norm bound).** $\mathbb{E}_{b \in \{\pm 1\}^k}[\|A\|_2] \le O(\sqrt{k \ell \log n})$.

<a id="pdf-b372a20892ce-p011-b006"></a>
<!-- pdf-source: page=11; block=6; confidence=0.95 -->
**Proof.** Apply Matrix Khintchine to $A = \sum_{i=1}^k b_i A_i$. Since the $\ell_1$-norm of any row/column of $A_i$ is at most $1$, $\|A_i\|_2 \le 1$, so $\|\sum_{i=1}^k A_i^2\|_2 \le \sum_{i=1}^k \|A_i\|_2^2 \le k$. Hence $\mathbb{E}[\|A\|_2] \le O(\sqrt{k \log N})$, and $\log_2 N \le \ell \log_2 n$ finishes the proof.

<a id="pdf-b372a20892ce-p011-b007"></a>
<!-- pdf-source: page=11; block=7; confidence=0.93 -->
By lem:qevenspecbound, $2\eps \le \mathbb{E}_b[\val(\psi_b)] \le \frac{1}{mD} N\, O(\sqrt{k\ell \log n})$. With $|\mathcal{H}_i| = \delta n$, $m = \delta n k$, so $\eps \le \frac{N}{\delta nk D} O(\sqrt{k\ell \log n}) \le \frac{1}{\delta nk}(n/\ell)^{q/2} O(\sqrt{k\ell \log n}) \le \frac{1}{\delta} O\big(\sqrt{\tfrac{n^{1-2/q}}{k}\log n}\big)$, using $\ell = n^{1-2/q}/c$ and the $D/N$ bound. Conclude $k \le n^{1-2/q} O(\log n)/\eps^2\delta^2$.

<a id="pdf-b372a20892ce-p011-b008"></a>
<!-- pdf-source: page=11; block=8; confidence=0.93 -->
**Proof of Lemma (lem:qevenrowpruning).** Count is independent of $C$: for $C' \ne C$ in $\mathcal{H}_i$ (disjoint, matching), take a bijection $\pi$ between $C$ and $C'$ extended by identity elsewhere; $\pi$ maps valid pairs for $C$ to valid pairs for $C'$. By symmetry $D$ depends only on $|\mathcal{H}_i|, q, n$, and since $|\mathcal{H}_i| = \delta n$, $D$ is independent of $i$. Lower bound: $S \oplus T = C$ iff $S = C_S \cup Q$, $T = C_T \cup Q$ with $C_S, C_T \subseteq C$ disjoint of size $q/2$, $C = C_S \cup C_T$, $Q \subseteq [n]\setminus C$ of size $\ell - q/2$. If for some $C' \ne C$ either $|S \oplus C'| = \ell$ or $|T \oplus C'| = \ell$, then $|Q \cap C'| = q/2$. Hence $D \ge \binom{q}{q/2}\binom{n-q}{\ell-q/2} - |\mathcal{H}_i|\binom{q}{q/2}^2\binom{n-2q}{\ell-q}$. By fact:binomialratio, $D/N \ge \binom{q}{q/2}e^{-3q}(\ell/n)^{q/2} - n\binom{q}{q/2}^2 e^{3q}(\ell/n)^q = \binom{q}{q/2}e^{-3q}(\ell/n)^{q/2}\big(1 - n\,2^q e^{6q}(\ell/n)^{q/2}\big) \ge \frac{1}{2}\binom{q}{q/2}e^{-3q}(\ell/n)^{q/2}$, using $\ell \le n^{1-2/q}/e^{16}$.

<a id="pdf-b372a20892ce-p011-b009"></a>
<!-- pdf-source: page=11; block=9; confidence=0.90 -->
Acknowledgements: thanks to anonymous reviewers, Tim Hsieh, and Sidhanth Mohanty. (Bibliography follows.)

<a id="pdf-b372a20892ce-p011-b010"></a>
<!-- pdf-source: page=11; block=10; confidence=0.95 -->
Appendix section: improved lower bounds for $3$-LDCs over larger alphabets.

<a id="pdf-b372a20892ce-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.92 -->
The appendix extends the main theorem (mthm:main) to $3$-query LDCs over larger alphabets by combining it with standard results from [KT00, KdW04].

<a id="pdf-b372a20892ce-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.95 -->
**Definition (def:general-ldc).** Given positive integer $q$, constants $\delta,\eps > 0$, and alphabet $\Sigma$, a code $\mathcal{C} : \{\pm 1\}^k \to \Sigma^n$ is $(q,\delta,\eps)$-locally decodable if there is a randomized decoder $\Dec$ with oracle access to $y \in \Sigma^n$, taking input $i \in [k]$, such that (1) $\Dec$ makes at most $q$ queries to $y$, and (2) for all $b \in \{\pm 1\}^k$, $i \in [k]$, and $y \in \Sigma^n$ with $\Delta(y,\mathcal{C}(b)) \le \delta n$, $\Pr[\Dec^y(i) = b_i] \ge \tfrac{1}{2} + \eps$.

<a id="pdf-b372a20892ce-p012-b003"></a>
<!-- pdf-source: page=12; block=3; confidence=0.96 -->
**Theorem (thm:main-gen-alpha).** Let $\mathcal{C} : \{\pm 1\}^k \to \Sigma^n$ be a $(3,\delta,\eps)$-LDC. Then $k^3 \le |\Sigma|^{41} n \cdot O(\log^6(|\Sigma| n)/\eps^{32}\delta^{16})$. In particular, if $\delta,\eps$ are constants and $|\Sigma| \le n$, then $n \ge \Omega(k^3/(|\Sigma|^{41}\log^6 k))$.

<a id="pdf-b372a20892ce-p012-b004"></a>
<!-- pdf-source: page=12; block=4; confidence=0.00 -->
**Lemma (lemma:gen-normal-form).** Let $\mathcal{C} : \{\pm 1\}^k \to \Sigma^n$ be a $(3,\delta,\eps)$-LDC. Then there is a binary code $\mathcal{C}' : \{\pm 1\}^k \to \{\pm 1\}^{n'}$ with $n' \le 4n|\Sigma|$ and $q$-uniform matchings $\mathcal{H}'_1,\dots,\mathcal{H}'_k$ over $n'$ vertices such that for all $i$, $|\mathcal{H}'_i| \ge \eps\delta n'/(4q^2|\Sigma|)$, and for any $C \in \mathcal{H}'_i$, $\Pr_b[b_i = \oplus_{v \in C}\mathcal{C}(b)_v] \ge \tfrac{1}{2} + \tfrac{\eps}{8|\Sigma|^{3/2}}$. (Then applying mthm:main to this normal-form code yields thm:main-gen-alpha, with better $\eps$-dependence for a normal-form initial LDC.)

<a id="pdf-b372a20892ce-p012-b005"></a>
<!-- pdf-source: page=12; block=5; confidence=0.93 -->
**Lemma (Theorem 1 + Lemma 4 of [KT00]).** Let $\mathcal{C} : \{\pm 1\}^k \to \Sigma^n$ be a $(q,\delta,\eps)$-LDC. Then there exist $q$-uniform matchings $\mathcal{H}_1,\dots,\mathcal{H}_k$ over $[n]$ with $|\mathcal{H}_i| \ge \eps\delta n/q^2$ for all $i$, and for any $C \in \mathcal{H}_i$ a function $f_C : \Sigma^q \to \{\pm 1\}$ with $\Pr_b[b_i = f_C(\mathcal{C}(b)|_C)] \ge \tfrac{1}{2} + \tfrac{\eps}{2}$. (The [KT00] statement gives size at most $q$; padding each codeword with $n$ zeros makes sizes exactly $q$.)

<a id="pdf-b372a20892ce-p012-b006"></a>
<!-- pdf-source: page=12; block=6; confidence=0.93 -->
**Lemma (Lemma 2 of [KdW04]).** Let $q \ge 2$ and $\mathcal{C} : \{\pm 1\}^k \to \Sigma^n$ a code. Let $\mathcal{H}_1,\dots,\mathcal{H}_k$ be $q$-uniform matchings over $[n]$ with $|\mathcal{H}_i| \ge \eps\delta n/q^2$ and for each $C \in \mathcal{H}_i$ a function $f_C : \Sigma^q \to \{\pm 1\}$ with $\Pr_b[b_i = f_C(\mathcal{C}(b)|_C)] \ge \tfrac{1}{2} + \tfrac{\eps}{2}$. Then there is a binary code $\mathcal{C}' : \{\pm 1\}^k \to \{\pm 1\}^{n'}$ with $n' \le 4n|\Sigma|$ and $q$-uniform matchings $\mathcal{H}'_1,\dots,\mathcal{H}'_k$ over $n'$ with $|\mathcal{H}'_i| \ge \eps\delta n'/(4q^2|\Sigma|)$, such that for any $C \in \mathcal{H}'_i$, $\Pr_b[b_i = \oplus_{v \in C}\mathcal{C}'(b)_v] \ge \tfrac{1}{2} + \tfrac{\eps}{2^q|\Sigma|^{q/2}}$.

<a id="pdf-b372a20892ce-p012-b007"></a>
<!-- pdf-source: page=12; block=7; confidence=0.92 -->
Combining lemma:kt and lemma:kdw yields lemma:gen-normal-form; thm:main-gen-alpha then follows by applying mthm:main. It remains to prove lemma:kdw, using Boolean-analysis notation from [OD14].

<a id="pdf-b372a20892ce-p012-b008"></a>
<!-- pdf-source: page=12; block=8; confidence=0.00 -->
**Proof of Lemma (lemma:kdw).** Choose $\ell \in \mathbb{N}$ with $|\Sigma| < 2^\ell \le 2|\Sigma|$, set $n' := n 2^{\ell+1}$, and WLOG $\Sigma \subseteq \{\pm 1\}^\ell$. Use the first-order Reed-Muller encoding $\mathrm{RM}_1 : \{\pm 1\}^\ell \to \{\pm 1\}^{2^{\ell+1}}$, $\mathrm{RM}_1(\sigma) = (\langle a,\sigma\rangle + t)_{a \in \{\pm 1\}^\ell, t \in \{\pm 1\}}$, and define $\mathcal{C}'(b) := (\mathrm{RM}_1(\mathcal{C}(b)_1),\dots,\mathrm{RM}_1(\mathcal{C}(b)_n))$. For $i \in [k]$, $C = \{v_1,\dots,v_q\} \in \mathcal{H}_i$, extend $f_C$ to $(\{\pm 1\}^\ell)^q$ by $f_C(\sigma)=0$ off $\Sigma$, and set $x := \mathcal{C}(b)$. Then $\Pr_b[b_i = f_C(\mathcal{C}(b)|_C)] \ge \tfrac12+\tfrac\eps2 \iff \mathbb{E}_b[b_i f_C(x_{v_1},\dots,x_{v_q})] \ge \eps$. With Fourier expansion $f_C(y_1,\dots,y_q) = \sum_{S_1,\dots,S_q \subseteq [\ell]} \widehat{f_C}(S_1,\dots,S_q)\prod_{t=1}^q\prod_{j \in S_t}(y_t)_j$, Cauchy-Schwarz and Parseval give $\eps^2 \le \mathbb{E}_b[b_i f_C]^2 \le \big(\sum \widehat{f_C}^2\big)\big(\sum_{S} \mathbb{E}_b[b_i \prod_t\prod_{j \in S_t}(x_{v_t})_j]^2\big) = \sum_{S} \mathbb{E}_b[\cdots]^2 \le 2^{q\ell}\max_{S}\mathbb{E}_b[\cdots]^2$. Hence there are $R_1^C,\dots,R_q^C \subseteq [\ell]$ and $t_C \in \{\pm 1\}$ with $(-1)^{t_C}\mathbb{E}_b[b_i \prod_t\prod_{j\in S_t}(x_{v_t})_j] \ge \eps/2^{q\ell/2} \ge \eps/(2^{q-1}|\Sigma|^{q/2})$. Reverting to $\{\pm 1\}$: $\Pr_b[t_C + \sum_{i=1}^q\langle \mathbf{1}_{R_1^C},x_{v_i}\rangle = b_i] \ge \tfrac12 + \tfrac{\eps}{2^q|\Sigma|^{q/2}}$. Form the query set $C' := \{(v_1,(\mathbf{1}_{R_1^C},t_C)),(v_2,(\mathbf{1}_{R_2^C},0)),\dots,(v_q,(\mathbf{1}_{R_q^C},0))\}$ recovering $b_i$ w.p. $\tfrac12+\eps/(2^q|\Sigma|^{q/2})$; these define $\mathcal{H}'_1,\dots,\mathcal{H}'_k$. Since the map is a bijection on query sets, $|\mathcal{H}_i| = |\mathcal{H}'_i| \ge \eps\delta n/q^2 \ge \eps\delta n'/(4q^2|\Sigma|)$, and it preserves disjointness and size so the $\mathcal{H}'_i$ are $q$-uniform matchings.

<a id="pdf-b372a20892ce-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.95 -->
**Section (Appendix).** Our Proof as a Black-box Reduction to 2-LDC Lower Bounds. Reinterprets the proof of the main theorem for *linear* 3-LDCs as a black-box reduction to known linear 2-LDC lower bounds.

<a id="pdf-b372a20892ce-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.90 -->
Given a linear 3-LDC $\mathcal{C}$, the transformation produces two linear codes $\mathcal{C}_2,\mathcal{C}_3$ (from the 2-XOR instance $g_b$ and 3-XOR instance $f_b$), with the guarantee that at least one is a linear 2-LDC. Applies only to linear 3-LDCs, but yields better dependence on $\log n$, $\varepsilon$, $\delta$ because linear 2-LDC bounds are stronger than general ones. The intermediate objects are "weak LDCs".

<a id="pdf-b372a20892ce-p013-b003"></a>
<!-- pdf-source: page=13; block=3; confidence=0.00 -->
**Definition (Linear weak LDC).** A code $\mathcal{C}\colon\{0,1\}^k\to\{0,1\}^n$ is a linear $(q,\delta)$-weakly locally decodable code ($(q,\delta)$-wLDC) if $\mathcal{C}$ is linear and there exist $q$-uniform hypergraph matchings $\mathcal{H}_1,\dots,\mathcal{H}_k$ over $[n]$ such that (1) $\sum_{i=1}^k |\mathcal{H}_i| \ge \delta n k$, and (2) for every $i\in[k]$ and every $C\in\mathcal{H}_i$, $\bigoplus_{v\in C}\mathcal{C}(b)_v = b_i$ for all messages $b\in\{0,1\}^k$.

<a id="pdf-b372a20892ce-p013-b004"></a>
<!-- pdf-source: page=13; block=4; confidence=0.90 -->
wLDCs are equivalent to LDCs up to constant factors: a wLDC only requires $\sum_i |\mathcal{H}_i|\ge\delta nk$ instead of $|\mathcal{H}_i|\ge\delta n$ for all $i$. Removing all $\mathcal{H}_i$ with $|\mathcal{H}_i|\le \delta n/2$ (fixing those $b_i=0$) yields $\mathcal{C}'\colon\{0,1\}^{k'}\to\{0,1\}^n$ with $k'\ge\delta k$ and $|\mathcal{H}_i|\ge\delta n/2$ for all $i\in[k']$.

<a id="pdf-b372a20892ce-p013-b005"></a>
<!-- pdf-source: page=13; block=5; confidence=0.97 -->
**Lemma (Lemma 3.3 of [GKST06]).** Any linear $(2,\delta)$-wLDC $\mathcal{C}\colon\{0,1\}^k\to\{0,1\}^n$ satisfies $n \ge 2^{\delta k}$. Used as a black box.

<a id="pdf-b372a20892ce-p013-b006"></a>
<!-- pdf-source: page=13; block=6; confidence=0.95 -->
**Theorem (thm:linreduction).** Let $\mathcal{C}\colon\{0,1\}^k\to\{0,1\}^n$ be a linear $(3,\delta)$-wLDC and $d\in\mathbb{N}$. Then there are codes $\mathcal{C}_2\colon\{0,1\}^{k_2}\to\{0,1\}^n$ and $\mathcal{C}_3\colon\{0,1\}^{k_3}\to\{0,1\}^N$ such that either $\mathcal{C}_2$ is a linear $(2,\Omega(\delta\cdot\frac{d}{d+k}))$-wLDC or $\mathcal{C}_3$ is a linear $(2,\Omega(\delta^2/d))$-wLDC, where $k_2,k_3\ge k/2$, $N=\binom{2n}{\ell}$, and $\ell=\sqrt{n/k}/c$ for an absolute constant $c$.

<a id="pdf-b372a20892ce-p013-b007"></a>
<!-- pdf-source: page=13; block=7; confidence=0.96 -->
**Corollary (cor:linlb).** Let $\mathcal{C}\colon\{0,1\}^k\to\{0,1\}^n$ be a $(3,\delta)$-linear LDC. Then $n \ge \Omega\!\left(\dfrac{\delta^6 k^3}{\log^4 k}\right)$.

<a id="pdf-b372a20892ce-p013-b008"></a>
<!-- pdf-source: page=13; block=8; confidence=0.92 -->
**Proof.** Apply the Theorem with $d=c\log_2 n/\delta$ ($c$ large). If $k\le d$ done; otherwise $k\ge d$. If $\mathcal{C}_2$ is a linear $(2,\Omega(\delta\cdot\frac{d}{d+k}))$-wLDC, the GKST lemma gives $\log_2 n \ge \Omega(\delta dk/(k+d))\ge\Omega(\delta d)$ (since $k+d\le 2k$), contradicting $d=c\log_2 n/\delta$. Hence $\mathcal{C}_3$ is a linear $(2,\Omega(\delta^2/d))$-wLDC, and the lemma gives $O(\sqrt{n/k}\log n)\ge \ell\log_2 n \ge \Omega(\delta^2 k/d)$, yielding $n\ge\Omega(\delta^6 k^3/\log^4 n)$. Since $\log_2 n=\Theta(\log k)$ (else the corollary is trivial), the bound follows. $\square$

<a id="pdf-b372a20892ce-p013-b009"></a>
<!-- pdf-source: page=13; block=9; confidence=0.88 -->
**Proof (of thm:linreduction).** From the $(3,\delta)$-wLDC, take 3-uniform matchings $\mathcal{H}_1,\dots,\mathcal{H}_k$ with $\sum_i|\mathcal{H}_i|\ge\delta nk$ and $\bigoplus_{v\in C}\mathcal{C}(b)_v=b_i$ for $C\in\mathcal{H}_i$. Let $G_1,\dots,G_k,\mathcal{H}'_1,\dots,\mathcal{H}'_k$ be the output of the hypergraph decomposition (lem:decomp) with parameter $d$.

*Constructing $\mathcal{C}_2$:* For $L_2\subseteq[k]$ with $|L_2|\ge k/2$, define $\mathcal{C}_2(b'):=\mathcal{C}(b)$ where $b_i=b'_i$ for $i\in L_2$ and $b_j=0$ otherwise (zero-padding). Claim: if $\sum_i|G_i|\ge\delta nk/2$, some $L_2$ ($|L_2|\ge k/2$) makes $\mathcal{C}_2$ a linear $(2,\Omega(\delta\cdot\frac{d}{d+k}))$-wLDC. Each $G_i$ is a bipartite matching on $[n]\times P$, $P=\{p=(u,v):\deg_{\mathcal{H}}(p)\ge d\}$, $\mathcal{H}=\cup_i\mathcal{H}_i$. By duplicating elements of $P$, assume each $p$ appears in between $d$ and $2d$ edges across the $G_i$. Partition $[k]=L_2\cup R_2$ ($|L_2|\ge k/2$). For $i\in L_2$, let $G'_i$ have edges $E_i=\{(u,v):\exists p\in P, j\in R_2,\ (u,p)\in G_i,(v,p)\in G_j\}$. In expectation over a random partition $\sum_{i\in L_2}|G'_i|\ge\Omega(\delta nkd)$, so such a partition exists.

<a id="pdf-b372a20892ce-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.90 -->
**Proof (cont.).** For any $u\in[n]$ and $i\in L_2$, $u$ has degree $\le 2d+k$ in $G'_i$: at most $2d$ edges $(u,v)$ arise from an edge $(u,p)\in G_i$, and for each $v$ at most $k$ edges $(u,v)$ arise (one per $j\in R_2$ since each $G_j$ is a matching). Hence each $G'_i$ has a matching $M'_i$ with $|M'_i|\ge\Omega(|G'_i|/(d+k))$, giving $\sum_i|M'_i|\ge\Omega(\delta nk\cdot\frac{d}{d+k})$. For $i\in L_2$ and $(u,v)\in M'_i$: $\mathcal{C}_2(b')_u\oplus\mathcal{C}_2(b')_v=b'_i$, since $\mathcal{C}(b)_u\oplus\mathcal{C}(b)_p=b_i$ and $\mathcal{C}(b)_v\oplus\mathcal{C}(b)_p=b_j=0$ (with $j\in R_2$, $(u,p)\in G_i$, $(v,p)\in G_j$). Thus if $\sum_i|G_i|\ge\delta nk/2$ then $\mathcal{C}_2$ is a linear $(2,\Omega(\delta\cdot\frac{d}{d+k}))$-wLDC.

<a id="pdf-b372a20892ce-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.00 -->
**Proof (cont.).** *Constructing $\mathcal{C}_3$:* Let $L_3\subseteq[k]$, $|L_3|\ge k/2$, $\ell=\sqrt{n/k}/c$, and $N=\binom{2n}{\ell}$ identified with $\binom{[n]\times[2]}{\ell}$. Define $\mathcal{C}_3\colon\{0,1\}^{L_3}\to\{0,1\}^N$ by
$$\mathcal{C}_3(b')_S:=\Big(\bigoplus_{u^{(1)}\in S}\mathcal{C}(b)_u\Big)\oplus\Big(\bigoplus_{v^{(2)}\in S}\mathcal{C}(b)_v\Big),$$
where $b_i=b'_i$ for $i\in L_3$, else $0$. Claim: if $\sum_i|\mathcal{H}'_i|\ge\delta nk/2$, some $L_3$ makes $\mathcal{C}_3$ a linear $(2,\Omega(\delta^2/d))$-wLDC. Each $\mathcal{H}'_i$ is a 3-uniform matching with $\deg_{\mathcal{H}'}(\{u,v\})\le d$, $\mathcal{H}'=\cup_i\mathcal{H}'_i$. Partition $[k]=L_3\cup R_3$. With Kikuchi matrices $B_i\in\mathbb{R}^{N\times N}$ (def:kikuchi-matrix), let $G''_i$ have adjacency $B_i$ (edge $(S,T)$ iff $B_i(S,T)\ne0$). By lem:degbound the max degree in $G''_i$ is $\le 2d$, so $G''_i$ has a matching $M''_i$ with $|M''_i|\ge\Omega(|G''_i|/d)$. Since $|\mathcal{H}'|\ge\delta nk/2$, double counting gives $\ge\Omega(\delta^2 nk^2)$ clause pairs $C_1,C_2\in\mathcal{H}'$ with $|C_1\cap C_2|\ge1$. By a random partition and lem:rowpruning, $\sum_i|G''_i|\ge\Omega(D\delta^2 nk^2)$ in expectation, $D=2\binom{2n-\ell}{\ell-4}$. By fact:binomialratio $D/N\ge\Omega(\ell^2/n^2)$, so $\sum_i|M''_i|\ge\Omega(\delta^2 Nk/d)$ (using $\ell=\sqrt{n/k}/c$). For $i\in L_3$, $(S,T)\in M''_i$: $b'_i=\mathcal{C}_3(b')_S\oplus\mathcal{C}_3(b')_T=\mathcal{C}(b)_S\oplus\mathcal{C}(b)_T=b_i\oplus b_j=b'_i$. Thus if $\sum_i|\mathcal{H}'_i|\ge\delta nk/2$ then $\mathcal{C}_3$ is a linear $(2,\Omega(\delta^2/d))$-wLDC.

<a id="pdf-b372a20892ce-p014-b003"></a>
<!-- pdf-source: page=14; block=3; confidence=0.95 -->
**Proof (concl.).** By lem:decomp, either $\sum_i|G_i|\ge\delta nk/2$ or $\sum_i|\mathcal{H}'_i|\ge\delta nk/2$, so at least one of $\mathcal{C}_2,\mathcal{C}_3$ has the desired property. $\square$

<a id="pdf-b372a20892ce-p014-b004"></a>
<!-- pdf-source: page=14; block=4; confidence=0.90 -->
**Remark (rem:linearity).** Linearity of $\mathcal{C}$ is needed: the decoding constraints for $\mathcal{C}_2,\mathcal{C}_3$ come from XORing two clauses $C_1,C_2$, so $C_1\oplus C_2$ decodes $b_i\oplus b_j$; hardcoding $\sim k/2$ of the $b_j$ to $0$ then gives many constraints recovering $b_i$. For nonlinear codes this fails, because individual constraints only decode $b_i,b_j$ *in expectation* over random $b$, so hardcoding bits destroys the expectation guarantee for the derived constraint over the free bits.
