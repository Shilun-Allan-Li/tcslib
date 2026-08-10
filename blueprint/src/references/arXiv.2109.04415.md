<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: 9c5df3bb4a04eeeea67f0c590a5340f72bfc2557b6ea9e626202e500afc9f29a -->

<a id="pdf-9c5df3bb4a04-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.95 -->
# Algorithms and Certificates for Boolean CSP Refutation: "Smoothed is no harder than Random"

Authors: Venkatesan Guruswami (UC Berkeley); Pravesh K. Kothari (Carnegie Mellon University); Peter Manohar (Carnegie Mellon University). Dated September 6, 2023.

<a id="pdf-9c5df3bb4a04-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.95 -->
**Abstract.** Presents an algorithm that strongly refutes smoothed instances of all Boolean CSPs. In the smoothed model (hybrid of worst- and average-case), the input is an arbitrary CSP instance in which only the literal negation patterns are re-randomized with small probability. For an $n$-variable smoothed instance of a $k$-arity CSP, the algorithm runs in $n^{O(\ell)}$ time and w.h.p. bounds the optimum fraction of satisfiable constraints away from $1$, provided the number of constraints is at least $\tilde O(n)\,(n/\ell)^{k/2-1}$. This matches (up to polylog factors in $n$) the running-time vs. constraint-count trade-off of state-of-the-art algorithms for refuting fully random CSP instances [RRS17]. The analysis connects the "randomness-starved" semi-random $k$-XOR setting to the existence of even covers in worst-case hypergraphs; this resolves Feige's 2008 conjecture (an extremal conjecture on even covers in sufficiently dense hypergraphs generalizing the Moore bound for graph girth). Corollary: polynomial-size refutation witnesses exist for arbitrary smoothed CSP instances whose constraint count is a polynomial factor below the "spectral threshold" $n^{k/2}$, extending the random 3-SAT result of Feige, Kim and Ofek [FKO06].

<a id="pdf-9c5df3bb4a04-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.90 -->
Keywords: CSP refutation, smoothed CSPs, even covers. (Funding acknowledgments and NSF disclaimer omitted as non-mathematical.)

<a id="pdf-9c5df3bb4a04-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.85 -->
Table of contents. Section structure: 1. Introduction (1.1 Our results); 2. Overview of Techniques (2.1 random 4-XOR via the Kikuchi matrix of [WAM19]; 2.2 semirandom 4-XOR via row bucketing from [AGK21]; 2.3 Feige's conjecture for 4-uniform hypergraphs; 2.4 refuting semirandom 3-XOR via row pruning; 2.5 handling $k$-XOR for $k=3$ via hypergraph regularity; 2.6 organization); 3. Preliminaries (notation, concentration inequalities, sum-of-squares algorithm); 4. A Hypergraph Decomposition Lemma; 5. Refuting Semirandom Sparse Polynomials over the Hypercube (5.1 regular bipartite polynomials, 5.2 reduction to them); 6. Refuting Regular Bipartite Polynomials (6.1 Kikuchi matrix and algorithm, 6.2 bounding $\|A\|_{\infty\to1}$ proof plan, 6.3 row pruning, 6.4 bounding good rows / Lemma 6.11, 6.5 bounding number of bad rows / Lemma 6.9); 7. Strong CSP Refutation: Smoothed via Semirandom (7.1 proof of Thm 7.4); 8. Proof of Feige's Conjecture: Even Covers in Hypergraphs (8.1 proof of Lemma 8.4); 9. Polynomial-Size Refutation Witnesses Below the Spectral Threshold; Appendix A. Analyzing the [WAM19] approach for random 3-XOR.

<a id="pdf-9c5df3bb4a04-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.97 -->
# 1 Introduction

<a id="pdf-9c5df3bb4a04-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.86 -->
Worst-case landscape for Max $k$-CSPs with $k$-ary Boolean predicates. For a large class [Cha13, MR10], ETH [IP01] implies that for sparse instances ($m > O(n)$ constraints in $n$ variables) no sub-exponential-time approximation beats a random assignment. Fully-dense instances ($m \ge O(n^k)$) admit a PTAS [AKK95], but ETH implies lowering $m$ to $\sim n^{k-1}$ makes the problem APX-hard [FLP16] even for sub-exponential-time algorithms. For $m \le O(n^{k-1})$, it is suspected that even efficiently verifiable certificates of non-vacuous upper bounds on the value (max satisfiable fraction) do not exist.

<a id="pdf-9c5df3bb4a04-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.90 -->
Contrast for random CSPs. Max $k$-CSPs with strictly super-linear $m \ge n^{1.1}$ random constraints admit sub-exponential-time tight refutation algorithms [BM16, AOW15, RRS17], based on spectral methods. When $m \sim \tilde O(n^{k/2}) \ll n^{k-1}$, these yield a PTAS for certifying the instance's value. A fine-grained, predicate-specific and likely sharp trade-off between running time and constraint count is known [BCK15, KMOW17]. Additionally, [FKO06] shows random CSPs admit polynomial-time verifiable certificates of non-trivial upper bounds on the value even at $m \sim n^{k/2-\delta_k}$ — i.e., polynomially below the threshold for efficient refutation.

<a id="pdf-9c5df3bb4a04-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.90 -->
Motivating questions (expository): how does the complexity of CSPs, for both algorithms and certificates, interpolate between the worst-case and random extremes, and are the tools/structural properties governing random-CSP success relevant to more general instances.

<a id="pdf-9c5df3bb4a04-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.83 -->
Smoothed model. Feige [Fei07] (2007) introduced a hybrid worst-case/random model (in the spirit of Spielman–Teng [ST03]): start from an arbitrary (worst-case) instance and independently negate each literal in each clause with small constant probability. Thus the clause structure ($k$-tuples defining constraints) is arbitrary while only a small constant fraction of literal patterns is random. Feige combined semidefinite programming with a combinatorial certificate based on cycles in hypergraphs, proving that polynomial algorithms weakly refute (certify a $1-o_n(1)$ upper bound on value; Definition 1.2) smoothed 3-SAT formulas with $m \ge \tilde O(n^{1.5})$ constraints.

<a id="pdf-9c5df3bb4a04-p003-b006"></a>
<!-- pdf-source: page=3; block=6; confidence=0.90 -->
Feige's techniques appear fundamentally limited to weak refutation and specialized to 3-CSPs. Consequently, there was no known strong refutation algorithm (certifying a $1-\Omega(1)$ upper bound on value) for smoothed 3-SAT, and no known (even weak) refutation algorithm for smoothed instances of any nontrivial 4-CSP.

<a id="pdf-9c5df3bb4a04-p003-b007"></a>
<!-- pdf-source: page=3; block=7; confidence=0.82 -->
This work develops new techniques yielding strong refutation algorithms for all smoothed [CSPs] (sentence continues past supplied text). Footnotes: "random" means variables and literal patterns in each constraint are chosen uniformly and independently; a "tight refutation" algorithm correctly certifies an upper bound on the value within an arbitrarily small additive $\varepsilon$ w.h.p.

<a id="pdf-9c5df3bb4a04-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.85 -->
Concludes a result statement: smoothed Boolean $k$-CSPs admit a (possibly sharp) running-time vs. number-of-constraints trade-off matching fully random $k$-CSPs [RRS17] up to polylog factors. Strong refutation in the 'randomness-starved' smoothed setting is no harder than for fully random instances.

<a id="pdf-9c5df3bb4a04-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.80 -->
**Feige's conjecture (result).** [FKO06] and extensions [Wit17] give efficiently verifiable witnesses of unsatisfiability for fully random $k$-CSPs with $n^{k/2-\delta_k}$ constraints ($\delta_k>0$ constant); for $k>3$ the threshold is $n^{1/4}$. Witnesses are based on *even covers* (hypergraph analogs of cycles). Feige [Fei08] conjectured a trade-off between number of constraints and size of the smallest even cover, generalizing the Moore girth bound [AHL02] to hypergraphs. This work proves Feige's conjecture via a new spectral double-counting argument relating sub-exponential-time smoothed refutation algorithms to existence of even covers, yielding efficiently verifiable unsatisfiability witnesses for smoothed instances of all $k$-CSPs at $m\sim n^{k/2-\delta_k}$ — polynomially below the efficient-refutation threshold for random $k$-CSPs.

<a id="pdf-9c5df3bb4a04-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.90 -->
**Summary.** Worst-case CSP complexity arises from isolated 'islands of pathology': most instances near the worst-case hard ones are essentially as easy as random, for both refutation algorithms and refutation witnesses. Worst-case difficulty is attributable to worst-case literal patterns rather than clause structure.

<a id="pdf-9c5df3bb4a04-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.88 -->
Figure 1 plots the time vs. #constraints trade-off for refuting random and smoothed 3-SAT, alongside approximation schemes for worst-case instances. Contribution: the smoothed case (blue) achieves the same trade-off as random (green); refutation witnesses exist for smoothed instances at $n^{1/4}$ constraints (purple), matching [FKO06]'s random result.

<a id="pdf-9c5df3bb4a04-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.95 -->
## 1.1 Our results

<a id="pdf-9c5df3bb4a04-p004-b006"></a>
<!-- pdf-source: page=4; block=6; confidence=0.82 -->
**Definition 1.1 ($k$-ary Boolean CSPs; random, semirandom, smoothed).** A CSP instance $\phi$ on $n$ variables with $k$-ary predicate $P:\{\pm1\}^k\to\{0,1\}$ is a set of $m$ constraints on $x_1,\dots,x_n\in\{\pm1\}^n$ of the form $P(\xi(C)_1 x_{C_1},\,\xi(C)_2 x_{C_2},\,\dots,\,\xi(C)_k x_{C_k})=1$. Here $C=(C_1,\dots,C_k)$ ranges over a collection $\mathcal H$ of scopes (clause structure) of $k$-tuples of variables with $C_i\neq C_j$, and $\xi:\mathcal H\to\{\pm1\}^k$ are literal negation patterns, one per $C\in\mathcal H$. The value $\mathrm{val}(\phi)$ is the maximum fraction of constraints satisfied by any assignment.

<a id="pdf-9c5df3bb4a04-p004-b007"></a>
<!-- pdf-source: page=4; block=7; confidence=0.90 -->
**Random instance.** $\mathcal H$ is a collection of $m$ i.i.d. uniformly random $k$-tuples, and each $\xi(C)$ is chosen i.i.d. uniformly from $\{\pm1\}^k$.

<a id="pdf-9c5df3bb4a04-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.88 -->
**Figure 1 (caption).** Time vs. #constraints trade-off for refuting random and smoothed 3-SAT and for approximation schemes on worst-case instances; the smoothed case is the paper's contribution, with refutation witnesses shown to exist for smoothed instances at $n^{1/4}$ constraints.

<a id="pdf-9c5df3bb4a04-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.92 -->
**Semirandom instance.** $\mathcal H$ is arbitrary (worst-case) and each $\xi(C)\in\{\pm1\}^k$ is uniformly random and independent.

<a id="pdf-9c5df3bb4a04-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.90 -->
**Smoothed instance.** $\mathcal H$ is arbitrary (worst-case); $\xi(C)$ is obtained from a worst-case $\xi'(C)\in\{\pm1\}^k$ by independently, for each $(C,i)$, setting $\xi(C)_i=\xi'(C)_i$ with probability $0.99$ and $\xi(C)_i=-\xi'(C)_i$ with probability $0.01$. The semirandom model generalizes the random model, and the smoothed model generalizes the semirandom model.

<a id="pdf-9c5df3bb4a04-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.90 -->
**Definition 1.2 (Weak, Strong, Tight refutation algorithms).** A refutation algorithm maps a CSP instance $\phi$ to $\mathrm{alg\text{-}val}(\phi)\in[0,1]$ with $\mathrm{alg\text{-}val}(\phi)\ge\mathrm{val}(\phi)$ for all $\phi$. For a distribution $\mathcal D$ over $\phi$: **weak refutation** means w.h.p. over $\phi\sim\mathcal D$, $\mathrm{alg\text{-}val}(\phi)<1$; **strong refutation** means $\mathrm{alg\text{-}val}(\phi)<1-\delta$ for an absolute constant $\delta>0$; **$\varepsilon$-tight refutation** means $\mathrm{alg\text{-}val}(\phi)<\mathrm{val}(\phi)+\varepsilon$ for a tunable parameter $\varepsilon$.

<a id="pdf-9c5df3bb4a04-p005-b005"></a>
<!-- pdf-source: page=5; block=5; confidence=0.93 -->
### 1.1.1 Algorithms for smoothed refutation

<a id="pdf-9c5df3bb4a04-p005-b006"></a>
<!-- pdf-source: page=5; block=6; confidence=0.90 -->
**Theorem 1 (Smoothed refutation; informal Theorem 7.4).** For every $\ell=\ell(n)$ there is an $n^{O(\ell)}$-time strong refutation algorithm for smoothed CSPs with $m\ge m_0=\tilde O(n)\cdot(n/\ell)^{\,t/2-1}$ constraints. That is, for any CSP instance $\phi$ with $m\ge m_0$ constraints, with probability $0.99$ over the smoothing $\phi_s$ of $\phi$, the algorithm outputs $\mathrm{alg\text{-}val}(\phi_s)\le 1-\delta$ for an absolute constant $\delta>0$.

<a id="pdf-9c5df3bb4a04-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.88 -->
**Degree of uniformity.** $t=t(P)\le k$ is the smallest integer $t\le k$ such that there is no $t$-wise uniform distribution (Definition 7.3) on $\{\pm1\}^k$ supported entirely on the satisfying assignments $P^{-1}(1)\subseteq\{\pm1\}^k$.

<a id="pdf-9c5df3bb4a04-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.92 -->
**Example 1.3 ($k$-SAT).** $P$ is the Boolean OR, so $t(P)=k$ (the uniform distribution on odd-parity strings is supported on $P^{-1}(1)$ and is $(k-1)$-wise uniform). The result gives a polynomial-time algorithm to strongly refute smoothed $k$-SAT whenever $m\ge\tilde O(n^{k/2})$; more generally, for any $\delta>0$, in time $2^{O(n^\delta)}$ it strongly refutes smoothed instances with $\ge\tilde O\!\big(n^{(1-\delta)k/2+\delta}\big)$ constraints.

<a id="pdf-9c5df3bb4a04-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.80 -->
**Example 1.4 (Hadamard predicate).** $P$ on $k=2^{2^q-1}$ bits, with $P(x)=1$ iff $x$ is a codeword of the truncated Hadamard code (truth table of a linear function, excluding the all-zeros function); Hadamard CSPs arise in query-efficient PCPs. Here $t(P)=3\ll k$, so the theorem gives a polynomial-time algorithm to strongly refute the smoothed Hadamard CSP with $\ge\tilde O(n^{1.5})$ constraints, and a $2^{n^\delta}$-time algorithm for instances with $\ge\tilde O(n^{1.5-\delta/2})$ constraints, for all $\delta\in(0,1]$.

<a id="pdf-9c5df3bb4a04-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.82 -->
**Comparison with prior results.** Building on [AOW15, BM16], Raghavendra, Rao and Schramm [RRS17] proved the same trade-off (up to a $\mathrm{polylog}(n)$ factor in $m$) for the simpler case of fully random CSPs; this work extends it to smoothed instances (worst-case clause structure, small random perturbations of worst-case literals). All known efficient refutation algorithms, including this one and [RRS17], can be seen as analyses of the canonical sum-of-squares (SoS) relaxation (Section 3.3) for max $k$-CSP; for random (hence smoothed) CSPs the trade-off is essentially tight [KMOW17, BCK15] for such 'SoS-encapsulated' algorithms. In the more general models: Feige [Fei07] gave weak refutation for smoothed/semirandom 3-SAT (extends to all 3-CSPs but not to strong refutation or 4-CSPs); Abascal, Guruswami and Kothari [AGK21] gave polynomial-time refutation of semirandom instances of all CSPs (the $\ell=O(1)$ extreme point of Theorem 1's trade-off). Theorem 1 relies on their *row bucketing* idea plus several new ideas.

<a id="pdf-9c5df3bb4a04-p006-b005"></a>
<!-- pdf-source: page=6; block=5; confidence=0.78 -->
**Algorithms for semirandom $k$-XOR.** The main technical result is an algorithm for *tight* refutation of semirandom $k$-XOR; Theorem 1 follows by a blackbox reduction (Section 7) using a dual polynomial from [AOW15]. A $k$-XOR instance $\phi$ is described by an arbitrary $k$-uniform hypergraph $\mathcal H$ and right-hand sides $b_C\in\{\pm1\}$ for each $C\in\mathcal H$, where (in Definition 1.1's notation) $b_C=\prod_{i=1}^k\xi(C)_i$. One associates to $\phi$ a homogeneous degree-$k$ polynomial $\phi(x)$ (definition continues beyond this page).

<a id="pdf-9c5df3bb4a04-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.82 -->
Defines the advantage polynomial on the hypercube $\{\pm1\}^n$:
$$\phi_0(x) = \tfrac{1}{m}\sum_{C\in\mathcal H} b_C \prod_{i\in C} x_i,$$
the "advantage over $\tfrac12$" of assignment $x$. The instance value equals $\tfrac12 + \tfrac12\max_{x\in\{\pm1\}^n}\phi_0(x)$; **tight refutation** means certifying $\phi_0(x)\le\varepsilon$ for arbitrary $\varepsilon>0$.

<a id="pdf-9c5df3bb4a04-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.92 -->
**Theorem 1.5 (Tight refutation of semirandom $k$-XOR; informal Thm 5.1).** For every $k\in\mathbb N$, $\ell\ge\ell_0(n)$, and $\varepsilon>0$, there is an $n^{O(\ell)}$-time $\varepsilon$-tight refutation algorithm for homogeneous degree-$k$ polynomials, succeeding with probability $\ge 0.99$ over coefficients drawn i.i.d. uniform on $\{-1,1\}$, whenever the associated hypergraph $\mathcal H$ has $m\ge n\,(n/\ell)^{k/2-1}\cdot\mathrm{poly}(\log n/\varepsilon)$ hyperedges. In particular, for every $\delta>0$ this yields a $2^{O(n^{\delta})}$-time $\varepsilon$-tight refutation for semirandom $k$-XOR with $m\gg\tilde O(n)\cdot n^{(1-\delta)(k/2-1)}\cdot\mathrm{poly}(1/\varepsilon)$ constraints.

<a id="pdf-9c5df3bb4a04-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.78 -->
Compresses the technique comparison: the $m$–$\ell$ trade-off matches (up to $\mathrm{polylog}(n)$ factors in $m$) that for fully random $k$-XOR [RRS17], but methods must differ since [RRS17] and predecessors [CGL04, BM16, AOW15] exploit hypergraph randomness via the spectral norm of a symmetric tensor power of the canonical matrix (trace moment method). [WAM19] simplified this using the Kikuchi matrix for even-$k$ random $k$-XOR; their proposed odd-$k$ generalization fails (Appendix A). [Ahn20] simplified aspects of [RRS17]. For semirandom $k$-XOR, [AGK21] handled the extreme point $\ell=O(1)$ via the $\infty\to1$ norm of the canonical matrix, reducing to $3$-XOR through row bucketing by "butterfly degree" plus a pseudorandom-vs-structured decomposition. This work builds on [AGK21]: for even $k$ the [WAM19] Kikuchi matrix with generalized butterfly-degree bucketing gives the right trade-off; odd $k$ needs a new Kikuchi-matrix variant whose spectral norm is provably too large even for random instances.

<a id="pdf-9c5df3bb4a04-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.82 -->
For odd $k$, instead of the full matrix's spectral norm (too large), the method uses the spectral norm after pruning appropriately chosen rows, showing the pruned rows contribute little to the $\infty\to1$ norm. This motivates **regularity** (pseudorandom well-spreadness of hyperedge intersection structure) and a **regularity decomposition lemma**: every $k$-uniform hypergraph decomposes into $k'$-uniform hypergraphs ($k'\le k$) each satisfying regularity, plus "error" hyperedges, such that refuting all the $k'$-XOR instances refutes the original.

<a id="pdf-9c5df3bb4a04-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.90 -->
**§1.1.2 Short refutations below the spectral threshold: proving Feige's conjecture.**

<a id="pdf-9c5df3bb4a04-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.88 -->
**Feige–Kim–Ofek (FKO) [FKO06].** W.h.p. a fully random 3-SAT instance $\psi$ with $m\sim\tilde O(n^{1.4})$ constraints has a polynomial-size witness weakly refuting it (poly-time nondeterministic refutation). All known poly-time deterministic refutation algorithms need $\Omega(n^{1.5})$ constraints (the **spectral threshold**); the fastest known algorithm [RRS17] at $\sim n^{1.4}$ constraints runs in $2^{n^{0.2}}$, matching the SoS lower bound [KMOW17]. Thus poly-time-verifiable refutation witnesses (certifying value $\le 1-o_n(1)$) exist at a density with no known $2^{n^{o(1)}}$-time algorithm. Motivating question: does this existence-vs-efficiency gap persist for semirandom/smoothed instances (worst-case constraint hypergraphs)?

<a id="pdf-9c5df3bb4a04-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.85 -->
Feige's 2008 conjecture [Fei08] on even covers in sufficiently dense hypergraphs generalizes the classical Moore bound on graph girth to hypergraphs; if true, it implies the FKO result for all semirandom and smoothed CSP instances, so FKO would not rely on the underlying hypergraph at all.

<a id="pdf-9c5df3bb4a04-p008-b005"></a>
<!-- pdf-source: page=8; block=5; confidence=0.90 -->
**Definition 1.6 (Even cover and girth).** For a $k$-uniform hypergraph $\mathcal H$ on $[n]$, an **even cover** of length $t$ is a collection of $t$ distinct hyperedges $C_1,\dots,C_t$ of $\mathcal H$ such that every vertex of $[n]$ appears in an even number of the $C_i$. The **girth** of $\mathcal H$ is the length of its smallest even cover.

<a id="pdf-9c5df3bb4a04-p008-b006"></a>
<!-- pdf-source: page=8; block=6; confidence=0.92 -->
**Conjecture 1.7 (Feige's conjecture; Conj. 1.2 of [Fei08]).** Every $k$-uniform hypergraph $\mathcal H$ on $[n]$ with $m\ge m_0 = O(n)\,(n/\ell)^{k/2-1}$ hyperedges has an even cover of length $O(\ell\log n)$.

<a id="pdf-9c5df3bb4a04-p008-b007"></a>
<!-- pdf-source: page=8; block=7; confidence=0.80 -->
**History, $k=2$.** For $k=2$ an even cover is a 2-regular subgraph (a union of cycles), so the conjecture reduces to the maximum-girth question for a graph on $n$ vertices with $nd/2$ edges (parameter $d$).

<a id="pdf-9c5df3bb4a04-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.85 -->
**History (cont.).** [AHL02]: any graph on $n$ vertices with $nd/2$ edges ($d>2$) has a cycle of length $\le c\log_{d-1} n$ with $c\le2$; the best girth lower bound is $c\log_{d-1} n$ with $c\ge 4/3$ via Ramanujan graphs [Mar88, LPS88]; tight $c$ is open. Hypergraphs: [NV08] proved the conjecture for even $k$ and $\ell=O(1)$ (coding view: hyperedges as $\mathbb F_2$ parity-check columns, even cover = sparse linear dependency, yielding rate–distance trade-offs for column-sparse codes); for odd $k$, $\ell=O(1)$ bounds were made essentially optimal in [Fei08]. For $\ell\gg1$ and 3-uniform hypergraphs, [AF09, Lem. 3.3] showed hypergraphs with $\tilde O(n^{2}/\ell)$ hyperedges have an even cover of size $\ell$ (off by $\sim\sqrt n$ in $m$); [JHL$^+$12] showed size-$O(1/\varepsilon)$ even covers when $m\gg n^{1.5+\varepsilon}$ (and $m\gg n^{k/2}$ in general); [FW16] proved variant "generalized girth" results. Prior to this work the conjecture was known only for $\ell=O(1)$; for larger $\ell$ only the combinatorial [FW16] approach existed. This work proves it (up to $\mathrm{poly}\log n$ slack in $m$) via a new **spectral double counting** argument.

<a id="pdf-9c5df3bb4a04-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.72 -->
**Theorem 2 (Feige's conjecture is true; informal Thm 8.2).** For every $k\in\mathbb N$ and $\ell\ge\ell_0(n)$, every $k$-uniform hypergraph $\mathcal H$ with $m\ge m_0 = \tilde O(n)\,(n/\ell)^{k/2-1}$ hyperedges has an even cover of size $O(\ell\log n)$.

<a id="pdf-9c5df3bb4a04-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.80 -->
The spectral double-counting argument is derived from the Kikuchi-matrix analysis for smoothed refutation; the proof of Thm 8.2 mirrors the refutation-algorithm analysis, giving a tight connection between even covers in $\mathcal H$ and simple cycles (hence the spectral norm of the adjacency matrix) in the associated "Kikuchi graph" (§2.3). Footnote: Hsieh and Mohanty later applied this technique to the non-backtracking walk matrix to recover the sharpest known Moore bound for irregular graphs [AHL02].

<a id="pdf-9c5df3bb4a04-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.85 -->
Combining Theorem 2 with the smoothed refutation algorithms (Theorem 1) gives a generalization of FKO: a poly-time nondeterministic refutation algorithm for smoothed instances of all $k$-ary CSPs with constraint count $m$ polynomially below the spectral threshold $n^{k/2}$.

<a id="pdf-9c5df3bb4a04-p009-b005"></a>
<!-- pdf-source: page=9; block=5; confidence=0.85 -->
**Theorem 3 (informal Thm 9.2).** There is a nondeterministic polynomial-time algorithm that weakly refutes smoothed instances of any $k$-CSP with $m\ge m_0 = \tilde O\!\big(n^{\,k/2-\,(k-2)/(2(k+8))}\big)$ constraints; for the special case $k=3$, $m_0=\tilde O(n^{1.4})$.

<a id="pdf-9c5df3bb4a04-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.95 -->
## 2 Overview of our Techniques

<a id="pdf-9c5df3bb4a04-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.82 -->
Expository roadmap. The section gives near-complete proofs of special cases. It first treats refuting **semirandom even-arity k-XOR** (simpler), showcasing two ideas: (1) the power of the Kikuchi matrix, which combined with the row-bucketing idea of [AGK21] resolves even-arity k-XOR — the Kikuchi matrix was introduced by [WAM19] to reprove [RRS17] for fully random even-arity k-XOR and left the odd-arity case open, and their suggested approach fails (shown in Appendix A); and (2) the connection between "Kikuchi matrix refutations" and **even covers in hypergraphs**, used to give a one-page proof of Feige's conjecture for even k. For odd arity (illustrated via 3-XOR, known to be harder [CGL04, BM16, AOW15]) the authors introduce a new Kikuchi-matrix variant, row pruning combined with row bucketing, and a new regularity decomposition for arbitrary hypergraphs. Feige's conjecture for odd k mirrors the even argument but uses the trace moment method (not matrix Bernstein) to bound spectral norms. The smoothed-to-semirandom reduction is deferred to Section 7.

<a id="pdf-9c5df3bb4a04-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.85 -->
### 2.1 Random 4-XOR via the Kikuchi matrix of [WAM19]

Goal: define the Kikuchi matrix and show it yields a simple refutation algorithm with optimal trade-off for random even-arity k-XOR; focus on k = 4.

<a id="pdf-9c5df3bb4a04-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.92 -->
**Definition 2.1 (Kikuchi Matrix).** Let N = C(n, ℓ). For a 4-XOR instance given by hypergraph ℋ and signs b_C for C ∈ ℋ, define A_C ∈ ℝ^{N×N} indexed by all size-ℓ subsets of [n], with entry at (S, T), for S, T ∈ C([n], ℓ), equal to b_C if S △ T = C and 0 otherwise (△ = symmetric difference). The level-ℓ Kikuchi matrix of the instance is A = Σ_{C∈ℋ} A_C.

<a id="pdf-9c5df3bb4a04-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.90 -->
**Quadratic forms.** Let φ(x) := (1/m) Σ_{C∈ℋ} b_C ∏_{i∈C} x_i. A nonzero entry (S, T) of A requires S △ T to be a clause C, which forces |S ∩ C| = 2, |T ∩ C| = 2, and |S ∩ T| = ℓ − 2; hence each b_C appears in C(4,2)·C(n−4, ℓ−2) entries of A. Let x^{⊙ℓ} be the C(n,ℓ)-dimensional vector whose S-th entry is ∏_{i∈S} x_i. Then

(2.1)  C(4,2)·C(n−4, ℓ−2)·φ(x) = (1/m)·(x^{⊙ℓ})^⊤ A x^{⊙ℓ}.

For x ∈ {±1}^n, ‖x^{⊙ℓ}‖² = N, giving the certificate

(2.2)  max_{x∈{±1}^n} φ(x) ≤ [C(n,ℓ)/(6m·C(n−4,ℓ−2))]·‖A‖_2 ≤ O(n²/(mℓ²))·‖A‖_2,

where ‖A‖_2 is the spectral norm (and 6 = C(4,2)). Thus if ‖A‖_2 ≤ Õ(ℓ) whp over ℋ and the b_C, then whenever m ≫ Õ(n²/ℓ) the certificate gives φ(x) ≤ 0.01 for all x ∈ {±1}^n.

<a id="pdf-9c5df3bb4a04-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.90 -->
**Fact 2.2 (Matrix Bernstein Inequality).** Let M_1, M_2, … be independent random N×N matrices with mean 0 and ‖M_i‖_2 ≤ R almost surely. Let σ² = max{ ‖E[Σ_i M_i M_i^⊤]‖_2, ‖E[Σ_i M_i^⊤ M_i]‖_2 } be the variance term. Then with probability at least 1 − 1/(10 n^{100}),

‖Σ_i M_i‖_2 ≤ O(R log N + σ√(log N)).

<a id="pdf-9c5df3bb4a04-p011-b004"></a>
<!-- pdf-source: page=11; block=4; confidence=0.90 -->
**Spectral norm of A (setup).** Each row of A_C has at most one nonzero entry, of magnitude 1. Since the spectral norm of a symmetric matrix is at most the maximum ℓ1-norm of its rows, ‖A_C‖_2 ≤ 1.

<a id="pdf-9c5df3bb4a04-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.85 -->
**Spectral norm of A (variance and bound).** Key fact: A_C² is diagonal for every C, since its (S,T) entry Σ_U A_C(S,U)A_C(U,T) is nonzero only if S △ U = U △ T = C, i.e. iff T = S. As A_C²(S,S) ∈ {0,1}, Σ_C A_C²(S,S) = deg(S), where deg(S) := |{C : |S ∩ C| = 2}|, so the variance term is σ² = max_S deg(S). Each constraint contributes C(4,2)·C(n−4,ℓ−2) nonzero entries, so Σ_S deg(S) = C(4,2)·C(n−4,ℓ−2)·m and the average deg(S) ≈ mℓ²/n² (∼ ℓ when m ∼ n²/ℓ). For a random hypergraph with ∼ n²/ℓ hyperedges, a Chernoff bound gives deg(S) ≤ O(ℓ log n) for all S whp; with N = C(n,ℓ), Matrix Bernstein yields ‖A‖_2 ≤ O(log N) + O(√(ℓ log n · log N)) = Õ(ℓ).

<a id="pdf-9c5df3bb4a04-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.85 -->
### 2.2 Semirandom instances of 4-XOR via row bucketing [AGK21]

**Post-mortem.** After fixing ℋ, the A_C remain independent random matrices (all randomness in the b_C), so Matrix Bernstein still applies; the hypergraph's randomness was used only to establish deg(S) = O(ℓ log n) for every S. Hence the proof extends to semirandom instances whose hypergraph ℋ satisfies deg(S) = O(ℓ log n) for all S. This bound is delicate: deg(S) = Ω(ℓ²) gives no nontrivial refutation, and even deg(S) ∼ ℓ^{1.1} gives a suboptimal trade-off; in arbitrary ℋ, deg(S) can be as large as m (but no larger), and large deg(S) genuinely forces a large spectral norm of A.

<a id="pdf-9c5df3bb4a04-p012-b003"></a>
<!-- pdf-source: page=12; block=3; confidence=0.85 -->
**Key observation.** Building on [AGK21] (poly-time strong refutation of semirandom k-XOR with ≥ Õ(n^{k/2}) constraints): when deg(S) is large the spectral norm of A is high, but the offending large quadratic forms come only from "sparse" vectors (ℓ2 mass concentrated on a small fraction of coordinates), whereas the ±1 vectors of interest are maximally non-sparse ("flat").

<a id="pdf-9c5df3bb4a04-p012-b004"></a>
<!-- pdf-source: page=12; block=4; confidence=0.85 -->
**Row bucketing.** Let d_0 ∼ mℓ²/n² be the average value of deg(S). Partition the C(n,ℓ) row indices into multiplicatively-close buckets ℱ_0, ℱ_1, …, ℱ_t where, for i ≥ 1, ℱ_i = { S : 2^{i−1} d_0 < deg(S) ≤ 2^i d_0 }, and ℱ_0 = { S : deg(S) ≤ d_0 }. Since deg(S) ≤ m and d_0 ≥ 1 (as m ∼ n²/ℓ), one can take t ≤ log₂ m. By Markov's inequality, |ℱ_i| ≤ 2^{−i}·C(n,ℓ) = 2^{−i} N. For each i, j ≤ t, define A_{i,j} as … (text cut off at page end).

<a id="pdf-9c5df3bb4a04-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.72 -->
**Proof (continued).** Define $A_{i/j}$ as the Kikuchi matrix $A$ with all rows outside $\mathcal F_i$ and all columns outside $\mathcal F_j$ zeroed out; then $A=\sum_{i/j}A_{i/j}$. Rows/columns of $A_{i/j}$ where $\deg(S)$ exceeds the average by a factor $2^i$ (resp. $2^j$) are compensated by the reduced number of nonzero rows/columns. For $y\in\{\pm1\}^N$, with $y_{\mathcal F_i}$ the vector zeroing coordinates outside $\mathcal F_i$, Cauchy–Schwarz gives
$$\max_{y\in\{\pm1\}^N} y^\top A_{i/j}y=\max_{y} (y_{\mathcal F_i})^\top A_{i/j}(y_{\mathcal F_j})\le \sqrt{|\mathcal F_i|\,|\mathcal F_j|}\,\|A_{i/j}\|_2. \tag{2.3}$$
Applying Matrix Bernstein: the variance term grows by $\max(2^i,2^j)$ and $\|A_{i/j}\|_2$ by $\max(2^{i/2},2^{j/2})$, while the effective $\ell_2$ norm drops by $2^{-(i+j)/2}$. The trade-off favors the bound, whose dominating term is $A_{0/0}$ (spectral norm of the same order as $A$ in the random 4-XOR analysis). Hence $\max_{y\in\{\pm1\}^N}y^\top Ay=\tilde O\!\big(\tfrac{n^2}{m\ell^2}\cdot\ell\big)$, certifying $\phi(x)\le 0.01$ for every $x\in\{\pm1\}^n$.

<a id="pdf-9c5df3bb4a04-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.85 -->
**Section 2.3. Proving Feige's conjecture for 4-uniform hypergraphs.** Connects the Kikuchi-matrix analysis to Feige's conjecture on even covers in even-uniform hypergraphs — a trade-off between hyperedge count and girth (smallest even cover) generalizing the Moore bound, which asserts a graph on $n$ vertices with $nd/2$ edges has a cycle of length $\le 2\log_{d-1}n$. Plan: prove a much weaker Moore bound for graphs via a spectral double-counting argument, then generalize to hypergraphs through the associated Kikuchi graph.

<a id="pdf-9c5df3bb4a04-p013-b003"></a>
<!-- pdf-source: page=13; block=3; confidence=0.85 -->
**Proposition 2.3 (Weak Moore bound in irregular graphs).** Every graph $G$ on $n$ vertices with $nd/2$ edges, for $d\ge O(\log_2^{3/2}n)$, has a cycle of length $\le 2\lceil\log_2 n\rceil$.

<a id="pdf-9c5df3bb4a04-p013-b004"></a>
<!-- pdf-source: page=13; block=4; confidence=0.83 -->
**Proof idea (spectral double counting).** Let $A$ be the 0–1 adjacency matrix of $G$; count edges two ways. First, $\mathbf 1^\top A\mathbf 1=nd$. Second, if $G$ has no cycle of length $\le 2\lceil\log_2 n\rceil$, then every $\pm1$-quadratic form of $A$ is at most $n\cdot\tilde O(\sqrt d)$. The two bounds yield a contradiction.

<a id="pdf-9c5df3bb4a04-p013-b005"></a>
<!-- pdf-source: page=13; block=5; confidence=0.85 -->
**Claim 2.4 (Trace method in the absence of even covers).** Let $A$ be the 0–1 adjacency matrix of a graph $G$ on $n$ vertices with $nd/2$ edges and no cycle of length $\le 2r$ for $r=\lceil\log_2 n\rceil$. Then for every $y\in\{\pm1\}^n$,
$$y^\top Ay\le n\sqrt d\cdot O(\log_2^{1.5} n).$$

<a id="pdf-9c5df3bb4a04-p013-b006"></a>
<!-- pdf-source: page=13; block=6; confidence=0.75 -->
The claim contradicts $\mathbf 1^\top A\mathbf 1=nd$ whenever $nd=n\sqrt d\cdot O(\log_2^{1/2}n)$, i.e. when $d\ge O(\log_2^3 n)$, proving Proposition 2.3.

<a id="pdf-9c5df3bb4a04-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.78 -->
**Proof (of Claim 2.4).** Average degree is $d$. For $1\le i\le\log_2 n$ let $\mathcal F_i=\{v: 2^i d\le\deg(v)\le 2^{i+1}d\}$, and let $A_{i/j}$ zero rows outside $\mathcal F_i$ and columns outside $\mathcal F_j$, so $A=\sum_{i/j}A_{i/j}$. As before,
$$y^\top Ay\le\sum_{i/j}\sqrt{|\mathcal F_i|\,|\mathcal F_j|}\,\|A_{i/j}\|_2.\tag{2.4}$$
Bound $\|A_{i/j}\|_2$ via the trace moment method: $\operatorname{tr}\big((A_{i/j}A_{i/j}^\top)^r\big)\ge\|A_{i/j}\|_2^{2r}$. Although $A_{i/j}$ is fixed, if $G$ has no cycle of length $\le 2r$ the upper bound on $\operatorname{tr}(A_{i/j}^{2r})$ matches that of a random signing of $A$. Expanding,
$$\operatorname{tr}\big((A_{i/j}A_{i/j}^\top)^r\big)=\!\!\sum_{v_1,\dots,v_{2r}\in[n]}\!\!A_{i/j}(v_1,v_2)A_{i/j}(v_3,v_2)\cdots A_{i/j}(v_{2r-1},v_{2r})A_{i/j}(v_1,v_{2r}).$$
A tuple contributes $\le 1$ only if each $\{v_i,v_{i+1}\}$ is an edge $e_i$. The multiset $E'=\{e_1,\dots,e_{2r}\}$ (edges of a closed walk) satisfies $\sum_{i=1}^{2r}e_i=0$ over $\mathbb F_2$; pruning equal pairs must remove all edges, else a 2-regular induced subgraph forces a cycle of length $\le 2r$. Hence each edge appears an even number of times. Counting closed walks from fixed $v_1$: matching first/last occurrences gives $\tfrac{(2r)!}{2^r r!}$ matchings, at most $r$ distinct edge choices, each with $\le\Delta=\max(2^i,2^j)d$ options, so at most $n\cdot\Delta^r 2^r r^r$ contributing walks. Thus $\|A_{i/j}\|_2\le 2\sqrt d\,\max(2^{i/2},2^{j/2})\cdot \sqrt{2\log_2 n}$ for $r=2\lceil\log_2 n\rceil$ and large $n$. Substituting into (2.4), $y^\top Ay\le 2\sum_{i\le j}2^{-(i+j)/2}\,n\,2^{j/2}\sqrt{2d\log_2 n}\le n\sqrt d\,O(\log_2^{1.5}n)$.

<a id="pdf-9c5df3bb4a04-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.82 -->
**Summary.** Analyzing hypercube quadratic forms of the row-bucketed adjacency matrix yields a significantly weaker but nontrivial girth bound for a graph with a given edge count.

<a id="pdf-9c5df3bb4a04-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.83 -->
The argument could be sharpened to an absolute-constant factor loss by using the non-backtracking walk matrix of $G$ (dropping the row-bucketing step). The looser argument, however, generalizes to hypergraphs, shown below.

<a id="pdf-9c5df3bb4a04-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.83 -->
**Lemma 2.5 (Feige's conjecture for 4-uniform hypergraphs).** Every 4-uniform hypergraph $\mathcal H$ on $[n]$ with $m\ge O\!\big(\tfrac{n^2}{\ell}\log_2^3 n\big)$ hyperedges has an even cover of length $O(\ell\log_2 n)$.

<a id="pdf-9c5df3bb4a04-p015-b003"></a>
<!-- pdf-source: page=15; block=3; confidence=0.88 -->
**Proof.** Set $b_C=1$ for all $C\in\mathcal H$ and take the Kikuchi matrix $A$ of the resulting 4-XOR instance — equivalently the adjacency matrix of the Kikuchi graph on vertex set $\binom{[n]}{\ell}$ with edges $(S,T)$ where $S\triangle T=C$ for some $C\in\mathcal H$. Each $C\in\mathcal H$ contributes $\binom{4}{2}\binom{n-4}{\ell-2}$ nonzero entries, so for $x=\mathbf 1_n$,
$$(x^{\odot\ell})^\top A\,x^{\odot\ell}=6\binom{n-4}{\ell-2}|\mathcal H|.$$
Mirroring the weak Moore bound: if $\mathcal H$ has no even cover of length $2r$ for $r=0.5\log_2 N$, then $y^\top Ay\le \binom{n}{\ell}\,\tilde O(\ell)$ for all $y\in\{\pm1\}^N$. Let $\deg(S)=|\{C:|S\cap C|=2\}|$; for $i\le\lceil\log_2 m\rceil$ set $\mathcal F_i=\{S: 2^{i-1}d_0\le\deg(S)\le 2^i d_0\}$ (with $\mathcal F_0=\{S:\deg(S)\le d_0\}$), $d_0\sim m\ell^2/n^2$. Since $\deg(S)\le m$ and $d_0\ge 1$, there are $\le\lceil\log_2 m\rceil$ buckets. Writing $A=\sum_{i/j}A_{i/j}$,
$$y^\top Ay\le\sum_{i/j}\|A_{i/j}\|_2\,\sqrt{|\mathcal F_i|\,|\mathcal F_j|}.$$
Since the $b_C$ are fixed at $1$, Matrix Bernstein is replaced by the trace moment method.

<a id="pdf-9c5df3bb4a04-p015-b004"></a>
<!-- pdf-source: page=15; block=4; confidence=0.85 -->
**Proposition 2.6.** If $\mathcal H$ has no even cover of length $2r$ for $r\le\log_2 N$, then $\|A_{i/j}\|_2\le O(\ell\log_2 n)$.

<a id="pdf-9c5df3bb4a04-p015-b005"></a>
<!-- pdf-source: page=15; block=5; confidence=0.72 -->
**Proof of Proposition 2.6.** Use $\|A_{i/j}\|_2^{2r}\le\operatorname{tr}\big((A_{i/j}A_{i/j}^\top)^r\big)$ for $r\in\mathbb N$, with
$$\operatorname{tr}\big((A_{i/j}A_{i/j}^\top)^r\big)=\!\!\sum_{S_1,\dots,S_{2r}\in\binom{[n]}{\ell}}\!\!A_{i/j}(S_1,S_2)A_{i/j}(S_3,S_2)\cdots A_{i/j}(S_{2r-1},S_{2r})A_{i/j}(S_{2r+1},S_{2r}),\quad S_{2r+1}:=S_1.$$
Each term (a $2r$-tuple of $\ell$-sets) contributes $0$ or $1$. A $+1$ term requires, for each $t\le 2r$, some $C_t\in\mathcal H$ with $S_t\triangle S_{t+1}=C_t$; each such term is in bijection with $(S_1,C_1,C_2,\dots,C_{2r})$, and $\varnothing=\triangle_{t=1}^{2r}(S_t\triangle S_{t+1})=\triangle_{t=1}^{2r}C_t$ (text cuts off).

<a id="pdf-9c5df3bb4a04-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.78 -->
**Proof (continued).** Because each surviving element appears twice, the total symmetric difference vanishes, so a non-zero term $(S_1, C_1, C_2, \dots, C_{2r})$ must satisfy $\bigoplus_{t=1}^{2r} C_t = \varnothing$. Removing equal pairs repeatedly (as before) and using that $\mathcal{H}$ has no even cover of length $\le 2r$, each hyperedge occurs an even number of times in the multiset $\{C_1,\dots,C_{2r}\}$. Count the tuples with every $C_t$ occurring evenly: match the first occurrence of each hyperedge to its last, giving at most $2^r r!$ choices of matching. Given $S_1$ and the matching there are at most $r$ distinct $C_t$ to pick, and once $C_t$ is chosen $S_t$ is determined by earlier choices, so at most $\deg(S_t) \le \Delta := \max\{2^i,2^j\}\, d_0$ choices for each hyperedge. Hence there are at most $N \cdot 2^r r!\,\Delta^r$ non-zero terms, and so
$$\lVert A_{i,j}\rVert_2 \le N^{1/2r}2^{1/2}\sqrt r\,\max\{2^{i/2},2^{j/2}\}\sqrt{d_0} \le \max\{2^{i/2},2^{j/2}\}\,2\sqrt{\log_2 N}\,\sqrt{d_0},$$
for $r = 0.5\log_2 N$ and large $n$. The remaining calculation mimics Proposition 2.3 (using $d_0 \sim m\ell^2/n^2$), finishing the proof of Lemma 2.5.

<a id="pdf-9c5df3bb4a04-p016-b002"></a>
<!-- pdf-source: page=16; block=2; confidence=0.90 -->
## 2.4 Refuting semirandom 3-XOR via row pruning

<a id="pdf-9c5df3bb4a04-p016-b003"></a>
<!-- pdf-source: page=16; block=3; confidence=0.85 -->
Odd-arity XOR refutation is significantly harder than even arity (true even for random CSPs and the polynomial-time $\ell = O(1)$ case). The authors first treat random 3-XOR. A prior attempt [WAM19] proposed a Kikuchi-matrix variant whose spectral norm was claimed to refute (Section F.1 of [WAM19]), but this fails (Appendix A); no reasonable Kikuchi variant is known whose spectral norm refutes even fully random 3-XOR at the expected trade-off. Instead they use the spectral norm of a *pruned* version of the matrix, later combined with regularity decomposition and row bucketing for semirandom odd-arity XOR.

<a id="pdf-9c5df3bb4a04-p016-b004"></a>
<!-- pdf-source: page=16; block=4; confidence=0.80 -->
**Setup (Bipartite 3-XOR).** For a 3-XOR instance on a 3-uniform hypergraph $\mathcal{H}$ with $m$ hyperedges and right-hand sides $b_C$, define $\psi(x) = \frac{1}{m}\sum_{C\in\mathcal{H}} b_C x_C$, where $x_R := \prod_{i\in R} x_i$ so $x_C = \prod_{i\in C} x_i$. Let $C_{\min}$ be the minimum-indexed element of $C$ under the natural order on $[n]$. Then
$$\max_{x\in\{\pm1\}^n}\psi(x) \;\le\; \max_{x,y\in\{\pm1\}^n} \frac{1}{m}\sum_{C\in\mathcal{H}} b_C\, y_{C_{\min}}\, x_{C\setminus C_{\min}},$$
where each $y_u$ is a formally new variable identified with $x_u$.

<a id="pdf-9c5df3bb4a04-p017-b001"></a>
<!-- pdf-source: page=17; block=1; confidence=0.78 -->
**Reformulation.** For each $u$, let $\mathcal{H}_u := \{\, C\setminus\{u\} : C\in\mathcal{H},\ C_{\min}=u \,\}$ (the two-element remainders of hyperedges whose minimum is $u$). Then
$$\max_{x\in\{\pm1\}^n}\psi(x) \;\le\; \max_{x,y\in\{\pm1\}^n} \frac{1}{m}\sum_{u\in[n]} y_u \sum_{C\in\mathcal{H}_u} b_{u,C}\, x_C.$$
The RHS is a bipartite 3-XOR instance on $2n$ variables: every constraint uses one $y$ variable and two $x$ variables. The refutation algorithm targets such bipartite instances generally.

<a id="pdf-9c5df3bb4a04-p017-b002"></a>
<!-- pdf-source: page=17; block=2; confidence=0.72 -->
**Squaring step.** By Cauchy-Schwarz,
$$\Big(\tfrac{1}{m}\sum_{u} y_u \sum_{C\in\mathcal{H}_u} b_{u,C} x_C\Big)^2 \le \tfrac{n}{m^2}\sum_u \sum_{C,C'\in\mathcal{H}_u} b_{u,C}b_{u,C'} x_C x_{C'} = \tfrac{n}{m} + \tfrac{n}{m^2}\sum_u \sum_{C\neq C'\in\mathcal{H}_u} b_{u,C}b_{u,C'} x_C x_{C'} =: \tfrac{n}{m} + f(x). \tag{2.5}$$
The first term $n/m \le \varepsilon^2/2$ when $m \ge 2n/\varepsilon^2$; the second term is a $\le 4$-XOR instance. This yields an even-arity (4-XOR) instance, but with far less randomness than the previous section required.

<a id="pdf-9c5df3bb4a04-p017-b003"></a>
<!-- pdf-source: page=17; block=3; confidence=0.80 -->
**Our Kikuchi matrix.** Indexed by size-$\ell$ subsets of a universe of size $2n$ — two labeled copies of each original $x$ variable. For $C\in\mathcal{H}$, let $C^{(1)}$ (resp. $C^{(2)}$) be the copy of $C$ in $[n]\times[2]$ with every element labeled $1$ (resp. $2$). This makes the clauses $x_{C^{(1)}}x_{C'^{(2)}}$ a genuine 4-XOR instance since $C^{(1)}$ and $C'^{(2)}$ cannot intersect. For even $k$ the independent pieces were $A_C$ (one per $C$); for odd $k$ they are $A_u$ (one per $y_u$), reflecting the loss of independence from the Cauchy-Schwarz step.

<a id="pdf-9c5df3bb4a04-p017-b004"></a>
<!-- pdf-source: page=17; block=4; confidence=0.82 -->
**Definition 2.7 (Kikuchi Matrix, 3-XOR).** Let $N = \binom{2n}{\ell}$. For each $u\in[n]$, define $A_u\in\mathbb{R}^{N\times N}$: for $S,T\subseteq[n]\times[2]$ of size $\ell$, $A_u(S,T)$ is non-zero iff there exist $C,C'\in\mathcal{H}_u$ with $S\oplus T = C^{(1)}\oplus C'^{(2)}$ and $1 = |S\cap C^{(1)}| = |S\cap C'^{(2)}| = |T\cap C^{(1)}| = |T\cap C'^{(2)}|$ (i.e. each of $S,T$ holds one variable from each of $C^{(1)},C'^{(2)}$). In that case $A_u(S,T) = b_{u,C}\cdot b_{u,C'}$. Set $A = \sum_u A_u$. Equivalently, $A_u(S,T)\neq 0$ iff the 1-labeled and 2-labeled elements of $S,T$ have symmetric differences $C$ and $C'$ respectively. The two-copy construction makes every pair $(C,C')$ contribute equally many non-zero entries to $A$ (otherwise the count would depend on $|C\cap C'|$), which is needed for row pruning.

<a id="pdf-9c5df3bb4a04-p017-b005"></a>
<!-- pdf-source: page=17; block=5; confidence=0.92 -->
**Quadratic form.** For $D = 4\binom{2n-4}{\ell-2}$, the value of the underlying 4-XOR instance is controlled by
$$\mathrm{val}(\phi)^2 \le \tfrac{n}{m} + \mathrm{val}(f) \le \tfrac{n}{m} + \tfrac{n}{m^2 D}\,\max_{z\in\{\pm1\}^N} z^\top A z.$$

<a id="pdf-9c5df3bb4a04-p018-b001"></a>
<!-- pdf-source: page=18; block=1; confidence=0.78 -->
**Bounding $z^\top A z$.** Unlike the even case, bounding the RHS by the spectral norm of $A$ provably fails. Define the row degree
$$\deg(S) = \big|\{ C,C'\in\mathcal{H}_u : |S\cap C^{(1)}| = |S\cap C'^{(2)}| = 1 \}\big|,$$
the number of non-zero entries in row $S$ of $A_u$. Matrix Bernstein gives an almost-sure bound on $A_u$ of order $\sim \max_S \sqrt{\deg(S)}$, and some $S$ achieve $\ge \ell$; hence the best achievable spectral-norm bound on $A$ is $\Omega(\ell\log_2 N) = \tilde\Omega(\ell^2)$, giving no non-trivial refutation.

<a id="pdf-9c5df3bb4a04-p018-b002"></a>
<!-- pdf-source: page=18; block=2; confidence=0.88 -->
**Row pruning.** Key observation: $\deg(S)$ is large only for few rows. Model a uniform $S\in\binom{[2n]}{\ell}$ by including each element independently w.p. $\sim \ell/2n$; then $\mathbb{E}[\deg(S)] = O(1)$. Using that $|C\cap C'| = \varnothing$ in $\mathcal{H}_u$ for almost all pairs w.h.p., $\mathrm{Var}[\deg(S)] = O(1)$. A Chernoff bound shows the fraction of $S$ with $|\{C\in\mathcal{H}_u : |S\cap C| > O(\log n)\}|$ is inverse-polynomially small; a union bound over $u$ makes the fraction of rows "bad" for any $u$ inverse-polynomial. These bad rows can be dropped without appreciably changing the certified upper bounds on quadratic forms over "flat" vectors. Matrix Bernstein is then applied to the residual matrix. Execution needs row bucketing by a combinatorial parameter, the *butterfly degree* (generalizing [AGK21]), which controls the variance term.

<a id="pdf-9c5df3bb4a04-p018-b003"></a>
<!-- pdf-source: page=18; block=3; confidence=0.82 -->
**Extending to semirandom instances.** The analysis relies on the $\mathcal{H}_u$ satisfying a "spread"/regularity condition: few-to-no distinct pairs $C,C'\in\mathcal{H}_u$ with $C\cap C'\neq\varnothing$; this is the exact pseudorandom property that makes row pruning go through. For 3-XOR it is enforced by an ad hoc argument: if too many pairs share a variable, resolving them yields a 2-XOR system, which is refuted easily via the Grothendieck inequality [Fei07, AGK21]. This was roughly the [AGK21] strategy for $\ell = O(1)$; in that regime one can reduce $k$-XOR for all $k$ to 3-XOR at the right trade-off.

<a id="pdf-9c5df3bb4a04-p018-b004"></a>
<!-- pdf-source: page=18; block=4; confidence=0.85 -->
## 2.5 Handling $k$-XOR for $k \ge 3$: hypergraph regularity

When $\ell \gg O(1)$, higher arity $k$ no longer reduces to $k = 3$. Guided by random $k$-XOR, the argument uses a generalization of the Kikuchi matrix for $k > 3$; analyzing the row-pruning step requires tail inequalities for low-degree polynomials.

<a id="pdf-9c5df3bb4a04-p019-b001"></a>
<!-- pdf-source: page=19; block=1; confidence=0.82 -->
Concentration bounds on the polynomial depend on the "spread" of the hypergraph of nonzero-coefficient indices; the authors use the Schudy–Sviridenko [SS12] inequality (building on [KV00]). This forces a stricter **(ε,ℓ)-regularity** notion: for a parameter ℓ and accuracy bound ε, it requires that for each subset Q ⊆ [n], the number of hyperedges C ∈ ℋ_u with Q ⊆ C is bounded above by a suitable function of m/n and ℓ. Random hypergraphs satisfy this naturally.

<a id="pdf-9c5df3bb4a04-p019-b002"></a>
<!-- pdf-source: page=19; block=2; confidence=0.85 -->
A new regularity decomposition for arbitrary hypergraphs is introduced, based on a **bipartite contraction** operation: given a bipartite hyperedge (u,C) ∈ ℋ and Q ⊆ C, replace it with ((u,Q), C∖Q), merging Q and u into a single new element (u,Q) and yielding a smaller-arity hyperedge in an extended variable space. A greedy, efficient algorithm starts from a k-uniform hypergraph and repeatedly applies bipartite contractions to produce a sequence of k′-uniform hypergraphs (k′ ≤ k) plus some "error" hyperedges, each output k′-uniform hypergraph being (ε,ℓ)-regular and associated with a k′-XOR instance related to the input k-XOR instance. Refuting each output instance yields a refutation of the original k-XOR instance.

<a id="pdf-9c5df3bb4a04-p019-b003"></a>
<!-- pdf-source: page=19; block=3; confidence=0.86 -->
Unlike the 3-XOR case (equal numbers of y and x variables), the bipartite k′-XOR instances from the decomposition are lopsided: the number of y variables can be polynomially larger in n than the number n of x variables, so a naive constraint-count bound is too large even for even k. Instead, applying the Cauchy–Schwarz trick to even-arity k-XOR instances "kills" the y_u's in the polynomial, leaving only a polynomial in the x_i's — a different use than in prior works, where it built "square" matrices for spectral refutations when k is odd.

<a id="pdf-9c5df3bb4a04-p019-b004"></a>
<!-- pdf-source: page=19; block=4; confidence=0.98 -->
## 2.6 Organization

<a id="pdf-9c5df3bb4a04-p019-b005"></a>
<!-- pdf-source: page=19; block=5; confidence=0.95 -->
Section 3: notation and concentration inequalities. Section 4: statement and proof of the hypergraph decomposition lemma. Section 5: begins proof of Theorem 1.5, reducing k-XOR to "lopsided" polynomials. Section 6: handles lopsided polynomials, completing Theorem 1.5. Section 7: uses Theorem 1.5 to prove Theorem 1. Section 8: proves Feige's conjecture (Theorem 2). Section 9: uses Theorems 1 and 2 to prove Theorem 3.

<a id="pdf-9c5df3bb4a04-p020-b001"></a>
<!-- pdf-source: page=20; block=1; confidence=0.98 -->
## 3 Preliminaries
### 3.1 Basic notation

<a id="pdf-9c5df3bb4a04-p020-b002"></a>
<!-- pdf-source: page=20; block=2; confidence=0.90 -->
**Notation.** [n] := {1,…,n}. For S,T ⊆ [n], the symmetric difference is S △ T := {i : (i∈S ∧ i∉T) ∨ (i∉S ∧ i∈T)}. For A ∈ ℝ^{m×n}, the spectral norm is ‖A‖₂ := max_{x∈ℝ^m, y∈ℝ^n, ‖x‖₂=‖y‖₂=1} xᵀAy, and the ∞→1 norm is ‖A‖_{∞→1} := max_{x∈{±1}^m, y∈{±1}^n} xᵀAy; note ‖A‖_{∞→1} ≤ √(nm)·‖A‖₂. For a multiset ℋ, C ∈ ℋ denotes a distinct element and C ≠ C′ denotes distinct elements (even if equal-valued copies). For a set R and variables x₁,…,xₙ, x_R := ∏_{i∈R} x_i; in particular x_C := ∏_{i∈C} x_i.

<a id="pdf-9c5df3bb4a04-p020-b003"></a>
<!-- pdf-source: page=20; block=3; confidence=0.98 -->
### 3.2 Concentration inequalities

<a id="pdf-9c5df3bb4a04-p020-b004"></a>
<!-- pdf-source: page=20; block=4; confidence=0.90 -->
**Fact 3.1 (Rectangular matrix Bernstein; Thm 1.6 of [Tro12]).** Let X₁,…,X_k be independent random d₁×d₂ matrices with 𝔼[X_i] = 0 and ‖X_i‖ ≤ R for all i. Let σ² satisfy σ² ≥ max(‖𝔼[∑_{i=1}^k X_i X_iᵀ]‖, ‖𝔼[∑_{i=1}^k X_iᵀ X_i]‖). Then for all t ≥ 0,

$$\mathbb{P}\left[\left\|\sum_{i=1}^k X_i\right\| \ge t\right] \le (d_1 + d_2)\exp\!\left(\frac{-t^2/2}{\sigma^2 + Rt/3}\right).$$

<a id="pdf-9c5df3bb4a04-p020-b005"></a>
<!-- pdf-source: page=20; block=5; confidence=0.92 -->
**Fact 3.2 (Concentration of polynomials; Thm 1.2 of [SS12], specialized).** Let ℋ ⊆ ([n] choose t) be a collection of multilinear degree-t monomials in n {0,1}-valued variables, and f(x) := ∑_{C∈ℋ} ∏_{i∈C} x_i. Let Y₁,…,Yₙ be i.i.d. Bernoulli with ℙ[Y_i = 1] = τ. Then for some absolute constant R ≥ 1,

$$\mathbb{P}\big[\,|f(Y) - \mathbb{E} f(Y)| \ge \lambda\,\big] \le e^2 \max\!\left(\max_{r=1,\dots,t} e^{-\lambda^2/(\nu_0 \nu_r R^t)},\ \max_{r=1,\dots,t} e^{-(\lambda/(\nu_r R^t))^{1/r}}\right),$$

where for every r ≤ t, ν_r = τ^{t−r} · max_{h₀⊆[n], |h₀|=r} |{h ∈ ℋ : h ⊇ h₀}|.

<a id="pdf-9c5df3bb4a04-p020-b006"></a>
<!-- pdf-source: page=20; block=6; confidence=0.95 -->
### 3.3 The sum-of-squares algorithm

Key SoS facts, taken from [BS16, FKP19].

<a id="pdf-9c5df3bb4a04-p020-b007"></a>
<!-- pdf-source: page=20; block=7; confidence=0.90 -->
**Definition 3.3 (Pseudo-expectations over the hypercube).** A degree-d pseudo-expectation 𝔼̃ over {±1}^n is a linear operator mapping degree-≤d polynomials on {±1}^n to real numbers satisfying three properties:

1. **(Normalization)** 𝔼̃[1] = 1.

(Properties 2 and 3 continue on the next page.)

<a id="pdf-9c5df3bb4a04-p021-b001"></a>
<!-- pdf-source: page=21; block=1; confidence=0.90 -->
**Definition 3.3 (continued).**

2. **(Booleanity)** For any x_i and any polynomial f of degree ≤ d−2, 𝔼̃[f x_i²] = 𝔼̃[f].
3. **(Positivity)** For any polynomial f of degree ≤ d/2, 𝔼̃[f²] ≥ 0.

If 𝔼̃ is the expectation of a genuine distribution over {±1}^n, it is a degree-d pseudo-expectation for every d; hence max_{x∈{±1}^n} f(x) ≤ max_{𝔼̃} 𝔼̃[f], the max over all degree-d pseudo-expectations.

<a id="pdf-9c5df3bb4a04-p021-b002"></a>
<!-- pdf-source: page=21; block=2; confidence=0.88 -->
**Fact 3.4 (Sum-of-squares algorithm; Cor 3.40 in [FKP19]).** Let f(x₁,…,xₙ) be a degree-k polynomial with rational coefficients of poly(n) bit complexity, and let d ≥ k. There is an algorithm that, on input (f, d), runs in time n^{O(d)} and outputs a value β̃ satisfying β + 2^{−n} ≥ β̃ ≥ β, where β is the maximum over all degree-d pseudo-expectations 𝔼̃ over {±1}^n of 𝔼̃[f].

<a id="pdf-9c5df3bb4a04-p021-b003"></a>
<!-- pdf-source: page=21; block=3; confidence=0.92 -->
**Fact 3.5 (SoS Cauchy–Schwarz).** Let f, g be polynomials with deg(f), deg(g) ≤ d/2, and let 𝔼̃ be a degree-d pseudo-expectation. Then 𝔼̃[fg] ≤ √(𝔼̃[f²]·𝔼̃[g²]).

<a id="pdf-9c5df3bb4a04-p021-b004"></a>
<!-- pdf-source: page=21; block=4; confidence=0.92 -->
**Fact 3.6 (Grothendieck's inequality).** Let A be an n×n matrix and let s = max_{Z∈ℝ^{n×n}, Z⪰0, Z_{i,i}=1 ∀i} tr(A·Z). Then s ≤ K_G·‖A‖_{∞→1}, where K_G ≤ 1.8 is a universal constant independent of A.

<a id="pdf-9c5df3bb4a04-p021-b005"></a>
<!-- pdf-source: page=21; block=5; confidence=0.80 -->
**Fact 3.7 (SoS "knows of" Grothendieck).** Let A ∈ ℝ^{n×n} and let 𝔼̃ be a pseudo-expectation over {±1}^n of degree ≥ 2. Then 𝔼̃[xᵀAx] ≤ K_G·‖A‖_{∞→1} ≤ 1.8·‖A‖_{∞→1}.

<a id="pdf-9c5df3bb4a04-p021-b006"></a>
<!-- pdf-source: page=21; block=6; confidence=0.92 -->
**Proof.** Since 𝔼̃ has degree ≥ 2, the pseudo-moment matrix 𝔼̃[xxᵀ] ⪰ 0. Since 𝔼̃ is over {±1}^n, 𝔼̃[x_i²] = 1 for every i ∈ [n]. Thus Z = 𝔼̃[xxᵀ] ⪰ 0 with Z_{i,i} = 1, and applying Fact 3.6 completes the proof. ∎

<a id="pdf-9c5df3bb4a04-p021-b007"></a>
<!-- pdf-source: page=21; block=7; confidence=0.90 -->
**Fact 3.8.** Let f(x₁,…,x_k) be a non-negative degree-≤k multilinear polynomial, i.e. f(x) ≥ 0 for all x ∈ {±1}^k. Let 𝔼̃ be a degree-d pseudo-expectation over {±1}^n with d ≥ 2k. Then 𝔼̃[f] ≥ 0.

<a id="pdf-9c5df3bb4a04-p021-b008"></a>
<!-- pdf-source: page=21; block=8; confidence=0.97 -->
## 4 Hypergraph Decomposition Lemma

<a id="pdf-9c5df3bb4a04-p021-b009"></a>
<!-- pdf-source: page=21; block=9; confidence=0.85 -->
A key ingredient in the proof of Theorem 1 is a **regular hypergraph decomposition algorithm** that takes an arbitrary k-uniform hypergraph and decomposes it into k−1 different regular sub-hypergraphs (after removing a small fraction of the hyperedges). The section presents this decomposition step, first introducing notation and then explaining the decomposition.

<a id="pdf-9c5df3bb4a04-p022-b001"></a>
<!-- pdf-source: page=22; block=1; confidence=0.90 -->
**Definition 4.1 (Uniform hypergraphs).** A *k*-uniform hypergraph ℋ on *n* vertices is a collection of size-exactly-*k* subsets of [n]. For Q ⊆ [n], deg(Q) := |{C ∈ ℋ : Q ⊆ C}|.

<a id="pdf-9c5df3bb4a04-p022-b002"></a>
<!-- pdf-source: page=22; block=2; confidence=0.90 -->
**Remark 4.2.** ℋ is not assumed simple; it may be a multiset. C ∈ ℋ denotes a multiset element, and C ≠ C′ distinguishes distinct copies even when they are equal as sets. deg(Q) counts C ⊇ Q with multiplicity. The reader may assume ℋ is simple; nothing changes for multisets with definitions adjusted to count multiplicities.

<a id="pdf-9c5df3bb4a04-p022-b003"></a>
<!-- pdf-source: page=22; block=3; confidence=0.83 -->
**Definition 4.3 (Bipartite hypergraphs).** A *p*-bipartite *t*-uniform hypergraph on *n* vertices is a collection {ℋ_u}_{u ∈ [p]} where each ℋ_u is a set of size-(t−1) subsets of [n]. Each u (or ℋ_u) is a *partition*; C ∈ ℋ_u corresponds to the hyperedge (u, C). For Q ⊆ [n], u ∈ [p]: deg_u(Q) := |{C ∈ ℋ_u : Q ⊆ C}|. Intuition: view {ℋ_u} as a hypergraph on [p] ⊔ [n] whose hyperedge (u, C) has one vertex u ∈ [p] and t−1 (in the k-uniform case, k−1) vertices in [n]; ℋ_u collects all C with (u, C) present.

<a id="pdf-9c5df3bb4a04-p022-b004"></a>
<!-- pdf-source: page=22; block=4; confidence=0.85 -->
**Definition 4.4 (Hypergraph regularity).** A *p*-bipartite *k*-uniform hypergraph {ℋ_u}_{u ∈ [p]} is (ε, ℓ)-regular if for every u ∈ [p] and every Q ⊆ [n] with |Q| ≤ k−1,

deg_u(Q) ≤ (1/ε²)·max( (n/ℓ)^{k/2−1−|Q|}, 1 ).

When ε, ℓ are clear it is just called *regular*.

<a id="pdf-9c5df3bb4a04-p022-b005"></a>
<!-- pdf-source: page=22; block=5; confidence=0.85 -->
**Remark 4.5 (Regularity as pseudorandomness).** Informally, regularity upper-bounds the number of k-tuples in ℋ_u that all contain a fixed set of size j. If ℋ = ∪_u ℋ_u is a uniformly random bipartite hypergraph with p = n partitions and m = ℓ·(n/ℓ)^{k/2} random k-tuples, then w.h.p. for every u, Q, deg_u(Q) ≤ max( m/(p·n^{|Q|}), 1 )·O(log n) ≤ max( (n/ℓ)^{k/2−1−|Q|}, 1 )·O(log n), i.e. the regularity condition up to an O(log n) factor. Thus regularity is a (weak) pseudorandom property.

<a id="pdf-9c5df3bb4a04-p022-b006"></a>
<!-- pdf-source: page=22; block=6; confidence=0.85 -->
**Definition 4.6 (Bipartite contractions).** Let ℋ be k-uniform on n vertices. A pair (Q, C′) of subsets of [n] is a *contraction* of hyperedge C ∈ ℋ if C = Q ∪ C′ with Q, C′ disjoint (thinkable as an object of size 1 + (k − |Q|): first "element" is the whole set Q, the remaining k − |Q| elements are from C ∖ Q). A *bipartite contraction* of ℋ is a collection of k−1 bipartite hypergraphs {ℋ^{(t)}_u}_{u ∈ [p^{(t)}]} for t = 2, …, k, together with a set ℋ^{(1)} of "discarded edges", such that:
(1) each {ℋ^{(t)}_u}_{u ∈ [p^{(t)}]} is a bipartite t-uniform hypergraph.

<a id="pdf-9c5df3bb4a04-p023-b001"></a>
<!-- pdf-source: page=23; block=1; confidence=0.85 -->
**Definition 4.6 (continued).** (2) each u ∈ [p^{(t)}] corresponds to a subset Q_u ⊆ [n] with |Q_u| = k + 1 − t (distinct u, u′ may have Q_u = Q_{u′}); (3) every hyperedge R ∈ ℋ^{(t)}_u is a bipartite contraction of some hyperedge of ℋ, i.e. Q_u ∪ R = C for some C ∈ ℋ, so (Q_u, R) is a contraction of C; (4) every C ∈ ℋ is contracted exactly once: either C ∈ ℋ^{(1)}, or there is a unique t, u ∈ [p^{(t)}], R ∈ ℋ^{(t)}_u with Q_u ∪ R = C.

<a id="pdf-9c5df3bb4a04-p023-b002"></a>
<!-- pdf-source: page=23; block=2; confidence=0.80 -->
**Lemma 4.7 (Hypergraph contraction lemma).** Let ℋ be a k-uniform hypergraph on n vertices with k ≥ 2 and |ℋ| = m. Then there is a bipartite contraction of ℋ such that:
(1) m^{(1)} := |ℋ^{(1)}| ≤ (n/(kε²))·(n/ℓ)^{k/2−1}.
(2) For t ≥ 2, each bipartite t-uniform {ℋ^{(t)}_u}_{u ∈ [p^{(t)}]} is (a) (ε, ℓ)-regular, and (b) |ℋ^{(t)}_u| = m^{(t)}/p^{(t)} = ⌊(1/ε²)·max((n/ℓ)^{t−k/2−1}, 1)⌋ for all u ∈ [p^{(t)}], where m^{(t)} := Σ_{u ∈ [p^{(t)}]} |ℋ^{(t)}_u|.
Moreover the decomposition is computable, given ℋ, in time O(n^k·|ℋ|²). No lower bound on m is assumed; if m is too small then m^{(t)} = 0 for all t ≥ 2.

<a id="pdf-9c5df3bb4a04-p023-b003"></a>
<!-- pdf-source: page=23; block=3; confidence=0.80 -->
**Proof of Lemma 4.7 (idea).** Analyze a greedy algorithm. If ℋ has too few hyperedges, set ℋ^{(1)} = ℋ and stop. Otherwise there is a "violating" set Q with deg(Q) above a threshold τ (from the regularity definition); choose a *maximal* such Q (no proper superset violates), then (1) remove an arbitrary τ hyperedges of the form Q ∪ C′, (2) form their contractions (Q, C′ ∖ Q), and (3) add {C ∖ Q} to a new partition ℋ^{(k+1−|Q|)}_u with Q_u := Q. The same Q may be chosen again (each step drops deg(Q) by only τ). Repeat until no violation remains. The procedure is one-shot — the produced ℋ^{(t)}_u are not recursively processed — yet they are (ε, ℓ)-regular by design.

<a id="pdf-9c5df3bb4a04-p023-b004"></a>
<!-- pdf-source: page=23; block=4; confidence=0.90 -->
**Algorithm 4.8.** Given: a k-uniform hypergraph ℋ over n vertices with m = |ℋ|. Output: a bipartite contraction {{ℋ^{(t)}_u}_{u ∈ [p^{(t)}]}}_{t = 2, …, k} of ℋ.

<a id="pdf-9c5df3bb4a04-p024-b001"></a>
<!-- pdf-source: page=24; block=1; confidence=0.85 -->
**Algorithm 4.8 (operation).**
1. Initialize p^{(t)} = 0 for t = 2, …, k.
2. Fix violations greedily:
 (a) Find a maximal nonempty violating Q: some Q ⊆ [n] with 1 ≤ |Q| ≤ k−1 such that deg(Q) > (1/ε²)·max((n/ℓ)^{k/2−|Q|}, 1) while deg(Q′) ≤ (1/ε²)·max((n/ℓ)^{k/2−|Q′|}, 1) for all Q′ ⊋ Q.
 (b) Let q = |Q|; take a new label u = 1 + p^{(k+1−q)}; let ℋ′ be an arbitrary subset of {C ∈ ℋ : Q ⊆ C} of size exactly ⌊(1/ε²)·max((n/ℓ)^{k/2−q}, 1)⌋; set Q_u := Q and ℋ^{(k+1−q)}_u := {C ∖ Q : C ∈ ℋ′}.
 (c) Set p^{(k+1−q)} ← 1 + p^{(k+1−q)} and ℋ ← ℋ ∖ ℋ′.
3. When no such Q exists, put the remaining hyperedges in ℋ^{(1)}.

<a id="pdf-9c5df3bb4a04-p024-b002"></a>
<!-- pdf-source: page=24; block=2; confidence=0.88 -->
**Proof (bound on m^{(1)}).** At termination, for every vertex i, deg({i}) ≤ (1/ε²)·max((n/ℓ)^{k/2−1}, 1) = (1/ε²)·(n/ℓ)^{k/2−1}, where deg counts only hyperedges remaining in ℋ (= ℋ^{(1)}). Since Σ_{i ∈ [n]} deg({i}) = k·|ℋ^{(1)}| (each C ∈ ℋ^{(1)} is counted k times), we get m^{(1)} ≤ (n/(kε²))·(n/ℓ)^{k/2−1}.

<a id="pdf-9c5df3bb4a04-p024-b003"></a>
<!-- pdf-source: page=24; block=3; confidence=0.80 -->
**Proof (property (2)(b)).** Fix t ∈ {2, …, k}. By construction every ℋ^{(t)}_u has the same size ⌊(1/ε²)·max((n/ℓ)^{t−k/2−1}, 1)⌋. Hence m^{(t)} := Σ_{u ∈ [p^{(t)}]} |ℋ^{(t)}_u| = p^{(t)}·⌊(1/ε²)·max((n/ℓ)^{t−k/2−1}, 1)⌋, so p^{(t)} ≤ ε²·m^{(t)} and |ℋ^{(t)}_u| = m^{(t)}/p^{(t)}, proving (2)(b).

<a id="pdf-9c5df3bb4a04-p024-b004"></a>
<!-- pdf-source: page=24; block=4; confidence=0.85 -->
**Proof (property (2)(a): (ε, ℓ)-regularity).** Fix u ∈ [p^{(t)}] with associated Q_u, where |Q_u| = k + 1 − t. Let ℋ′ be the set of constraints in ℋ at the moment u and ℋ^{(t)}_u were added, so Q_u ∪ C ∈ ℋ′ for every C ∈ ℋ^{(t)}_u. Take a nonempty R ⊆ [n] with |R| ≤ t−1. If R ∩ Q_u ≠ ∅ then deg_u(R) = 0 (since C ∩ Q_u = ∅ for all C ∈ ℋ^{(t)}_u), so assume R ∩ Q_u = ∅. Then deg_u(R) ≤ deg_{ℋ′}(Q_u ∪ R). Because Q_u was maximal when processed and Q_u ⊊ Q_u ∪ R (R nonempty, disjoint from Q_u),

deg_{ℋ′}(Q_u ∪ R) ≤ (1/ε²)·max((n/ℓ)^{k/2−|Q_u ∪ R|}, 1) = (1/ε²)·max((n/ℓ)^{k/2−|Q_u|−|R|}, 1) = (1/ε²)·max((n/ℓ)^{t−k/2−1−|R|}, 1) ≤ (1/ε²)·max((n/ℓ)^{t/2−1−|R|}, 1),

the last inequality using t − k/2 − 1 − |R| ≤ t/2 − 1 − |R| since t ≤ k. This gives the regularity bound for the t-uniform piece.

<a id="pdf-9c5df3bb4a04-p025-b001"></a>
<!-- pdf-source: page=25; block=1; confidence=0.80 -->
**Proof (conclusion).** Finally, when $R=\varnothing$, we have $\deg_u(\varnothing)=|\mathcal H^{(t)}_u|=\lfloor\tfrac{1}{\varepsilon^2}\max((n/\ell)^{t-k/2-1},1)\rfloor\le\tfrac{1}{\varepsilon^2}\max((n/\ell)^{t-k/2-1},1)\le\tfrac{1}{\varepsilon^2}\max((n/\ell)^{t/2-1},1)$, using $t-k/2\le t/2$ since $t\le k$. Runtime: each iteration takes $O(|\mathcal H|\,n^k)$ time by brute force, and there are at most $|\mathcal H|$ iterations.

<a id="pdf-9c5df3bb4a04-p025-b002"></a>
<!-- pdf-source: page=25; block=2; confidence=0.60 -->
**§5 Refuting Semirandom Sparse Polynomials over the Hypercube.** Gives an algorithm to tightly refute semirandom instances of homogeneous, multilinear degree-$k$ polynomials: given $\phi$ in $n$ variables $x_1,\dots,x_n$, it outputs a correct upper bound on $\mathrm{val}(\phi):=\max_{x\in\{\pm1\}^n}\phi(x)$. When coefficients are drawn from independent distributions on $[-1,1]$ and the coefficient (multi-)hypergraph has enough hyperedges, w.h.p. the output is below a target $\varepsilon$ (Theorem 5.1).

<a id="pdf-9c5df3bb4a04-p025-b003"></a>
<!-- pdf-source: page=25; block=3; confidence=0.85 -->
**Theorem 5.1 (Refuting semirandom sparse polynomials).** Let $k\in\mathbb N$ and $\ell:\mathbb N\to\mathbb N$ with $2(k-1)\le\ell(n)\le n$. There is an algorithm taking a homogeneous multilinear polynomial $\phi$ in $n$ variables of total degree $k$, specified by a $k$-uniform multi-hypergraph $\mathcal H$ and rationals $\{b_C\}_{C\in\mathcal H}$ with
$$\phi(x)=\tfrac1m\sum_{C\in\mathcal H}b_C\prod_{i\le k}x_{C_i},\qquad(5.1)$$
and outputting $\mathrm{alg\text{-}val}(\phi)\in[-1,1]$ in time $n^{O(\ell)}$ such that:
**(1)** $1\ge\mathrm{alg\text{-}val}(\phi)\ge\mathrm{val}(\phi)$.
**(2)** There is an absolute constant $\Gamma>0$ such that if $n^{\log_2 n}\ge|\mathcal H|=m\ge m_0=\Gamma^k\cdot(n/\ell)^{k/2}\cdot\ell\cdot(\log_2 n)^{4k+1}/\varepsilon^5$ and the $b_C$ are independent, mean-$0$ variables supported in $[-1,1]$, then with probability $1-1/\mathrm{poly}(n)$ over the $b_C$, $\mathrm{alg\text{-}val}(\phi)\le\varepsilon+2^{-n}$.
Moreover the algorithm is captured by the canonical degree-$2\ell$ sum-of-squares relaxation of hypercube polynomial maximization: under the same hypothesis, for every pseudo-expectation $\tilde{\mathbb E}$ of degree $\ge 2\ell$ over $\{\pm1\}^n$, $\tilde{\mathbb E}[\phi]\le\varepsilon$.

<a id="pdf-9c5df3bb4a04-p025-b004"></a>
<!-- pdf-source: page=25; block=4; confidence=0.75 -->
As in §4, $\mathcal H$ is not assumed simple, and the notational conventions of Remark 4.2 are adopted.

<a id="pdf-9c5df3bb4a04-p025-b005"></a>
<!-- pdf-source: page=25; block=5; confidence=0.65 -->
**§5.1 Regular bipartite polynomials.** The proof of Theorem 5.1 reduces to refuting sparse polynomials with extra structure called *bipartite polynomials*, generalizing the partitioned 2-XOR instances of [GK21]. A *regularity* property of these polynomials is the key technical ingredient of the algorithm.

<a id="pdf-9c5df3bb4a04-p026-b001"></a>
<!-- pdf-source: page=26; block=1; confidence=0.60 -->
**Definition 5.2 ($p$-bipartite polynomials).** Let $k\in\mathbb N$. A $p$-bipartite polynomial $\psi$ is a homogeneous degree-$k$ polynomial in the $p+n$ variables $y=\{y_u\}_{u\in[p]}$ and $x=\{x_j\}_{j\in[n]}$ defined by
$$\psi(y,x)=\tfrac1m\sum_{u=1}^{p}y_u\sum_{C\in\mathcal H_u}b_{u,C}\,x_C,$$
where $\{\mathcal H_u\}_{u\in[p]}$ is a $p$-bipartite $k$-uniform hypergraph (Definition 4.3), $b_{u,C}\in[-1,1]$, $x_C:=\prod_{i\in C}x_i$, and $m:=\sum_{u\in[p]}|\mathcal H_u|$. Its value is $\mathrm{val}(\psi)=\max_{y\in\{\pm1\}^p,\,x\in\{\pm1\}^n}\psi(y,x)\in[-1,1]$. Note $\psi$ is homogeneous of degree $1$ in $y$.

<a id="pdf-9c5df3bb4a04-p026-b002"></a>
<!-- pdf-source: page=26; block=2; confidence=0.70 -->
**Definition 5.3 (Regular $p$-bipartite polynomials).** A $p$-bipartite polynomial $\psi$ is $(\varepsilon,\ell)$-regular if its underlying $p$-bipartite $k$-uniform hypergraph $\{\mathcal H_u\}_{u\in[p]}$ is $(\varepsilon,\ell)$-regular (Definition 4.4). When $\varepsilon,\ell$ are clear, $\psi$ is simply called regular.

<a id="pdf-9c5df3bb4a04-p026-b003"></a>
<!-- pdf-source: page=26; block=3; confidence=0.80 -->
**Theorem 5.4 (Refuting regular bipartite polynomials).** The bulk of Theorem 5.1's proof is this. Let $k\in\mathbb N$ and $\ell:\mathbb N\to\mathbb N$ with $2(k-1)\le\ell(n)\le n$. There is an algorithm taking a $p$-bipartite homogeneous polynomial $\psi(y,x)$ in $y=\{y_u\}_{u\in[p]}$, $x=\{x_i\}_{i\in[n]}$ of total degree $k$,
$$\psi(y,x)=\tfrac1m\sum_{u=1}^{p}y_u\sum_{C\in\mathcal H_u}b_{u,C}\,x_C,$$
specified by $(k-1)$-uniform hypergraphs $\{\mathcal H_u\}_{u\in[p]}$ and rationals $\{b_{u,C}\}\subset[-1,1]$, running in time $(p+n)^{O(\ell)}$ and outputting $\mathrm{alg\text{-}val}(\psi)\in[-1,1]$ with:
**1.** $\mathrm{alg\text{-}val}(\psi)\ge\mathrm{val}(\psi)$ for every $\psi$.
**2.** Whenever: **(a)** $\psi$ is $(\varepsilon,\ell)$-regular; **(b)** $|\mathcal H_u|\le 2m/p$ for all $u\in[p]$; **(c)** $n^{\log_2 n}\ge m\ge\max\{\Gamma^k\cdot(n/\ell)^{(k-1)/2}\cdot\sqrt{p\ell}\cdot(\log_2 n)^{2k+0.5}/\varepsilon^3,\ p/\varepsilon^2\}$, where $\Gamma$ is an absolute constant; **(d)** each $b_{u,C}$ is from a (possibly different) independent mean-zero distribution on $[-1,1]$ — then with probability $1-1/\mathrm{poly}(n)$, $\mathrm{alg\text{-}val}(\psi)\le\sqrt{2.8}\,\varepsilon+2^{-n}$.
Further, the algorithm is captured by the degree-$2\ell$ SoS algorithm: for every degree-$2\ell$ pseudo-expectation $\tilde{\mathbb E}$ in $x,y$ over $\{\pm1\}^{p+n}$, $\tilde{\mathbb E}[\psi(x,y)]\le\sqrt{2.8}\,\varepsilon$. Proof deferred to §6.

<a id="pdf-9c5df3bb4a04-p027-b001"></a>
<!-- pdf-source: page=27; block=1; confidence=0.70 -->
**§5.2 Reduction to regular bipartite polynomials.** Combines Lemma 4.7 and Theorem 5.4 to prove Theorem 5.1 by analyzing Algorithm 5.5.

<a id="pdf-9c5df3bb4a04-p027-b002"></a>
<!-- pdf-source: page=27; block=2; confidence=0.60 -->
**Algorithm 5.5 (Main Refutation Algorithm).** *Given:* $\phi$ specified by a $k$-uniform multi-hypergraph $\mathcal H$ over $n$ vertices and rationals $\{b_C\}_{C\in\mathcal H}$. *Output:* a value $\mathrm{alg\text{-}val}\in[-1,1]$. *Operation:*
1. Apply the Lemma 4.7 decomposition to build bipartite hypergraphs $\{\mathcal H^{(t)}_u\}_{u\in[p^{(t)}]}$ for $2\le t\le k$, plus a set $\mathcal H^{(1)}$ of discarded edges.
2. For every $t$, $u\in[p^{(t)}]$, and hyperedge $C\in\mathcal H^{(t)}_u$, set $b_{u,C}=b_{Q_u\cup C}$.
3. For $2\le t\le k$, apply the Theorem 5.4 refutation algorithm to the degree-$t$, $p^{(t)}$-bipartite polynomial given by $\{\mathcal H^{(t)}_u\}$ and the $b_{u,C}$ to get $\mathrm{alg\text{-}val}_t$; set $\mathrm{alg\text{-}val}_1=1$.
4. Output $\mathrm{alg\text{-}val}=\tfrac1m\sum_{t=1}^{k}m^{(t)}\cdot\mathrm{alg\text{-}val}_t$, where $m^{(t)}=\sum_{u\in[p^{(t)}]}|\mathcal H^{(t)}_u|$.

<a id="pdf-9c5df3bb4a04-p027-b003"></a>
<!-- pdf-source: page=27; block=3; confidence=0.88 -->
**Proof of Theorem 5.1 (from Lemma 4.7 and Theorem 5.4).** WLOG $\varepsilon\le 1/\sqrt2$, so $1/\varepsilon^2\ge2$ (changes only the universal constant). For each $t$ and $u\in[p^{(t)}]$, let $Q_u\subseteq[n]$ be the associated subset of size $k+1-t$, and let $\psi_t$ be the polynomial of the $t$-uniform $(\varepsilon,\ell)$-regular bipartite hypergraph $\{\mathcal H^{(t)}_u\}$ from the decomposition, in variables $\{y^{(t)}_u\}_{u\in[p^{(t)}]}\cup\{x_i\}_{i\in[n]}$:
$$\psi_t(\{y^{(t)}_u\},x):=\tfrac{1}{m^{(t)}}\sum_{u\in[p^{(t)}]}y^{(t)}_u\sum_{C\in\mathcal H^{(t)}_u}b_{Q_u\cup C}\,x_C.$$
Then
$$\phi(x)=\tfrac1m\sum_{t=2}^{k}m^{(t)}\psi_t(\{x_{Q_u}\}_{u},x)+\tfrac1m\sum_{C\in\mathcal H^{(1)}}b_C\,x_C,\qquad(5.2)$$
by definition of bipartite contraction: substituting $x_{Q_u}$ for $y_u$ gives $y_u x_C=x_{Q_u\cup C}=x_{C'}$ for $C'\in\mathcal H$. With $\mathrm{alg\text{-}val}_t=\mathrm{alg\text{-}val}(\psi_t)$, Theorem 5.4 gives $\mathrm{val}(\psi_t)\le\mathrm{alg\text{-}val}_t$, so by (5.2) $\mathrm{val}(\phi)\le\tfrac1m\sum_{t=1}^{k}m^{(t)}\mathrm{alg\text{-}val}_t=\mathrm{alg\text{-}val}$. If $m^{(t)}\le\varepsilon m$ for some $t$, the trivial bound $\mathrm{alg\text{-}val}(\psi_t)\le1$ gives $m^{(t)}\mathrm{alg\text{-}val}(\psi_t)\le\varepsilon m$. In particular $m^{(1)}\le\varepsilon m$ always holds, since $m\ge\tfrac{1}{\varepsilon^3}(n/\ell)^{k/2}\ell$ and $m^{(1)}\le\tfrac{n}{k\varepsilon^2}(n/\ell)^{k/2-1}$.

<a id="pdf-9c5df3bb4a04-p028-b001"></a>
<!-- pdf-source: page=28; block=1; confidence=0.75 -->
**Proof (continued).** Now suppose that for some $t$, $m^{(t)} \ge \varepsilon m$. Notice $m^{(t)} \le m \le n^k \le n^{\log_2 n}$. We prove that in this setting $m^{(t)} \ge \Gamma^t\cdot(n/\ell)^{(t-1)/2}\cdot\sqrt{p^{(t)}\ell}\cdot(\log_2 n)^{2t+0.5}/\varepsilon^3$. Since $m^{(t)} = p^{(t)}\cdot\lfloor\tfrac{1}{\varepsilon^2}\max((n/\ell)^{t-k/2-1}, 1)\rfloor$, it suffices to show
$$\varepsilon m \ge \Gamma^{2t}\cdot(n/\ell)^{t-1}\cdot\ell\cdot(\log_2 n)^{4t+1}/\varepsilon^6 \cdot \frac{1}{\tfrac{1}{2\varepsilon^2}\max((n/\ell)^{t-k/2-1}, 1)},$$
where we use that $\lfloor\tfrac{1}{\varepsilon^2}\max((n/\ell)^{t-k/2-1}, 1)\rfloor \ge \lfloor\tfrac{1}{\varepsilon^2}\rfloor \ge \tfrac{1}{2\varepsilon^2}$ as $1/\varepsilon^2\ge 2$. Hence, for $t\ge \tfrac{k}{2}+1$ it suffices that $\varepsilon m \ge 2\Gamma^{2t}\,(n/\ell)^{k/2}\ell\,(\log_2 n)^{4t+1}/\varepsilon^4$, and for $t<\tfrac{k}{2}+1$ that $\varepsilon m \ge 2\Gamma^{2t}\,(n/\ell)^{t-1}\ell\,(\log_2 n)^{4t+1}/\varepsilon^4$. As $m \ge \Gamma'^{k}(n/\ell)^{k/2}\ell\,(\log_2 n)^{4k+1}/\varepsilon^5$ for the absolute constant $\Gamma' = 2\Gamma^2$, both conditions are satisfied. Hence if $m^{(t)}\ge\varepsilon m$ then $\psi_t$ satisfies the hypotheses of Theorem 5.4, so $m^{(t)}\cdot\mathrm{alg\text{-}val}_t \le \varepsilon m^{(t)} \le \varepsilon m$ with probability $1-1/\mathrm{poly}(n)$ over the draw of the $b_{C}$'s. A union bound over all $t$ gives $\mathrm{alg\text{-}val}(\phi) \le O(k\varepsilon)$ with probability $1-k/\mathrm{poly}(n) \ge 1-1/\mathrm{poly}(n)$, completing the analysis of the second guarantee.

<a id="pdf-9c5df3bb4a04-p028-b002"></a>
<!-- pdf-source: page=28; block=2; confidence=0.85 -->
Running time is dominated by applying the Theorem 5.4 refutation algorithm to each bipartite polynomial produced by the decomposition algorithm, bounded by $n^{O(\ell)}$. The algorithm is captured by SoS because Theorem 5.4 is captured by SoS and by linearity of pseudo-expectations.

<a id="pdf-9c5df3bb4a04-p028-b003"></a>
<!-- pdf-source: page=28; block=3; confidence=0.95 -->
**6. Refuting Regular Bipartite Polynomials**

<a id="pdf-9c5df3bb4a04-p028-b004"></a>
<!-- pdf-source: page=28; block=4; confidence=0.85 -->
Proves Theorem 5.4 via an SDP relaxation of the $\infty\to 1$ norm of a matrix associated with the polynomial $\psi$; the analysis yields the "Further, …" part of the statement. As in prior work starting with [CGL04], the proof applies the Cauchy–Schwarz trick to reduce to an even-degree polynomial associated with $\psi$.

<a id="pdf-9c5df3bb4a04-p028-b005"></a>
<!-- pdf-source: page=28; block=5; confidence=0.80 -->
**Lemma 6.1 (Cauchy–Schwarz trick).** Let $\psi$ be a $p$-bipartite, homogeneous polynomial $\psi=\psi(y,x)$ in variables $y=(y_u)_{u\in[p]}$ and $x=(x_i)_{i\in[n]}$ of total degree $k$, given by
$$\psi(y,x)=\frac{1}{m}\sum_{u=1}^{p} y_u \sum_{C\in\mathcal H_u} b_{u,C}\,x_C.$$
*(statement continues on next page)*

<a id="pdf-9c5df3bb4a04-p029-b001"></a>
<!-- pdf-source: page=29; block=1; confidence=0.80 -->
Let $f$ be obtained from $\psi$ by
$$f(x)=\frac{p}{m^2}\sum_{u=1}^{p}\sum_{\substack{(C,C')\in\mathcal H_u\times\mathcal H_u\\ C\ne C'}} b_{u,C}\,b_{u,C'}\,x_C x_{C'}.$$
Then $\mathrm{val}(\psi)^2 \le \tfrac{p}{m}\,\mathrm{val}(f)$. Further, for every pseudo-expectation $\tilde{\mathbb E}$ of degree $\ge 2k$ over $\{\pm 1\}^{p+n}$, $\tilde{\mathbb E}[\psi]^2 \le \tfrac{p}{m}\,\tilde{\mathbb E}[f]$.

<a id="pdf-9c5df3bb4a04-p029-b002"></a>
<!-- pdf-source: page=29; block=2; confidence=0.70 -->
**Proof.** Fix a $\pm 1$ assignment to the $y_u$ and $x_i$. Then
$$\psi^2(y,x)=\Big(\tfrac{1}{m}\sum_{u} y_u\sum_{C\in\mathcal H_u} b_{u,C}x_C\Big)^2 \le \tfrac{1}{m^2}\Big(\sum_u y_u^2\Big)\Big(\sum_u\big(\sum_{C\in\mathcal H_u} b_{u,C}x_C\big)^2\Big)$$
$$\le \tfrac{p}{m^2}\sum_u\sum_{C\in\mathcal H_u} b_{u,C}^2 x_C^2 + \tfrac{p}{m^2}\sum_u\sum_{(C,C'),C\ne C'} b_{u,C}b_{u,C'}x_C x_{C'} \le \tfrac{p}{m} + \tfrac{p}{m^2}\sum_u\sum_{C\ne C'} b_{u,C}b_{u,C'}x_C x_{C'},$$
using Cauchy–Schwarz (first step), $y_u^2=1$ (second), and $b_{u,C}^2\le 1$, $x_C^2=1$ (third). By the SoS Cauchy–Schwarz inequality (Fact 3.5) and $\tilde{\mathbb E}$ being over $\{\pm 1\}^{p+n}$, the same holds for degree $d\ge 2(k+1)$ pseudo-expectations. Taking the maximum over $x,y$ gives $\mathrm{val}(\psi)^2\le\tfrac{p}{m}\mathrm{val}(f)$; maximizing over pseudo-expectations and using Fact 3.5 gives $\tilde{\mathbb E}[\psi]^2\le\tilde{\mathbb E}[\psi^2]\le\tfrac{p}{m}\tilde{\mathbb E}[f]$. $\square$

<a id="pdf-9c5df3bb4a04-p029-b003"></a>
<!-- pdf-source: page=29; block=3; confidence=0.95 -->
**6.1 Our Kikuchi matrix and algorithm**

<a id="pdf-9c5df3bb4a04-p029-b004"></a>
<!-- pdf-source: page=29; block=4; confidence=0.85 -->
By Lemma 6.1 it suffices to upper bound $\mathrm{val}(f)$; the certificate uses a variant of the Kikuchi matrix of [WAM19]. Notation: two clones of each of the $n$ $x$-variables, denoted $(i,1)$ and $(i,2)$; for $C\subseteq[n]$, $C(1)=\{(i,1):i\in C\}$ and $C(2)=\{(i,2):i\in C\}$. $S\triangle T$ is symmetric difference, and $S_1\triangle\cdots\triangle S_t$ is the set of elements occurring in an odd number of the $S_i$.

<a id="pdf-9c5df3bb4a04-p029-b005"></a>
<!-- pdf-source: page=29; block=5; confidence=0.90 -->
**Definition 6.2 (Our Kikuchi Matrix).** Let $\ell\in\mathbb N$ and $N:=\binom{2n}{\ell}$. Fix a $p$-bipartite $k$-uniform hypergraph $\{\mathcal H_u\}_{u\in[p]}$. For each $u\in[p]$ define the $N\times N$ matrix $A_u$, indexed by sets $S\subseteq[n]\times[2]$ of size $\ell$. For $S,T\subseteq[n]\times[2]$ of size $\ell$ and $C\ne C'\in\mathcal H_u$ of size $k-1$, say $S\xrightarrow{C,C'}T$ if:
1. $S\triangle T = C(1)\triangle C'(2)$;
2. $k$ odd, and $|S\cap C(1)|=|S\cap C'(2)|=|T\cap C(1)|=|T\cap C'(2)|=\tfrac{k-1}{2}$; or
*(conditions 3–4 continue on next page)*

<a id="pdf-9c5df3bb4a04-p030-b001"></a>
<!-- pdf-source: page=30; block=1; confidence=0.72 -->
3. $k$ even, and $|S\cap C(1)|=|T\cap C'(2)|=\tfrac{k}{2}$ and $|S\cap C'(2)|=|T\cap C(1)|=\tfrac{k+2}{2}$; or
4. $k$ even, and $|S\cap C(1)|=|T\cap C'(2)|=\tfrac{k+2}{2}$ and $|S\cap C'(2)|=|T\cap C(1)|=\tfrac{k}{2}$.
Note $C(1)\triangle C'(2)=C(1)\cup C'(2)$ since they are disjoint. Define
$$A_u(S,T)=\begin{cases} b_{u,C}\,b_{u,C'} & \text{if }\exists\,C,C'\in\mathcal H_u\text{ with } S\xrightarrow{C,C'}T,\\ 0 & \text{otherwise.}\end{cases}\quad(6.1)$$
If $\mathcal H$ is not simple, the nonzero entry is replaced by $\sum_{C\ne C'\in\mathcal H_u:\,S\xrightarrow{C,C'}T} b_{u,C}b_{u,C'}$ (sum over distinct multiset elements, possibly equal as sets). The overall Kikuchi matrix for $f$ is $A:=\sum_{u=1}^{p} A_u$. $(6.2)$

<a id="pdf-9c5df3bb4a04-p030-b002"></a>
<!-- pdf-source: page=30; block=2; confidence=0.92 -->
**Lemma 6.3.** Let $N:=\binom{2n}{\ell}$ and $A$ the Kikuchi matrix of Definition 6.2 for an arbitrary $p$-bipartite $\psi$ with hypergraph $\mathcal H$ and coefficients $\{b_{u,C}\}$. For $x\in\{-1,1\}^n$, let $x^{\odot\ell}\in\{-1,1\}^N$ have $S$-th entry $x_S:=\prod_{b\in[2]}\prod_{(i,b)\in S} x_i$. Then
$$(x^{\odot\ell})^\top A\,x^{\odot\ell}=\frac{m^2 D}{p}\,f(x)\quad(6.3)$$
for $D$ as in Eq. (6.6). Consequently, since $x^{\odot\ell}$ has $\pm 1$ entries, $\mathrm{val}(f)\le\frac{p}{m^2 D}\|A\|_{\infty\to 1}$. Furthermore, for every pseudo-expectation $\tilde{\mathbb E}$ of degree $\ge 2\ell$ over $\{\pm 1\}^n$,
$$\tilde{\mathbb E}[f]=\frac{p}{m^2 D}\tilde{\mathbb E}\big[(x^{\odot\ell})^\top A x^{\odot\ell}\big]\le K_G\cdot\frac{p}{m^2 D}\|A\|_{\infty\to 1},$$
where $K_G\le 1.8$ is the universal constant of Fact 3.6.

<a id="pdf-9c5df3bb4a04-p030-b003"></a>
<!-- pdf-source: page=30; block=3; confidence=0.85 -->
**Proof.** For (6.3): by definition of $A$, when $k$ is odd each pair $(C,C')$ in $\mathcal H_u$ with $C\ne C'$ appears exactly $\binom{k-1}{(k-1)/2}^2\binom{2n-2(k-1)}{\ell-(k-1)}=D$ times in the expansion of the LHS — choose $S$'s $\tfrac{k-1}{2}$-element intersections with $C(1)$ and with $C'(2)$ (the $\binom{k-1}{(k-1)/2}^2$ factor), then the rest of $S$ ($\binom{2n-2(k-1)}{\ell-(k-1)}$ choices), which also determines $T$. A similar count gives $D$ for $k$ even, yielding (6.3). The clones ensure each pair $(C,C')$ appears the same number of times regardless of $|C\cap C'|$. The "as a consequence" part follows from the definition of the $\infty\to 1$ norm; the "furthermore" from Facts 3.6 and 3.7. $\square$

<a id="pdf-9c5df3bb4a04-p030-b004"></a>
<!-- pdf-source: page=30; block=4; confidence=0.90 -->
The definitions made so far are summarized below.

<a id="pdf-9c5df3bb4a04-p031-b001"></a>
<!-- pdf-source: page=31; block=1; confidence=0.90 -->
**Key Notation.** Fixes the three objects used throughout: the input polynomial ψ (eq. 6.4), the Cauchy–Schwarz polynomial f (eq. 6.5), and the Kikuchi matrix A (eq. 6.6), followed by the refutation algorithm.

<a id="pdf-9c5df3bb4a04-p031-b002"></a>
<!-- pdf-source: page=31; block=2; confidence=0.86 -->
**Notation 1 — input polynomial ψ, eq. (6.4).**
$$\psi(y,x)=\sum_{u\in[p]} y_u \sum_{C\in\mathcal{H}_u} b_{u,C}\,x_C.$$
ψ is (ε,ℓ)-regular and p-bipartite homogeneous of total degree k. It is described by a collection of (k+1)-uniform hypergraphs $\{\mathcal{H}_u\}_{u\in[p]}$ (one per $u\in[p]$) and rationals $\{b_{u,C}\}_{u\in[p],\,C\in\mathcal{H}_u}$.

<a id="pdf-9c5df3bb4a04-p031-b003"></a>
<!-- pdf-source: page=31; block=3; confidence=0.88 -->
**Notation 2 — polynomial f after the Cauchy–Schwarz trick, eq. (6.5).**
$$f(x)=\frac{p}{m^2}\sum_{u\in[p]}\ \sum_{\substack{(C,C')\in\mathcal{H}_u\times\mathcal{H}_u\\ C\neq C'}} b_{u,C}\,b_{u,C'}\,x_C x_{C'},$$
homogeneous of total degree 2(k−1). Moreover $\mathrm{val}(\psi)^2 \le \mathrm{val}(f)+p/m \le \mathrm{val}(f)+\varepsilon^2$, using $p/m \le \varepsilon^2$.

<a id="pdf-9c5df3bb4a04-p031-b004"></a>
<!-- pdf-source: page=31; block=4; confidence=0.85 -->
**Notation 3 — Kikuchi matrix A, eq. (6.6).** $A=\sum_u A_u$ is an $N\times N$ matrix with $N=\binom{2n}{\ell}$, rows/columns indexed by sets $S,T\subseteq[n]\times[2]$ of size ℓ. The entry $A_u(S,T)$ is nonzero and equal to $b_{u,C}b_{u,C'}$ iff $S \overset{C,C'}{\longleftrightarrow} T$ for some distinct pair $C,C'\in\mathcal{H}_u$. Each pair $(C,C')$ contributes exactly $D$ nonzero entries, where (6.6)
$$D=\begin{cases}\binom{k-1}{(k-1)/2}^2\binom{2n-2(k-1)}{\ell-(k-1)} & \text{if }k\text{ is odd,}\\ 2\binom{k-1}{k/2}\binom{k-1}{(k-2)/2}\binom{2n-2(k-1)}{\ell-(k-1)} & \text{if }k\text{ is even.}\end{cases}$$
Furthermore $\mathrm{val}(f) \le \frac{p}{m^2 D}\,\lVert A\rVert_{\infty\to1}$.

<a id="pdf-9c5df3bb4a04-p031-b005"></a>
<!-- pdf-source: page=31; block=5; confidence=0.85 -->
**Algorithm 6.4 (Refutation Algorithm for Regular Polynomials).** Given an (ε,ℓ)-regular p-bipartite polynomial $\psi=\sum_u\sum_{C\in\mathcal{H}_u} b_{u,C}\,y_u x_C$ in variables $x,y$, specified by (k−1)-uniform hypergraphs $\{\mathcal{H}_u\}_{u\in[p]}$ on [n] and rationals $\{b_{u,C}\}\in[-1,1]$. Output a value $\alpha\in[-1,1]$ with $\alpha\ge\mathrm{val}(\psi)$. Steps: (1) construct the $N\times N$ Kikuchi matrix A (Definition 6.2); (2) compute the SDP value $s=\max\{\,\mathrm{tr}(A\cdot Z):Z\in\mathbb{R}^{N\times N},\,Z\succeq0,\,Z_{S,S}=1\ \forall S\,\}$; (3) output $\alpha=\sqrt{\tfrac{p}{m^2 D}\,s + \tfrac{p}{m}}$.

<a id="pdf-9c5df3bb4a04-p032-b001"></a>
<!-- pdf-source: page=32; block=1; confidence=0.72 -->
**Lemma 6.5 (Bounding $\lVert A\rVert_{\infty\to1}$).** Let A be the Kikuchi matrix of Definition 6.2. With probability at least $1-1/10^{\mathrm{poly}(n)}$ over the draw of the $b_{u,C}$'s,
$$\lVert A\rVert_{\infty\to1}\ \le\ \frac{m^2 D\varepsilon^2}{p}.$$

<a id="pdf-9c5df3bb4a04-p032-b002"></a>
<!-- pdf-source: page=32; block=2; confidence=0.85 -->
**Proof (Lemma 6.5 ⇒ Theorem 5.4).** Since $Z=x^{\odot\ell}(x^{\odot\ell})^\top$ is a feasible SDP solution of value $\mathrm{val}(f)\cdot(Dm^2/p)$, we get $s\ge\mathrm{val}(f)\cdot Dm^2/p$; hence by Lemma 6.1, $\alpha\ge\mathrm{val}(\psi)$ always. By Fact 3.6, $s\le 1.8\lVert A\rVert_{\infty\to1}$. Combined with $p/m\le\varepsilon^2$, the algorithm's output is at most $\sqrt{2.8}\,\varepsilon$. An additional additive $2^{-n}$ error is required in the final algorithm because SDPs can only be solved efficiently to exponentially small error.

<a id="pdf-9c5df3bb4a04-p032-b003"></a>
<!-- pdf-source: page=32; block=3; confidence=0.82 -->
**§6.2 — Proof plan.** By Lemma 6.3, bounding $\lVert A\rVert_{\infty\to1}\le m^2 D\varepsilon^2/p$ reduces to establishing this bound when the $b_{u,C}$ are drawn independently from distributions supported on $[-1,1]$; the proof has three conceptual steps.

<a id="pdf-9c5df3bb4a04-p032-b004"></a>
<!-- pdf-source: page=32; block=4; confidence=0.85 -->
Steps: (1) **Row pruning** — delete rows of A with too-large $\ell_1$ norm in any $A_u$, incurring only a small additive loss; relies on regularity of the $\mathcal{H}_u$ and the Schudy–Sviridenko polynomial concentration inequality for combinatorial polynomials [SS12]. (2) **Row bucketing** — after pruning no row has large $\ell_1$-norm in a single $A_u$, but the spectral norm need not be bounded for arbitrary regular $\mathcal{H}_u$; instead partition rows/columns of A so that within each bucket all rows/columns contribute roughly equally to the “variance term.” (3) **Spectral norm bound** — bound the spectral norm of each partition piece to bound its $\infty\to1$ norm; this is the only step using randomness of the right-hand sides $b_C$, and larger spectral norm on a part is offset by its proportionally fewer rows/columns.

<a id="pdf-9c5df3bb4a04-p032-b005"></a>
<!-- pdf-source: page=32; block=5; confidence=0.85 -->
**§6.3 — Row pruning.** The pruning step defines bad rows/columns of each $A_u$; the key definition below abstracts the hypergraph property that decides which rows are bad.

<a id="pdf-9c5df3bb4a04-p033-b001"></a>
<!-- pdf-source: page=33; block=1; confidence=0.85 -->
**Definition 6.6 (Butterfly Degree).** For a (k−1)-uniform hypergraph $\mathcal{H}_u$ on [n] and $C,C'\in\mathcal{H}_u$, let
$$\mathcal{R}(C,C')=\Big\{R\subseteq[n]\times[2]:\ |R|=k-1,\ \{|R\cap(C\times\{1\})|,\,|R\cap(C'\times\{2\})|\}=\{\lceil\tfrac{k-1}{2}\rceil,\lfloor\tfrac{k-1}{2}\rfloor\}\Big\}.$$
For $S\subseteq[n]\times[2]$, the butterfly degree of S in $\mathcal{H}_u$ is
$$\gamma_u(S)=\sum_{\substack{(C,C')\in\mathcal{H}_u\times\mathcal{H}_u\\ C\neq C'}}\ \sum_{R\in\mathcal{R}(C,C')}\mathbf{1}\big[\,S\cap(C\times\{1\}\cup C'\times\{2\})=R\,\big].$$
The total butterfly degree is $\gamma(S)=\sum_{u\in[p]}\gamma_u(S)$. This generalizes the butterfly degree of [AGK21], so named because it counts butterfly-shaped graphs.

<a id="pdf-9c5df3bb4a04-p033-b002"></a>
<!-- pdf-source: page=33; block=2; confidence=0.82 -->
**Lemma 6.7 (Butterfly Degree and the $\ell_1$ norm of rows of the Kikuchi matrix).** Let $\mathcal{H}_u$ be a (k+1)-uniform hypergraph on [n] and $A_u$ its associated matrix (Definition 6.2). Then for any $S\subseteq[n]\times[2]$,
$$\gamma_u(S)\ \ge\ \sum_{T}\big|A_u(S,T)\big|.$$

<a id="pdf-9c5df3bb4a04-p033-b003"></a>
<!-- pdf-source: page=33; block=3; confidence=0.80 -->
**Proof.** For k odd, $\gamma_u(S)$ counts the pairs $(C,C')\in\mathcal{H}_u\times\mathcal{H}_u$, $C\neq C'$, with $|S\cap(C\times\{1\})|=|S\cap(C'\times\{2\})|=\tfrac{k+1}{2}$. For k even, it counts the pairs with $|S\cap(C\times\{1\})|=\tfrac{k}{2}$ and $|S\cap(C'\times\{2\})|=\tfrac{k+2}{2}$, or $|S\cap(C\times\{1\})|=\tfrac{k+2}{2}$ and $|S\cap(C'\times\{2\})|=\tfrac{k}{2}$. The bound follows. $\square$

<a id="pdf-9c5df3bb4a04-p033-b004"></a>
<!-- pdf-source: page=33; block=4; confidence=0.85 -->
**Definition 6.8 ($\Delta$-Bad rows in A).** The set of $\Delta$-bad rows is
$$\mathcal{B}:=\{\,S:\ \exists\,u\in[p],\ \gamma_u(S)\ge\Delta\,\}.$$
$\mathcal{B}$ does not depend on the values of the $b_{u,C}$'s.

<a id="pdf-9c5df3bb4a04-p033-b005"></a>
<!-- pdf-source: page=33; block=5; confidence=0.86 -->
By Lemma 6.7, every non-bad row has $\ell_1$-norm that is not too large. The next lemma bounds $|\mathcal{B}|$; its proof is deferred to §6.5.

<a id="pdf-9c5df3bb4a04-p033-b006"></a>
<!-- pdf-source: page=33; block=6; confidence=0.85 -->
**Lemma 6.9 (Bound on bad rows).** Let A be the Kikuchi matrix of the polynomial f obtained from an (ε,ℓ)-regular p-bipartite polynomial ψ of total degree k, defined by (k−1)-uniform hypergraphs $\{\mathcal{H}_u\}_{u\in[p]}$. Let $\mathcal{B}$ be the set of $\Delta$-bad rows for
$$\Delta=c^{\,k-1}\,\frac{1}{\varepsilon^4}\,\Big(\ln\tfrac{32pN}{\varepsilon^2 D}\Big)^{2(k-1)}\qquad(6.7),$$
with c an absolute constant. Then $|\mathcal{B}|\le \varepsilon^2 D/16$.

<a id="pdf-9c5df3bb4a04-p034-b001"></a>
<!-- pdf-source: page=34; block=1; confidence=0.92 -->
**Corollary 6.10 (Row pruning error).** Let $A_{\mathcal{G}/\mathcal{G}}$ be $A$ with all rows/columns in $\mathcal{B}$ zeroed out. Then $\|A - A_{\mathcal{G}/\mathcal{G}}\|_{\infty\to 1} \le \dfrac{m^2 D \varepsilon^2}{2p}$.

<a id="pdf-9c5df3bb4a04-p034-b002"></a>
<!-- pdf-source: page=34; block=2; confidence=0.86 -->
**Proof (Cor. 6.10 from Lemma 6.9).** Set $B = A - A_{\mathcal{G}/\mathcal{G}}$. For any row/column index $S \subseteq [n]\times[2]$, the $\ell_1$ norm of the $S$-th row of $B$ (indeed of $A$) is at most $\sum_{u=1}^p |\mathcal{H}_u|^2$, since each ordered pair $(C,C')\in \mathcal{H}_u\times\mathcal{H}_u$ contributes at most one nonzero entry, at column $T = S \pm C(1) \pm C'(2)$ (valid only if $|T|=\ell$). As $|\mathcal{H}_u| \le 2m/p$, this is $\le p\cdot 4m^2/p^2 = 4m^2/p$. If $B(S,T)\ne 0$ then $S$ or $T$ lies in $\mathcal{B}$, so $\|B\|_{\infty\to1} \le \sum_{S\in\mathcal{B}}\sum_T |B(S,T)| + \sum_{T\in\mathcal{B}}\sum_S|B(S,T)| \le 2|\mathcal{B}|\cdot 4m^2/p$. Since $|\mathcal{B}| \le \varepsilon^2 D/16$, this is $\le m^2 D\varepsilon^2/(2p)$. $\square$

<a id="pdf-9c5df3bb4a04-p034-b003"></a>
<!-- pdf-source: page=34; block=3; confidence=0.85 -->
**Lemma 6.11.** Let $A$ be the Kikuchi matrix of the polynomial $f$ obtained from an $(\varepsilon,\ell)$-regular $p$-bipartite polynomial $\psi$ of total degree $k$, defined by $(k+1)$-uniform hypergraphs $\{\mathcal{H}_u\}_{u\in[p]}$ and coefficients $\{b_{u,C}\}_{u\in[p],\,C\in\mathcal{H}_u}$. Then with probability $1 - \tfrac{1}{10\,\mathrm{poly}(n)}$ over the draw of the $b_{u,C}$,
$$\|A_{\mathcal{G}/\mathcal{G}}\|_{\infty\to1} \le O(\log^2 m)\, N\Delta\,(\log N + \log\log m) + O(\log m)\sqrt{\tfrac{N D m^2 (\log N + \log\log m)}{p}}.$$

<a id="pdf-9c5df3bb4a04-p034-b004"></a>
<!-- pdf-source: page=34; block=4; confidence=0.85 -->
**Proof (finishing Lemma 6.5).** By Corollary 6.10 and Lemma 6.11, with probability $1 - \tfrac{1}{10\,\mathrm{poly}(n)}$,
$$\|A\|_{\infty\to1} \le \|A-A_{\mathcal{G}/\mathcal{G}}\|_{\infty\to1} + \|A_{\mathcal{G}/\mathcal{G}}\|_{\infty\to1} \le \tfrac{m^2D\varepsilon^2}{2p} + O\!\big(\log^2 m\cdot N\Delta(\log N+\log\log m)\big) + O\!\big(\log m\cdot \sqrt{NDm^2(\log N+\log\log m)/p}\big).$$
It remains to bound $N/D$.

<a id="pdf-9c5df3bb4a04-p034-b005"></a>
<!-- pdf-source: page=34; block=5; confidence=0.82 -->
**Claim 6.12.** $N/D \le 16^{k+1}\,(n/\ell)^{k+1}$, where $D$ is defined as in Eq. (6.6).

<a id="pdf-9c5df3bb4a04-p034-b006"></a>
<!-- pdf-source: page=34; block=6; confidence=0.85 -->
**Proof.** $N/D \le \binom{2n}{\ell}\big/\binom{2n-2(k-1)}{\ell-(k-1)} \le (n/\ell)^{k-1}\cdot\Big(\tfrac{\ell}{\ell-(k-1)}\cdot 4\cdot\tfrac{n}{2n-\ell-(k-1)}\Big)^{k-1} \le (n/\ell)^{k-1}\cdot 16^{k-1}$, for $n$ sufficiently large, using $\ell \ge 2(k-1)$. $\square$

<a id="pdf-9c5df3bb4a04-p035-b001"></a>
<!-- pdf-source: page=35; block=1; confidence=0.72 -->
**Proof (cont.).** By Claim 6.12, the term $O(\log_2^2 m\cdot N\Delta(\log N+\log\log m))$ is at most $m^2 D\varepsilon^2/(4p)$. Using $m \le n^{\log_2 n}$:
$$\tfrac{O(1)p}{\varepsilon^2 D}(\log_2 m)^2 N\Delta(\log N+\log\log m) \le O(1)^{k-1}\tfrac{p}{\varepsilon^2 D}(\log_2 n)^5 N\ell\cdot\tfrac{1}{\varepsilon^4}\Big(\ln\tfrac{32pN}{\varepsilon^2 D}\Big)^{2(k-1)} \le O(1)^{k-1}\tfrac{\ell p N}{\varepsilon^6 D}(\log_2 n)^5(\ln^2 n)^{2(k-1)} \le O(1)^{k-1}\tfrac{\ell p}{\varepsilon^6}(n/\ell)^{k-1}(\log_2 n)^{4k+1} \le m^2,$$
using $p\le\varepsilon^2 m$, $m\le n^{\log_2 n}$, and the lower bound on $m$ in Theorem 5.4. Similarly $O(\log m\sqrt{NDm^2(\log N+\log\log m)/p}) \le m^2 D\varepsilon^2/(4p)$, since $O(1)\tfrac{p}{\varepsilon^2 D}\log_2 m\sqrt{NDm^2(\cdots)/p} \le O(1)(\log_2 n)^{2.5}\tfrac{m}{\varepsilon^2}\sqrt{pN\ell/D} \le O(1)^{k-1}(\log_2 n)^{2.5}\tfrac{m}{\varepsilon^2}\sqrt{p\ell(n/\ell)^{k-1}} \le m^2$, again using the lower bound on $m$ in Theorem 5.4. Hence $\|A\|_{\infty\to1} \le m^2 D\varepsilon^2/p$, which finishes the proof. It remains to prove Lemma 6.11 and Lemma 6.9.

<a id="pdf-9c5df3bb4a04-p035-b002"></a>
<!-- pdf-source: page=35; block=2; confidence=0.95 -->
**6.4 Bounding the $\infty\to1$ norm of the "good rows": proof of Lemma 6.11**

<a id="pdf-9c5df3bb4a04-p035-b003"></a>
<!-- pdf-source: page=35; block=3; confidence=0.85 -->
Write $G := A_{\mathcal{G}/\mathcal{G}}$ (Kikuchi matrix $A$ with rows in $\mathcal{B}$ zeroed) and $G_u := (A_u)_{\mathcal{G}/\mathcal{G}}$ (rows and columns in $\mathcal{B}$ zeroed); since $A=\sum_{u=1}^p A_u$, we have $G=\sum_{u=1}^p G_u$. Proof idea: split $G=\sum_{i,j}G^{(i,j)}$ into $O(\log^2 m)$ submatrices such that (1) each entry $(S,T)$ is nonzero in exactly one $G^{(i,j)}$, equal to $G(S,T)$ there, and (2) all nonzero rows/columns of a given $G^{(i,j)}$ have roughly the same butterfly degree ("row bucketing"). Property (2) converts a scaled spectral-norm bound on $G^{(i,j)}$ into an $\infty\to1$ bound; two proofs of this are given (Matrix Bernstein inequality, and the trace moment method, the latter reused in Section 8). Combining the $\|G^{(i,j)}\|_2$ bounds bounds $\|G\|_{\infty\to1}$.

<a id="pdf-9c5df3bb4a04-p036-b001"></a>
<!-- pdf-source: page=36; block=1; confidence=0.88 -->
**Definition 6.13 (Row bucketing).** Let $d := \dfrac{4m^2 D}{pN} \ge 1$. Partition the rows of $G$ into $\mathcal{F}_0\cup\mathcal{F}_1\cup\cdots\cup\mathcal{F}_t$: set $\mathcal{F}_0 := \{S\in\mathcal{G} : \gamma(S)\le d\}$, and for $1\le i\le t$, $\mathcal{F}_i := \{S\in\mathcal{G} : 2^{i-1}d < \gamma(S) \le 2^i d\}$. Since $\gamma(S)\le\sum_{u=1}^p|\mathcal{H}_u|^2\le m^2$ and $d\ge1$, every good row index $S\in\mathcal{G}$ lies in some $\mathcal{F}_i$ with $i\le t = 2\log_2 m$, so the $\mathcal{F}_i$ (for $i\le 2\log_2 m$) partition all rows of $G$. For $i,j\in\{0,\dots,t\}$, $G^{(i,j)}$ is the submatrix with $G^{(i,j)}(S,T)=G(S,T)$ when $S\in\mathcal{F}_i,\,T\in\mathcal{F}_j$, and $=0$ otherwise.

<a id="pdf-9c5df3bb4a04-p036-b002"></a>
<!-- pdf-source: page=36; block=2; confidence=0.90 -->
**Lemma 6.14 (Size of $\mathcal{F}_i$).** For the partition $\mathcal{F}_0\cup\cdots\cup\mathcal{F}_t$ ($t\le 2\log_2 m$) of Definition 6.13: $|\mathcal{F}_0| \le N$ and $|\mathcal{F}_i| \le 2^{1-i}N$ for each $i\in[t]$.

<a id="pdf-9c5df3bb4a04-p036-b003"></a>
<!-- pdf-source: page=36; block=3; confidence=0.85 -->
**Proof.** The bound $|\mathcal{F}_0|\le N$ is trivial. For $i\ge1$: $2^{i-1}d\,|\mathcal{F}_i| < \sum_{S\in\mathcal{F}_i}\gamma(S) \le \sum_S\gamma(S) \le D\sum_{u=1}^p|\mathcal{H}_u|^2 = D\cdot\tfrac{4m^2}{p} = dN$, since each ordered pair $(C,C')\in\mathcal{H}_u\times\mathcal{H}_u$ with $C\ne C'$ appears in exactly $D$ entries of the original matrix $A$. Hence $|\mathcal{F}_i| < 2^{1-i}N$. $\square$

<a id="pdf-9c5df3bb4a04-p036-b004"></a>
<!-- pdf-source: page=36; block=4; confidence=0.82 -->
**Lemma 6.15 (Spectral norm of $G^{(i,j)}$).** For the matrices of Definition 6.13, for each $i,j\in\{0,\dots,t\}$, with probability $1 - \tfrac{1}{\log_2^2 m\cdot\mathrm{poly}(n)}$ over the draw of the $b_{u,C}$,
$$\|G^{(i,j)}\|_2 \le O(1)\,\Delta(\log N+\log\log m) + O(1)\,2^{0.5\max(i,j)}\sqrt{d(\log N+\log\log m)}.$$

<a id="pdf-9c5df3bb4a04-p036-b005"></a>
<!-- pdf-source: page=36; block=5; confidence=0.83 -->
**Proof of Lemma 6.11.** There are at most $4\log_2^2 m$ pairs $(i,j)$ with $i,j\le t=2\log_2 m$; applying Lemma 6.15 and a union bound gives, with probability $\ge 1-\tfrac{1}{10\,\mathrm{poly}(n)}$, the bound $\|G^{(i,j)}\|_2 \le O(1)\Delta(\log N+\log\log m) + O(1)2^{0.5\max(i,j)}\sqrt{d(\log N+\log\log m)}$ simultaneously for all $i,j$; condition on this event. Key fact: for any $y,z\in\{\pm1\}^N$,
$$y^\top G^{(i,j)} z = y_{\mathcal{F}_i}^\top G^{(i,j)} z_{\mathcal{F}_j} \le \|y_{\mathcal{F}_i}\|_2\,\|z_{\mathcal{F}_j}\|_2\,\|G^{(i,j)}\|_2 = \sqrt{|\mathcal{F}_i||\mathcal{F}_j|}\,\|G^{(i,j)}\|_2,$$
using that only rows in $\mathcal{F}_i$ and columns in $\mathcal{F}_j$ are nonzero in $G^{(i,j)}$, then the spectral-norm definition. Hence $\|G^{(i,j)}\|_{\infty\to1} = \max_{y,z\in\{\pm1\}^N} y^\top G^{(i,j)} z \le \sqrt{|\mathcal{F}_i||\mathcal{F}_j|}\,\|G^{(i,j)}\|_2$. By the triangle inequality for $\|\cdot\|_{\infty\to1}$: $\|G\|_{\infty\to1} \le \sum_{i=0}^t\sum_{j=0}^t \|G^{(i,j)}\|_{\infty\to1} \le \sum_{i=0}^t\sum_{j=0}^t \sqrt{|\mathcal{F}_i||\mathcal{F}_j|}\,\|G^{(i,j)}\|_2$. [proof continues beyond this page]

<a id="pdf-9c5df3bb4a04-p037-b001"></a>
<!-- pdf-source: page=37; block=1; confidence=0.75 -->
**Proof (concl. of Lemma 6.11).** The tail of the chain of inequalities gives
$$\le O(Nt^2\Delta(\log N+\log\log m)) + 2\sum_{i=0}^{t}\sum_{j=i}^{t} N\sqrt{2^{2-i-j}}\cdot O(1)\cdot 2^{0.5j}\sqrt{d(\log N+\log\log m)}$$
$$= O(Nt^2\Delta(\log N+\log\log m)) + O\big(N\sqrt{d(\log N+\log\log m)}\big)\sum_{i=0}^{t}\sum_{j=i}^{t} 2^{-0.5i}$$
$$= O(Nt^2\Delta(\log N+\log\log m)) + O\big(Nt\sqrt{d(\log N+\log\log m)}\big).$$
As $t=O(\log m)$ and $d=\tfrac{4m^2 D}{pN}$, Lemma 6.11 follows.

<a id="pdf-9c5df3bb4a04-p037-b002"></a>
<!-- pdf-source: page=37; block=2; confidence=0.90 -->
Completing the proof of Lemma 6.15; two proofs are given: (i) a short one via the Matrix Bernstein inequality, and (ii) one via the trace moment method (used later in Section 8).

<a id="pdf-9c5df3bb4a04-p037-b003"></a>
<!-- pdf-source: page=37; block=3; confidence=0.95 -->
**6.4.1 Proof of Lemma 6.15 using Matrix Bernstein inequality**

<a id="pdf-9c5df3bb4a04-p037-b004"></a>
<!-- pdf-source: page=37; block=4; confidence=0.92 -->
**Proof (Lemma 6.15, Matrix Bernstein).** Fix $(i,j)$ and write $G^{(i,j)}=\sum_{u\ge1}G^{(i,j)}_u$; the $G^{(i,j)}_u$ are independent since $b_{u,C},b_{u',C'}$ are independent for $u\ne u'$. Apply Matrix Bernstein (Fact 3.1) to them.

Every nonzero row/column $S$ of the $G^{(i,j)}_u$ satisfies $S\in\mathcal G$, so $\gamma_u(S)\le\Delta$; hence each row/column has $\ell_1$-norm $\le\Delta$ and $\|G^{(i,j)}_u\|_2\le\Delta$ always.

Variance term: let $M=\mathbb E\big[\sum_{u\ge1}G^{(i,j)}_u(G^{(i,j)}_u)^{\top}\big]$ (expectation over the $b_{u,C}$). The $\ell_1$-norm of row $S$ of $M$ is $\sum_{u\ge1}\sum_{T\in\mathcal F_i}\sum_{R\in\mathcal F_j}\mathbb E[G^{(i,j)}_u(S,R)\,G^{(i,j)}_u(T,R)]$. As the $b_{u,C}$ are mean zero, a term is nonzero iff there exist $C\ne C'\in\mathcal H_u$ with $S\,\triangle\,R=C(1)\,\triangle\,C'(2)$ and either $T\,\triangle\,R=C(1)\,\triangle\,C'(2)$ or $T\,\triangle\,R=C(2)\,\triangle\,C'(1)$, and then the term is $\le1$. For each $u$ there are $\le\gamma_u(S)$ such $R$, each contributing $\le2$ (two choices of $T$), so the row $\ell_1$-norm is $\le2\sum_u\gamma_u(S)=2\gamma(S)$. Since $S\in\mathcal F_i$, $\gamma(S)\le2^{i}d$, giving $\|M\|_2\le2^{i+1}d$. By symmetry in $i,j$ one may take $\sigma^2=2\cdot2^{\max(i,j)}d$. Fact 3.1 then yields, with probability $\ge1-\tfrac{1}{\log_2^2 m\cdot\mathrm{poly}(N)}\ (\ge1-\tfrac{1}{\log_2^2 m\cdot\mathrm{poly}(n)})$, that $\|G^{(i,j)}\|_2\le O\big(\Delta(\log N+\log\log m)+\sqrt{2^{\max(i,j)}d(\log N+\log\log m)}\big)$, finishing the proof.

<a id="pdf-9c5df3bb4a04-p037-b005"></a>
<!-- pdf-source: page=37; block=5; confidence=0.95 -->
**6.4.2 Proof of Lemma 6.15 using trace moment method**

<a id="pdf-9c5df3bb4a04-p037-b006"></a>
<!-- pdf-source: page=37; block=6; confidence=0.85 -->
**Proof (Lemma 6.15, trace moment method).** Set $Z=G^{(i,j)}$, $Z_u=G^{(i,j)}_u$, and $r\in\mathbb N$. Since $\|Z\|_2^{2r}\le\operatorname{tr}((ZZ^{\top})^{r})$, the proof proceeds in two steps: first upper-bound $\mathbb E[\operatorname{tr}((ZZ^{\top})^{r})]$ by a combinatorial quantity — the number of *even walk sequences* (defined below) — then bound the number of such sequences.

<a id="pdf-9c5df3bb4a04-p038-b001"></a>
<!-- pdf-source: page=38; block=1; confidence=0.85 -->
**Definition 6.16 (walk sequence).** For $S\in\mathcal F_i$, a sequence $(u_1,C_1,C'_1),\dots,(u_{2r},C_{2r},C'_{2r})$ with $u_h\in[p]$ and $C_h\ne C'_h\in\mathcal H_{u_h}$ is a *walk sequence* for $S$ if the sets $T_h:=S\,\triangle\,\bigtriangleup_{j< h}\big(C_j(1)\,\triangle\,C'_j(2)\big)$ each have size exactly $\ell$ and the entries $Z_{u_{2h-1}}(T_{2h-1},T_{2h})$ and $Z_{u_{2h}}(T_{2h+1},T_{2h})$ are nonzero for each $h=1,\dots,r$. It is *even* if every $(u,Q)$ occurs an even number of times in the multiset $\{(u_h,C_h),(u_h,C'_h)\}_{h\in[2r]}$.

<a id="pdf-9c5df3bb4a04-p038-b002"></a>
<!-- pdf-source: page=38; block=2; confidence=0.90 -->
**Proposition 6.17.** $\mathbb E[\operatorname{tr}((ZZ^{\top})^{r})]\le\sum_{S\in\mathcal F_i}\big|\{\text{even walk sequences }(u_1,C_1,C'_1),\dots,(u_{2r},C_{2r},C'_{2r})\text{ for }S\}\big|.$

<a id="pdf-9c5df3bb4a04-p038-b003"></a>
<!-- pdf-source: page=38; block=3; confidence=0.90 -->
**Lemma 6.18 (Sequence counting).** For each $S\in\mathcal F_i$, the number of even walk sequences $(u_1,C_1,C'_1),\dots,(u_{2r},C_{2r},C'_{2r})$ for $S$ is at most $(4r)^{r}\big(2^{\max(i,j)}d+r\Delta^{2}\big)^{r}.$

<a id="pdf-9c5df3bb4a04-p038-b004"></a>
<!-- pdf-source: page=38; block=4; confidence=0.70 -->
**Proof step (6.17 + 6.18 ⟹ 6.15).** Combining gives $\mathbb E[\operatorname{tr}((ZZ^{\top})^{r})]\le|\mathcal F_i|(4r)^{r}(2^{\max(i,j)}d+r\Delta^{2})^{r}\le N(4r)^{r}(2^{\max(i,j)}d+r\Delta^{2})^{r}$. By Markov's inequality, $\mathbb P[\|Z\|_2\ge\lambda]\le\mathbb E[\|Z\|_2^{2r}]/\lambda^{2r}\le N(4r)^{r}(2^{\max(i,j)}d+r\Delta^{2})^{r}/\lambda^{2r}$. Taking $r=\lceil\log_2 N+\log_2\log_2 m\rceil$ and $\lambda=c\sqrt{r}\,\sqrt{2^{\max(i,j)}d+r\Delta^{2}}$ for a large enough absolute constant $c$ gives $\mathbb P\big[\|Z\|_2\ge c\sqrt{2^{\max(i,j)}dr+\Delta^{2}r^{2}}\big]\le N^{4r}/c^{2r}\le\tfrac{1}{\mathrm{poly}(N)\cdot\mathrm{polylog}(m)}$. Finally $\sqrt{2^{\max(i,j)}dr+\Delta^{2}r^{2}}\le\sqrt{2^{\max(i,j)}dr}+\Delta r$, proving Lemma 6.15 since $r\le O(\log N+\log\log m)$.

<a id="pdf-9c5df3bb4a04-p038-b005"></a>
<!-- pdf-source: page=38; block=5; confidence=0.75 -->
**Proof of Proposition 6.17.** Expand $\mathbb E[\operatorname{tr}((ZZ^{\top})^{r})]=\sum_{(u_1,S_1),\dots,(u_{2r},S_{2r})}\mathbb E\big[\prod_{h=1}^{r}Z_{u_{2h-1}}(S_{2h-1},S_{2h})\,Z_{u_{2h}}(S_{2h+1},S_{2h})\big]$, with the cyclic convention $u_{2r+1}:=u_1$, $S_{2r+1}:=S_1$. Reindexing over $S\in\mathcal F_i$ and walk sequences for $S$, and rewriting each $Z$-entry through its $b$-variables, this equals $\sum_{S\in\mathcal F_i}\sum_{\text{walk seq for }S}\mathbb E\big[\prod_{h=1}^{r}b_{u_{2h-1},C_{2h-1}}b_{u_{2h-1},C'_{2h-1}}b_{u_{2h},C_{2h}}b_{u_{2h},C'_{2h}}\big].$

<a id="pdf-9c5df3bb4a04-p039-b001"></a>
<!-- pdf-source: page=39; block=1; confidence=0.85 -->
**Proof of Proposition 6.17 (concl.).** Each such expectation vanishes unless the walk sequence is even, so the sum is $\le\sum_{S\in\mathcal F_i}\#\{\text{even walk sequences }(u_1,C_1,C'_1),\dots,(u_{2r},C_{2r},C'_{2r})\text{ for }S\}$, establishing the claim.

<a id="pdf-9c5df3bb4a04-p039-b002"></a>
<!-- pdf-source: page=39; block=2; confidence=0.75 -->
**Proof of Lemma 6.18.** Bound the sequences per $S$ by an encoding argument. Say $C,C'\in\mathcal H_u$ *extends* $S\in\mathcal F_i$ if $Z_u(S,\,S\triangle C(1)\triangle C'(2))$ is well-defined and nonzero (for $S\in\mathcal F_j$, require $Z_u(S\triangle C(1)\triangle C'(2),\,S)$ nonzero). Encoding:

(1) Choose $k\in[r]$, the number of distinct $u$'s. Evenness forces $k\le r$: no $u_h$ can appear only once, else $(u_h,C_h)$ must pair with $(u_h,C'_h)$ though $C_h\ne C'_h$.

(2) Choose $2k$ locations $L\subseteq[2r]$ marking the first and last occurrence of each distinct $u_h$, $h\in[k]$.

(3) Choose a perfect matching $\pi:L\to[k]$ with $t_1<t_2<\dots<t_k$, where $t_h$ is the first preimage of $h$ in $L$ (order inherited from $[2r]$) and $t'_h$ the second preimage.

(4) Process steps $t=1,\dots,2r$, knowing the current set $S_t$: (a) if $t=t_h$: choose an unused $u\in[p]$ and $C,C'\in\mathcal H_u$ extending $S_t$, set the $t$-th element to $(u,C,C')$; (b) if $t\ne t_h,t'_h$ for all $h$: pick an already-chosen $u$ not past its last occurrence (per $\pi$) and $C,C'\in\mathcal H_u$ extending $S_t$, set $(u,C,C')$; (c) if $t=t'_h$: take $u=u_h$ and the unique $C,C'\in\mathcal H_u$ that extends $S_t$ and keeps the sequence even, set $(u,C,C')$ or $(u,C',C)$.

<a id="pdf-9c5df3bb4a04-p039-b003"></a>
<!-- pdf-source: page=39; block=3; confidence=0.80 -->
**Proof of Lemma 6.18 (counting).** With the first three steps fixed: a new-$u$ step (case a) has $\sum_u\gamma_u(S_t)\le2^{\max(i,j)}d$ ways to pick $(u,C,C')$; an old-$u$ step (case b) has $z\Delta$ ways ($z$ choices for $u$, then $\gamma_u(S_t)\le\Delta$ for the pair $C,C'$); a $t=t'_h$ step (case c) has $2$ choices. Over all steps: $(2^{\max(i,j)}d)^{z}\cdot2^{z}\cdot(z\Delta)^{2r-2z}$. Treating $z$ as fixed, Steps (2) and (3) contribute $\binom{2r}{2z}$ and $\tfrac{(2z)!}{2^z z!}$ respectively. Combining, $\#\{\text{even, well-formed for }S\}\le\sum_{z=1}^{r}\binom{2r}{2z}\tfrac{(2z)!}{2^z z!}(2^{\max(i,j)}d)^{z}\cdot2^{z}\cdot(z\Delta)^{2r-2z}$. We now observe that $\binom{2r}{2z}\tfrac{(2z)!}{z!}z^{2r-2z} = \tfrac{(2r)!}{(2r-2z)!\,z!}\cdot z^{2r-2z}$.

<a id="pdf-9c5df3bb4a04-p040-b001"></a>
<!-- pdf-source: page=40; block=1; confidence=0.75 -->
**Proof (continued).** The chain continues:
$$= \frac{(2r)!}{r!\,r!}\cdot\frac{(r-z)!(r-z)!}{(2r-2z)!}\cdot\frac{r!}{(r-z)!}\cdot\frac{r!}{z!(r-z)!}\cdot z^{2r-2z} \le 2^{2r}\cdot1\cdot r^z\cdot\binom{r}{z}\cdot r^{2r-2z} \le (4r)^r\binom{r}{z}r^{r-z}.$$
Thus,
$$\sum_{z=1}^{r}\binom{2r}{2z}\frac{(2z)!}{2^z z!}(2^{\max(i,j)}d)^z\cdot2^z\cdot(z\Delta)^{2r-2z} \le (4r)^r\sum_{z=1}^{r}\binom{r}{z}(2^{\max(i,j)}d)^z(r\Delta^2)^{r-z} \le (4r)^r(2^{\max(i,j)}d + r\Delta^2)^r,$$
which finishes the proof.

<a id="pdf-9c5df3bb4a04-p040-b002"></a>
<!-- pdf-source: page=40; block=2; confidence=0.95 -->
**6.5 Bounding the number of bad rows: proof of Lemma 6.9**

<a id="pdf-9c5df3bb4a04-p040-b003"></a>
<!-- pdf-source: page=40; block=3; confidence=0.88 -->
Let $\mathcal U_\ell$ be the uniform distribution on subsets of $[n]\times[2]$ of size exactly $\ell$. To bound the fraction of bad rows (the size of $\mathcal B$), analyze the probability that a draw $S\leftarrow\mathcal U_\ell$ indexes a bad row of the Kikuchi matrix $A$, by viewing $\gamma_u(S)$ as a degree-$(k-1)$ polynomial in the indicator vector of $S$.

<a id="pdf-9c5df3bb4a04-p040-b004"></a>
<!-- pdf-source: page=40; block=4; confidence=0.72 -->
**Lemma 6.19 (Polynomial View of $\gamma_u(S)$).** Let $P_u$ be the polynomial in variables $\{x_{(i,b)}\}_{i\le n,\,b\in\{1,2\}}$ given by
$$P_u(x)=\sum_{\substack{(C,C')\in\mathcal H_u\times\mathcal H_u\\ C\ne C'}}\ \sum_{R\in\mathcal R(C,C')} x_R,\qquad x_R:=\prod_{(i,b)\in R} x_{i,b}.$$
Then for every $S\subseteq[n]\times[2]$, $\gamma_u(S)\le P_u(\mathbf 1_S)$, where $\mathbf 1_S$ is the 0-1 indicator of $S$ (a $1$ in coordinate $(i,b)$ iff $(i,b)\in S$).

<a id="pdf-9c5df3bb4a04-p040-b005"></a>
<!-- pdf-source: page=40; block=5; confidence=0.75 -->
**Proof.** By Definition 6.6,
$$\gamma_u(S)=\sum_{(C,C'),\,C\ne C'}\sum_{R\in\mathcal R(C,C')}\mathbf 1\big(S\cap(C(1)\cup C'(2))=R\big)\le\sum_{(C,C'),\,C\ne C'}\sum_{R\in\mathcal R(C,C')}\mathbf 1(R\subseteq S)=P_u(\mathbf 1_S).$$

<a id="pdf-9c5df3bb4a04-p040-b006"></a>
<!-- pdf-source: page=40; block=6; confidence=0.70 -->
It therefore suffices to upper bound $\Pr_{\mathcal U_\ell}[P_u(x)\ge\Delta]$. This is replaced by the more tractable product distribution $\mathcal U'_\ell$ on $x$, justified by the next lemma.

<a id="pdf-9c5df3bb4a04-p040-b007"></a>
<!-- pdf-source: page=40; block=7; confidence=0.68 -->
**Lemma 6.20 (Switching to a Product Distribution).** Let $\mathcal U'_\ell$ be the distribution including each $(i,b)\in[n]\times[2]$ in $S$ independently with probability $q=\dfrac{\ell}{2n(1+\beta)}$ (equivalently each $x_{i,b}\sim\mathrm{Bernoulli}(q)$), where $\beta=\max\Big\{\sqrt{\tfrac{4}{\ell}\ln\tfrac{32pN}{\varepsilon^2 D}},\ \tfrac{4}{\ell}\ln\tfrac{32pN}{\varepsilon^2 D}\Big\}$. Then for any $\lambda$,
$$\Pr_{x\leftarrow\mathcal U_\ell}[P_u(x)\ge\lambda]\ \le\ \Pr_{x\leftarrow\mathcal U'_\ell}[P_u(x)\ge\lambda]+\frac{\varepsilon^2 D}{32pN}.$$

<a id="pdf-9c5df3bb4a04-p041-b001"></a>
<!-- pdf-source: page=41; block=1; confidence=0.90 -->
**Remark.** Under $\mathcal U'_\ell$ the sampled set does not always have size exactly $\ell$.

<a id="pdf-9c5df3bb4a04-p041-b002"></a>
<!-- pdf-source: page=41; block=2; confidence=0.70 -->
**Proof.** Couple $\mathcal U'_\ell$ with $\mathcal U_\ell$: sample $T\leftarrow\mathcal U'_\ell$, then let $S$ be a uniformly random size-$\ell$ subset of $T$ (abort if $|T|<\ell$); let $\mathcal J$ be the resulting joint law. By a Chernoff bound, for every $\delta\in[0,1]$,
$$\Pr_{T\sim\mathcal U'_\ell}\big[|T|\le(1-\delta)(1+\beta)\ell\big]\le\exp\!\Big(-\tfrac{\delta^2\ell(1+\beta)}{2}\Big).$$
Setting $\delta=1-\tfrac{1}{1+\beta}$ gives $\Pr_{T\sim\mathcal U'_\ell}[|T|<\ell]\le\tfrac{\varepsilon^2 D}{32pN}$, since $\tfrac{\beta^2}{1+\beta}\ge\tfrac{2}{\ell}\ln\tfrac{32pN}{\varepsilon^2 D}$ by the choice of $\beta$. Since $P_u(T)\ge P_u(S)$ for any $S\subseteq T$, if $P_u(T)\le\lambda$ then $P_u(S)\le\lambda$ regardless of $S$; hence
$$\Pr_{S\leftarrow\mathcal U_\ell}[P_u(S)\ge\lambda]\le\Pr_{(S,T)\sim\mathcal J}\big[P_u(T)\ge\lambda\mid|T|\ge\ell\big]\le\Pr_{T\leftarrow\mathcal U'_\ell}[P_u(T)\ge\lambda]+\tfrac{\varepsilon^2 D}{32pN}.$$

<a id="pdf-9c5df3bb4a04-p041-b003"></a>
<!-- pdf-source: page=41; block=3; confidence=0.80 -->
**Proof of Lemma 6.9.** Bound $\Pr_{\mathcal U'_\ell}[P_u(x)\ge\Delta]$ via the polynomial concentration inequality (Fact 3.2). First the mean: with $q=\tfrac{\ell}{2n}(1+\beta)$,
$$\mathbb E_{x\leftarrow\mathcal U'_\ell}[P_u(x)]=\sum_{(C,C'),\,C\ne C'}q^{k-1}\,|\mathcal R(C,C')|=w_k\,q^{k-1}\,|\mathcal H_u|\,(|\mathcal H_u|-1),$$
where $w_k := \binom{k-1}{(k-1)/2}^2$ if $k$ is odd and $w_k := 2\binom{k-1}{k/2}\binom{k-1}{(k-2)/2}$ if $k$ is even. Let $\eta=4\ln\tfrac{32pN}{\varepsilon^2 D}$; then $\eta\ge4\ln32\ge1$ (using $N/D\ge1$, $p\ge1$, $\varepsilon<1$), and $\tfrac{1+\beta}{2}\le\eta$. By regularity of $\psi$ (described by $\{\mathcal H_u\}_{u\in[p]}$), $\deg_u(Q)\le\tfrac{1}{\varepsilon^2}(n/\ell)^{k/2-1-|Q|}$ for all $Q\subseteq[n]$ with $|Q|\le(k-2)/2$; in particular $|\mathcal H_u|=\deg_u(\emptyset)\le\tfrac{1}{\varepsilon^2}(n/\ell)^{k/2-1}$, so
$$\mathbb E_{\mathcal U'_\ell}[P_u(x)]\le w_k\Big(\tfrac{1+\beta}{2}\Big)^{k-1}\tfrac{1}{\varepsilon^4}\tfrac{\ell}{n}\le w_k\,\eta^{k-1}\tfrac{1}{\varepsilon^4}\tfrac{\ell}{n}.$$
Define, for $r=0,\dots,k-1$, $\nu_r=\max_{|R|=r}\sum_{(C,C'),\,C\ne C'}\sum_{R'\in\mathcal R(C,C')}\mathbf 1(R\subseteq R')\,q^{k-1-|R|}$. Writing $R_1=R\cap([n]\times\{1\})$, $R_2=R\cap([n]\times\{2\})$: $R\subseteq R'\in\mathcal R(C,C')$ forces $R\subseteq C(1)\cup C'(2)$ with $|R_1|,|R_2|\le(k-1)/2$ ($k$ odd) or $\le k/2$ ($k$ even), and the number of such $C(1)\cup C'(2)$ is at most $\deg_u(R_1)\deg_u(R_2)$.

<a id="pdf-9c5df3bb4a04-p042-b001"></a>
<!-- pdf-source: page=42; block=1; confidence=0.80 -->
**Proof (continued).** The number of $R'$ with $R\subseteq R'\subseteq C(1)\cup C'(2)$ is at most $|\mathcal R(C,C')|=w_k$, so
$$\nu_r\le w_k\,q^{k-1-r}\max_{\substack{R_1,R_2\subseteq[n],\ |R_1|+|R_2|=r\\ |R_1|,|R_2|\le(k-1)/2\ (k\text{ odd}),\ \le k/2\ (k\text{ even})}}\deg_u(R_1)\deg_u(R_2).$$
Fix maximizing $R_1,R_2$. By $(\varepsilon,\ell)$-regularity, $\deg_u(R_b)\le\tfrac{1}{\varepsilon^2}(n/\ell)^{k/2-1-|R_b|}$ if $|R_b|\le(k-2)/2$, and $\deg_u(R_b)\le\tfrac{1}{\varepsilon^2}$ at the maximal size ($(k-1)/2$ if $k$ odd, $k/2$ if $k$ even). Hence for $|R_b|\le(k-2)/2$,
$$\deg_u(R_b)\,q^{(k-1)/2-|R_b|}\le\tfrac{1}{\varepsilon^2}\Big(\tfrac{1+\beta}{2}\Big)^{(k-1)/2-|R_b|}\sqrt{\ell/n},$$
and if $|R_b|=(k-1)/2$ ($k$ odd) then $\deg_u(R_b)q^{(k-1)/2-|R_b|}=\deg_u(R_b)\le\tfrac{1}{\varepsilon^2}$, giving for $k$ odd $\nu_r\le w_k\tfrac{1}{\varepsilon^4}\eta^{k-1}$. For $k$ even: if $|R_1|,|R_2|\le(k-2)/2$ then $q^{k-1-r}\deg_u(R_1)\deg_u(R_2)\le\tfrac{1}{\varepsilon^4}\eta^{k-1}$ trivially; otherwise exactly one of $R_1,R_2$ has size $k/2$ (only one can, as $r\le k-1$), WLOG $|R_1|=k/2$ so $|R_2|=r-k/2\le(k-2)/2$, and
$$q^{k-1-r}\deg_u(R_1)\deg_u(R_2)\le\tfrac{1}{\varepsilon^4}\Big(\tfrac{1+\beta}{2}\Big)^{k-1-r}\le\tfrac{1}{\varepsilon^4}\eta^{k-1}.$$

<a id="pdf-9c5df3bb4a04-p042-b002"></a>
<!-- pdf-source: page=42; block=2; confidence=0.60 -->
**Proof (conclusion).** Taking $\lambda=w_k\tfrac{1}{\varepsilon^4}\eta^{k+1}c^{k+1}\ln^{k+1}\!\big(\tfrac{32pN}{\varepsilon^2 D}\big)$ for an absolute constant $c$ and applying Fact 3.2 gives
$$\Pr_{x\leftarrow\mathcal U'_\ell}\Big[P_u(x)\ge 2w_k\tfrac{1}{\varepsilon^4}\eta^{k+1}c^{k+1}\ln^{k+1}\tfrac{32pN}{\varepsilon^2 D}\Big]\le\tfrac{\varepsilon^2 D}{32pN}.$$
Lemma 6.9 follows by a union bound over the $p$ values of $u$ together with Lemma 6.20, and the observation that
$$2w_k\tfrac{1}{\varepsilon^4}\eta^{k+1}c^{k+1}\ln^{k+1}\tfrac{32pN}{\varepsilon^2 D}\le c'^{\,k+1}\tfrac{1}{\varepsilon^4}\ln^{2(k+1)}\tfrac{32pN}{\varepsilon^2 D}=\Delta,$$
where $c'$ is an absolute constant, since $\eta=4\ln\tfrac{32pN}{\varepsilon^2 D}$.

<a id="pdf-9c5df3bb4a04-p043-b001"></a>
<!-- pdf-source: page=43; block=1; confidence=0.90 -->
# 7. Strong CSP Refutation: Smoothed via Semirandom

Uses the tight refutation of semirandom sparse polynomials (Section 5) as a black box to obtain nearly optimal algorithms for strongly refuting smoothed Boolean CSPs, with semirandom CSPs as a special case.

<a id="pdf-9c5df3bb4a04-p043-b002"></a>
<!-- pdf-source: page=43; block=2; confidence=0.90 -->
**Definition 7.1 (Smoothed CSP Instances [Fei07]).** Fix $k\in\mathbb N$ and a CSP instance $\psi$ with predicate $P:\{\pm1\}^k\to\{0,1\}$, specified by a collection $\mathcal H$ of $k$-tuples and literal patterns $\xi$. Given smoothing parameters $\vec p=\{p_{C,i}\in[0,1]: C\in\mathcal H,\ i\in[k]\}$, a $\vec p$-smoothing of $\psi$ is obtained by:
1. For each $C\in\mathcal H$, form $S_C\subseteq[k]$ by adding each $i\in C$ to $S_C$ independently with probability $p_{C,i}$.
2. For each $i\in S_C$, reset $\xi(C,i)$ to a uniform independent random bit in $\pm1$.

<a id="pdf-9c5df3bb4a04-p043-b003"></a>
<!-- pdf-source: page=43; block=3; confidence=0.85 -->
**Remark 7.2.** (1) Smoothing allows a different rerandomization probability for each of the $mk$ literals in a $k$-CSP with $m$ constraints. (2) The two-step process is equivalent to flipping each literal's negation pattern $\xi(C,i)$ independently with probability $p_{C,i}/2$. (3) Taking $p_{C,i}=1$ for all $C,i$ makes the literal patterns uniformly random and independent in $\{\pm1\}$ — the semirandom CSP model.

<a id="pdf-9c5df3bb4a04-p043-b004"></a>
<!-- pdf-source: page=43; block=4; confidence=0.92 -->
**Definition 7.3 ($t$-wise uniform distribution).** A distribution $\mu$ on $\{\pm1\}^k$ is $t$-wise uniform if $\mathbb E_{x\sim\mu}\big[\prod_{i\in S}x_i\big]=0$ for every $S\subseteq[k]$ with $|S|\le t$.

<a id="pdf-9c5df3bb4a04-p043-b005"></a>
<!-- pdf-source: page=43; block=5; confidence=0.85 -->
**Theorem 7.4 (Smoothed Boolean CSP Refutation).** Let $P:\{\pm1\}^k\to\{0,1\}$ be a $k$-ary Boolean predicate with no $t$-wise uniform distribution supported on $P^{-1}(1)$. Let $\ell$ be an integer with $2(k-1)\le\ell\le n$. There is an $n^{O(\ell)}$-time algorithm that on input an instance $\Theta$ of CSP$(P)$ outputs $\mathrm{alg\text{-}val}(\Theta)\in[0,1]$ satisfying:

$(1)$ $\mathrm{val}(\Theta)\le\mathrm{alg\text{-}val}(\Theta)\le 1$.

$(2)$ If $\Theta$ is a smoothing $\psi_s$ of an arbitrary instance $\psi=(\mathcal H,\xi)$ with $n$ variables and $m$ constraints w.r.t. $\vec p=\{p_{C,i}\}\in[0,1]$, and $m\ge 2m_0/q(\vec p)$, where
$$m_0 = \frac{2^{O(k)}\,(\log_2 n)^{4t+1}}{\varepsilon^5}\cdot\ell\,(n/\ell)^{t/2},\qquad q(\vec p)=\tfrac1m\sum_{C\in\mathcal H}\prod_{i\in C}p_{C,i}.\quad(7.1)$$

<a id="pdf-9c5df3bb4a04-p044-b001"></a>
<!-- pdf-source: page=44; block=1; confidence=0.88 -->
**Theorem 7.4 (continued).** Then with probability $\ge 1-1/\mathrm{poly}(n)$ over the smoothing randomness,
$$\mathrm{alg\text{-}val}(\Theta)\le 1-\tfrac{q(\vec p)}{2}\,(\delta_t-\varepsilon)+2^{-n}.$$
In the semirandom case (all $p_{C,i}=1$), $\mathrm{alg\text{-}val}(\Theta)\le 1-\delta_t+\varepsilon+2^{-n}$ with probability $1-1/\mathrm{poly}(n)$. Here $\delta_t\ge 2^{-\tilde O(k^t)}$ depends only on $P$. The algorithm is captured by the canonical degree-$2\ell$ sum-of-squares relaxation of the CSP maximization problem over the hypercube.

<a id="pdf-9c5df3bb4a04-p044-b002"></a>
<!-- pdf-source: page=44; block=2; confidence=0.82 -->
**Fact 7.5 (Separating Polynomials [AOW15], Lemma 3.16 & Thm 4.10).** If $P:\{\pm1\}^k\to\{0,1\}$ has no $t$-wise uniform distribution supported on $P^{-1}(1)$, then there is $\delta_t\ge 2^{-\hat O(kt)}$ such that $\mathbb E_\zeta[P]\le 1-\delta_t$ for every $t$-wise uniform $\zeta$, and a degree-$t$ polynomial $Q:\{\pm1\}^k\to\mathbb R$, $Q(x)=\sum_{T\subseteq[k]}\hat Q(T)\,x^T$, such that:
1. $P(x)\le 1-\delta_t+Q(x)$ for every $x\in\{\pm1\}^k$;
2. $\hat Q(\emptyset)=0$ (no constant coefficient);
3. $\sum_{T\subseteq[k]}|\hat Q(T)|\le 2^{2k}$.

<a id="pdf-9c5df3bb4a04-p044-b003"></a>
<!-- pdf-source: page=44; block=3; confidence=0.85 -->
## 7.1 Proof of Theorem 7.4

**Proof.** By Fact 3.4, an $n^{O(\ell)}$-time algorithm outputs $\mathrm{alg\text{-}val}(\Theta)\in[0,1]$ with $\beta\le\mathrm{alg\text{-}val}(\Theta)\le\beta+2^{-n}$, where $\beta=\max_{\tilde{\mathbb E}}\tilde{\mathbb E}[\Theta]$ over degree-$2\ell$ pseudo-expectations on $\{\pm1\}^n$, and $\Theta(x):=\sum_{C\in\mathcal H}P(\xi(C,1)x_{C_1},\dots,\xi(C,k)x_{C_k})$ is a degree-$\le 2k$ polynomial (since $P$ is expressible as one). Completeness (Item 1) is trivial: take $\tilde{\mathbb E}=\mathbb E_\mu$ for $\mu$ supported on optimal solutions, giving $\mathrm{val}(\Theta)\le\beta\le\mathrm{alg\text{-}val}(\Theta)$. It remains to prove Item 2.

<a id="pdf-9c5df3bb4a04-p044-b004"></a>
<!-- pdf-source: page=44; block=4; confidence=0.85 -->
**Proof (cont.).** Analyze via the two smoothing steps. The event that step 1 rerandomizes all literals of clause $C\in\mathcal H$ has probability $\prod_{i=1}^k p_{C,i}$; let $\mathcal G$ be the set of such clauses. These 0-1 indicators are independent across clauses, and $\mathbb E|\mathcal G|=mq(\vec p)=\sum_{C\in\mathcal H}\prod_{i=1}^k p_{C,i}$. By Chernoff, $|\mathcal G|\ge 0.5\,mq(\vec p)$ with probability $\ge 1-e^{-mq(\vec p)/8}\ge 1-e^{-m_0/4}\ge 1-1/\mathrm{poly}(n)$ (using $mq(\vec p)\ge 2m_0$); assume this holds. For $C\in\mathcal G,\ i\in[k]$, the rerandomized $\xi(C,i)$ is uniform independent in $\pm1$; treat patterns for $C\notin\mathcal G$ as fixed and write $r_{C,i}:=\xi(C,i)$ for $C\in\mathcal G$.

<a id="pdf-9c5df3bb4a04-p045-b001"></a>
<!-- pdf-source: page=45; block=1; confidence=0.85 -->
**Proof (cont.).** Define
$$\psi_g=\tfrac1{|\mathcal G|}\sum_{C\in\mathcal G}P(r_{C_1}x_{C_1},\dots,r_{C_k}x_{C_k}),\quad \psi_b=\tfrac1{|\mathcal H|-|\mathcal G|}\sum_{C\notin\mathcal G}P(\xi(C,1)x_{C_1},\dots,\xi(C,k)x_{C_k}),$$
so $|\mathcal H|\psi_s=|\mathcal G|\psi_g+(|\mathcal H|-|\mathcal G|)\psi_b$. By linearity of pseudo-expectations, for any $\tilde{\mathbb E}$:
$$\tilde{\mathbb E}[\psi_s]\le\tfrac{|\mathcal G|}{|\mathcal H|}\,|\tilde{\mathbb E}[\psi_g]|+\big(1-\tfrac{|\mathcal G|}{|\mathcal H|}\big)\,|\tilde{\mathbb E}[\psi_b]|.\quad(7.2)$$
Since $P(\cdots)\le1$ and $P$ is a degree-$k$ polynomial on $k$ variables, Fact 3.8 gives $\tilde{\mathbb E}[P(\cdots)]\le1$ for degree-$2\ell\ge2k$ pseudo-expectations; summing over $C\notin\mathcal G$ yields $\tilde{\mathbb E}[\psi_b]\le1$ (7.3). ($\psi_g,\psi_b$ appear only in the analysis, not in the algorithm.)

<a id="pdf-9c5df3bb4a04-p045-b002"></a>
<!-- pdf-source: page=45; block=2; confidence=0.82 -->
**Proof (cont.).** By Fact 7.5, for every $x$, $P(r_{C,1}x_{C_1},\dots,r_{C,k}x_{C_k})\le 1-\delta_t+Q(r_{C,1}x_{C_1},\dots,r_{C,k}x_{C_k})$. Since $\deg(Q)=t\le k$, Fact 3.8 and summing over $C\in\mathcal G$ give, for degree-$2\ell\ge2k$ pseudo-expectations,
$$\tilde{\mathbb E}[\psi_g]\le 1-\delta_t+\tfrac1{|\mathcal G|}\sum_{C\in\mathcal G}\tilde{\mathbb E}\big[Q(r_{C,1}x_{C_1},\dots,r_{C,k}x_{C_k})\big].$$
For $T\subseteq[k]$ with $|T|\le t$, set $x_{C|T}=\prod_{i\in T}x_{C_i}$ and $b_{C|T}=\prod_{i\in T}r_{C,i}$; using $Q(x)=\sum_{0<|T|\le t}\hat Q(T)x^T$ and $\sum_{0<|T|\le t}|\hat Q(T)|\le 2^{2k}$, and defining the homogeneous degree-$|T|$ polynomial $\phi_T(x)=\tfrac1{|\mathcal G|}\sum_{C\in\mathcal G}b_{C|T}x_{C|T}$:
$$\tilde{\mathbb E}[\psi_g]\le 1-\delta_t+\sum_{0<|T|\le t}|\hat Q(T)|\,\tilde{\mathbb E}[\phi_T].\quad(7.4)$$
Each $\phi_T$ has independent random coefficients in $\{-1,1\}$. Since $|\mathcal G|\ge 0.5\,q(\vec p)m\ge m_0$, Theorem 5.1 applies with probability $\ge 1-1/\mathrm{poly}(n)$ [text cut off].

<a id="pdf-9c5df3bb4a04-p046-b001"></a>
<!-- pdf-source: page=46; block=1; confidence=0.80 -->
**Proof (continued, smoothed case).** For every pseudo-expectation $\tilde{\mathbb{E}}$ of degree at least $2\ell$, $\tilde{\mathbb{E}}[\phi_T] \le \varepsilon/2^{2k}$. A union bound over the $\le 2^k$ possible $T$ makes this hold for all $T$ with probability $\ge 1 - 1/\mathrm{poly}(n)$. Conditioning on this event, combining with (7.4), and using $\sum_T |\hat{Q}(T)| \le 2^{2k}$ gives $\tilde{\mathbb{E}}[\psi_g] \le 1 - \delta_t + \varepsilon$ (7.5). Substituting into (7.2) and using (7.3) yields $\tilde{\mathbb{E}}[\psi_s] \le \big(1 - \tfrac{|\mathcal G|}{|\mathcal H|}\big)\cdot 1 + \tfrac{|\mathcal G|}{|\mathcal H|}(1-\delta_t+\varepsilon) \le 1 - \tfrac{|\mathcal G|}{|\mathcal H|}(\delta_t-\varepsilon) \le 1 - (\delta_t-\varepsilon)\cdot\tfrac{q(\vec p)}{2}$ (7.6), using $|\mathcal{G}|/|\mathcal{H}| \ge q(\vec p)/2$. This requires $\delta_t \ge \varepsilon$ (the conclusion is trivial otherwise). Since $\mathrm{alg\text{-}val}(\psi_s) \le \beta + 2^{-n} \le 1 - (\delta_t-\varepsilon)\cdot\tfrac{q(\vec p)}{2} + 2^{-n}$, the smoothed case is complete.

<a id="pdf-9c5df3bb4a04-p046-b002"></a>
<!-- pdf-source: page=46; block=2; confidence=0.50 -->
**Proof (semirandom case).** The semirandom model is the special case of the smoothed model where $p_{C,i} = 1$ for every $i$; the argument directly gives $\tilde{\mathbb{E}}[\psi] \le \tfrac{1}{0.5\,\delta t\,\varepsilon}\cdot 2\sqrt{n}$. The $0.5$ factor arose only from the probabilistic bound on $|\mathcal{G}|$; in the semirandom setting $|\mathcal{G}| = |\mathcal{H}|$ with probability $1$, so this extra factor is not lost for semirandom refutation.

<a id="pdf-9c5df3bb4a04-p046-b003"></a>
<!-- pdf-source: page=46; block=3; confidence=0.95 -->
**Section 8. Proof of Feige's Conjecture: Even Covers in Hypergraphs.**

<a id="pdf-9c5df3bb4a04-p046-b004"></a>
<!-- pdf-source: page=46; block=4; confidence=0.50 -->
This section proves Feige's conjecture: every $k$-uniform hypergraph with sufficiently many hyperedges has a short even cover. It is later used (via Feige–Kim–Ofek ideas) to obtain polynomial-size refutations for semirandom 3-SAT at density $m > \tilde{\Omega}(n^{1/4})$, a $\tilde{O}(n^{0.1})$ factor below the spectral threshold $n^{1/2}$ for random instances. The result generalizes to $k$-SAT and arbitrary CSPs.

<a id="pdf-9c5df3bb4a04-p046-b005"></a>
<!-- pdf-source: page=46; block=5; confidence=0.85 -->
**Definition 8.1 (Even (multi)covers).** Let $\mathcal{H}$ be a $k$-uniform hypergraph on $[n]$. Distinct hyperedges $C_1,\dots,C_r \in \mathcal{H}$ form an **even cover of length $r$** if every element $j\in[n]$ lies in an even number of the $C_i$; equivalently $\bigoplus_{i=1}^r C_i = \emptyset$. An **even multicover** is the same but the $C_i$ need not be distinct. Even (multi)covers are defined analogously for bipartite hypergraphs using hyperedges $(u,C)$.

<a id="pdf-9c5df3bb4a04-p046-b006"></a>
<!-- pdf-source: page=46; block=6; confidence=0.85 -->
If $\mathcal{H}$ is not simple (a multiset), it trivially has an even cover of length $2$: it contains distinct $C_1, C_2$ equal as sets, so $C_1 \oplus C_2 = \emptyset$.

<a id="pdf-9c5df3bb4a04-p046-b007"></a>
<!-- pdf-source: page=46; block=7; confidence=0.80 -->
The main result proves Feige's conjecture (Conjecture 1.7) up to a $\mathrm{poly}\log n$ factor loss in the number of hyperedges $m$.

<a id="pdf-9c5df3bb4a04-p047-b001"></a>
<!-- pdf-source: page=47; block=1; confidence=0.90 -->
**Theorem 8.2 (Resolution of Feige's Conjecture).** Let $k\in\mathbb{N}$ and $\ell = \ell(n)$ with $2(k-1) \le \ell \le n$. Let $\mathcal{H}$ be a $k$-uniform hypergraph on $[n]$ with $m \ge \Gamma^k \cdot n\,(n/\ell)^{k/2 - 1}\log^{4k+1} n$ hyperedges, where $\Gamma$ is an absolute constant. Then $\mathcal{H}$ contains an even cover of size $O(\ell \log n)$.

<a id="pdf-9c5df3bb4a04-p047-b002"></a>
<!-- pdf-source: page=47; block=2; confidence=0.70 -->
The proof mimics Sections 4–6 (efficient refutation of semirandom sparse multilinear polynomials). First step: WLOG assume $\mathcal{H}$ is a simple, $p$-bipartite, $(\varepsilon,\ell)$-regular hypergraph with $\varepsilon = 10^{-4}$.

<a id="pdf-9c5df3bb4a04-p047-b003"></a>
<!-- pdf-source: page=47; block=3; confidence=0.85 -->
**Lemma 8.3 (Reduction to simple, $p$-bipartite, $(1/4,\ell)$-regular hypergraphs).** Fix $k$ and $\ell=\ell(n)\in\mathbb{N}$ with $2(k-1)\le\ell\le n$. Suppose that for every $p$-bipartite, $(1/4,\ell)$-regular, simple $k$-uniform hypergraph $\mathcal{H} = \{\mathcal{H}_u\}_{u\in[p]}$ with $m \ge \max\!\big(c^k\,(n/\ell)^{(k-1)/2}\sqrt{p\ell}\,\log^{2k+0.5} n,\; 16p\big)$ hyperedges (for an absolute constant $c$) and $|\mathcal{H}_u| = m/p$ for all $u$, there exists an even cover in $\mathcal{H}$ of length at most $r$. Then every $k$-uniform hypergraph $\mathcal{H}$ with $m \ge \Gamma^k\, n\,(n/\ell)^{k/2-1}\log^{4k+1} n$ hyperedges has an even cover of length at most $r$.

<a id="pdf-9c5df3bb4a04-p047-b004"></a>
<!-- pdf-source: page=47; block=4; confidence=0.55 -->
**Proof.** Let $\mathcal{H}$ be arbitrary $k$-uniform. If not simple, parallel hyperedges give an even cover of size $2$; so assume $\mathcal{H}$ simple. Apply the decomposition algorithm of Lemma 4.7 to get bipartite hypergraphs $\mathcal{H}^{(1)},\dots,\mathcal{H}^{(k)}$, all simple. Since $\sum_{t=1}^k m^{(t)} = m$, some $t$ ($1\le t\le k$) has $m^{(t)} \ge m/k$. As $m^{(1)} \le \varepsilon m/k$ always, $t \neq 1$. The Lemma 4.7 bound on $m^{(t)}/p^{(t)}$ gives $m^{(t)} \ge m/k \ge \max\!\big(c\,k\,\tfrac{n(n/\ell)^{(k-1)/2}}{p^{(t)}\ell}\log^{2k+0.5}n,\, 16p^{(t)}\big)$. Hence the $p^{(t)}$-bipartite $(10^{-4},\ell)$-regular $\mathcal{H}^{(t)}$ contains an even cover $(u_1,C_1),\dots,(u_{r'},C_{r'})$ with $r' \le r$. By Lemma 4.7, for each $u_i$ there is $Q_i$ so that hyperedge $(u_i,C_i)$ is a bipartite contraction of the unique $(Q_i \cup C_i) \in \mathcal{H}$. Then $(Q_1\cup C_1),\dots,(Q_{r'}\cup C_{r'})$ is an even cover of length $r' \le r$ in $\mathcal{H}$. $\square$

<a id="pdf-9c5df3bb4a04-p047-b005"></a>
<!-- pdf-source: page=47; block=5; confidence=0.85 -->
**Lemma 8.4 (No even covers implies refutation for semirandom polynomials on regular bipartite hypergraphs).** Fix odd $k\in\mathbb{N}$ and $\ell=\ell(n)$ with $2(k-1)\le\ell\le n$. Let $\mathcal{H} = \{\mathcal{H}_u\}_{u\in[p]}$ be a $p$-bipartite $(1/4,\ell)$-regular simple $k$-uniform hypergraph with $m \ge m_0 = \max\!\big(c^k\,(n/\ell)^{(k-1)/2}\sqrt{p\ell}\,\log^{2k+0.5}n,\,16p\big)$ hyperedges ($c$ an absolute constant) and $|\mathcal{H}_u| = m/p$ for all $u$. Let $\psi = \tfrac{1}{m}\sum_{u\in[p]}\sum_{C\in\mathcal{H}_u} b_{u,C}\, y_u x_C$ for arbitrary $b_{u,C}\in\{-1,1\}$. Suppose $\mathcal{H}$ has no even covers of length $\le O(\ell\log n)$. Then $\mathrm{val}(\psi) \le 0.5$.

<a id="pdf-9c5df3bb4a04-p047-b006"></a>
<!-- pdf-source: page=47; block=6; confidence=0.70 -->
The conclusion is deliberately absurd: setting $b_{u,C}=1$ for all $u,C$ gives $\mathrm{val}(\psi)=1$ (via $x=\mathbf{1}_n$, $y=\mathbf{1}_p$), so the lemma forces a contradiction — hence $\mathcal{H}$ must admit an even cover of length $O(\ell\log n)$. It is stated this way because the proof mimics the Section 6 refutation argument, carrying out all steps for arbitrary $b_{u,C}$ under the no-short-even-cover assumption. Theorem 8.2 follows easily from Lemma 8.4.

<a id="pdf-9c5df3bb4a04-p048-b001"></a>
<!-- pdf-source: page=48; block=1; confidence=0.70 -->
**Proof of Theorem 8.2.** By Lemma 8.3, assume $\mathcal{H} := \bigcup_{u\in[p]}\mathcal{H}_u$ is a $(10^{-4},\ell)$-regular, simple, $k$-uniform bipartite hypergraph with $p \le n^k$ partitions and $m \ge m_0$. Suppose for contradiction $\mathcal{H}$ has no even cover of length $O(\ell\log n)$. Set $b_{u,C}=1$ for all $u,C$ and take $\psi = \tfrac{1}{|\mathcal{H}'|}\sum_{u\in[p]}\sum_{C\in\mathcal{H}_u} b_{u,C}\,y_u x_C$. Setting $x=\mathbf{1}_n$, $y=\mathbf{1}_p$ gives $\mathrm{val}(\psi)=1$, while Lemma 8.4 gives $\mathrm{val}(\psi)\le 0.5$ — a contradiction. Hence $\mathcal{H}$ has an even cover of length $\le O(\ell\log n)$. $\square$

<a id="pdf-9c5df3bb4a04-p048-b002"></a>
<!-- pdf-source: page=48; block=2; confidence=0.90 -->
**Section 8.1. Proof of Lemma 8.4.**

<a id="pdf-9c5df3bb4a04-p048-b003"></a>
<!-- pdf-source: page=48; block=3; confidence=0.80 -->
**Proof of Lemma 8.4.** The proof follows the Section 6 outline for refuting $\psi$, but here bounds $\mathrm{val}(\psi)$ (no efficient certificate needed). Key point: only one Section 6 step uses randomness of the $b_{u,C}$, namely Lemma 6.15; the innovation is an analog of Lemma 6.15 valid for arbitrary $b_{u,C}$ whenever $\mathcal{H}$ has no $O(\ell\log n)$-length even cover. Since $\mathcal{H}$ satisfies the assumptions of Theorem 5.4, it suffices to re-establish the spectral-norm bounds of Lemma 6.15. Using Section 6 notation: let $f$ be the polynomial from Lemma 6.1 applied to $\psi$, and $A$ the Kikuchi matrix (Definition 6.2) for $f$. Lemma 6.3 gives $\mathrm{val}(\psi)^2 \le \tfrac{1}{12}+\mathrm{val}(f) \le \tfrac{1}{12}+\tfrac{p}{m^2 D}\,\|A\|_{\infty\to 1}$, using $12p \le m$. Here $D := \binom{k-1}{(k-1)/2}^2\binom{2n-2(k-1)}{\ell-(k-1)}$ for $k$ odd, and $2\binom{k-1}{k/2}\binom{k-1}{(k-2)/2}\binom{2n-2(k-1)}{\ell-(k-1)}$ for $k$ even. Let $\mathcal{B}$ be the bad rows of $A$; by Lemma 6.9, for $\Delta = c'^{\,k-1}\,\tfrac{1}{\varepsilon^4}\ln^{2(k-1)}\!\big(\tfrac{32pN}{\varepsilon^2 D}\big)$ (absolute constant $c'$, $\varepsilon=1/4$), one has $|\mathcal{B}|/N \le \varepsilon^2 D/(16N)$. Let $G$ be $A$ with rows/columns in $\mathcal{B}$ zeroed out (as in Lemma 6.11, Section 6.4). Let $\mathcal{F}_0\cup\mathcal{F}_1\cup\dots\cup\mathcal{F}_t$, $t\le 2\log_2 m$, partition the non-bad rows, and $G^{(i,j)}$ (Definition 6.13) zero out rows/columns outside $\mathcal{F}_i,\mathcal{F}_j$ from $G$; define $G^{(i,j)}_u$ analogously from $G_u$. Following Section 6.4, it remains only to establish the conclusion of Lemma 6.15 for arbitrary $b_{u,C}$ under the no-small-even-cover assumption, stated as the following lemma. (Footnote: the only other deviation from Section 6 is that $12p \le m$ replaces $16p \le m$ since $4p$ edges were removed; this is unimportant.)

<a id="pdf-9c5df3bb4a04-p049-b001"></a>
<!-- pdf-source: page=49; block=1; confidence=0.82 -->
**Lemma 8.5 (Spectral norm of $G^{(i,j)}$ when $\mathcal{H}$ has no small even cover).** Suppose the $(1/4,\ell)$-regular $p$-bipartite simple $k$-uniform hypergraph $\mathcal{H}$ associated to the polynomial $\psi$ has no even cover of length $\le c_0\ell\log_2 n$ for a large enough constant $c_0$. Then for each $i,j\in\{0,\dots,t\}$,
$$\|G^{(i,j)}\|_2 \le O(1)\cdot 2^{0.5\max(i,j)}\sqrt{d\log N}\;+\;O(1)\,\Delta\log N.$$

<a id="pdf-9c5df3bb4a04-p049-b002"></a>
<!-- pdf-source: page=49; block=2; confidence=0.85 -->
Lemma 8.5 completes the proof of Lemma 8.4: via the same calculation as in Section 6 it gives $\tfrac{p}{m^2 D}\|A\|_{\infty\to 1}\le \varepsilon^2 = \tfrac{1}{16}$, hence $\mathrm{val}(\phi)\le \tfrac{1}{12}+\tfrac{1}{16}\le \tfrac13$. It remains to prove Lemma 8.5.

<a id="pdf-9c5df3bb4a04-p049-b003"></a>
<!-- pdf-source: page=49; block=3; confidence=0.72 -->
**Proof of Lemma 8.5.** Following the trace-method proof of Lemma 6.15 (Section 6.4.2). Fix a pair $(i,j)$ and write $Z:=G^{(i,j)}$, $Z_u:=G^{(i,j)}_u$. Since $\|Z\|_2\le \operatorname{tr}((ZZ^\top)^r)^{1/(2r)}$ for every $r\in\mathbb{N}$, the lemma is proved by upper bounding $\operatorname{tr}((ZZ^\top)^r)$ for $r=O(\ell\log^2 n)$. Unlike the classical random-matrix use of the trace moment method, here $Z$ has no randomness, so instead of bounding an expectation the contributing walk terms are controlled using the combinatorial structure of the support of the Kikuchi matrix $A$ (an approach that cannot work for arbitrary matrices).

<a id="pdf-9c5df3bb4a04-p049-b004"></a>
<!-- pdf-source: page=49; block=4; confidence=0.75 -->
**Proposition 8.6.** Suppose the $((1/4),\ell)$-regular $p$-bipartite simple $k$-uniform hypergraph $\mathcal{H}$ associated to $\psi$ has no even cover of length $\le 4c_0\ell\log^2 n$ for a large enough constant $c_0$. Then for $r\le c_0\ell\log^2 n$,
$$\operatorname{tr}((ZZ^\top)^r)\le \sum_{S\in\mathcal{F}_i} \#\{\text{even walk sequences }(u_1,C_1,C_1'),\dots,(u_{2r},C_{2r},C_{2r}')\text{ for }S\}.$$
The bound holds regardless of the values $b_{u,C}$, being a consequence of the support structure of Kikuchi matrices.

<a id="pdf-9c5df3bb4a04-p049-b005"></a>
<!-- pdf-source: page=49; block=5; confidence=0.70 -->
**Proof (conclusion of Lemma 8.5 from Proposition 8.6).** By Lemma 6.18, for each $S\in\mathcal{F}_i$ the number of such sequences is at most $(4r)^r\,(2\max(i,j)\,d + r\Delta^2)^r$. Hence
$$\|Z\|_2^{2r}\le \operatorname{tr}((ZZ^\top)^r)\le N\,(4r)^r\,(2\max(i,j)\,d + r\Delta^2)^r.$$
Setting $r=c_0\ell\log^2 n$ gives $\|Z\|_2\le O(1)\,2^{0.5\max(i,j)}\sqrt{d\log^2 N}+O(1)\,\Delta\log^2 N$, assuming $\mathcal{H}$ has no even cover of length $\le 4r=4c_0\ell\log^2 n$. This proves Lemma 8.5 modulo Proposition 8.6.

<a id="pdf-9c5df3bb4a04-p050-b001"></a>
<!-- pdf-source: page=50; block=1; confidence=0.78 -->
**Proof of Proposition 8.6.** Expand
$$\operatorname{tr}((ZZ^\top)^r)=\sum_{u_1,S_1,u_2,S_2,\dots,u_{2r},S_{2r}}\;\prod_{h=1}^{r} Z_{u_{2h-1}}(S_{2h-1},S_{2h})\,Z_{u_{2h}}(S_{2h+1},S_{2h}),\tag{8.1}$$
with $u_{2r+1}:=u_1$ and $S_{2r+1}:=S_1$. Each term of (8.1) contributes at most $1$ (all $b_{u,C}\in\{\pm1\}$ and $\mathcal{H}$ is simple), so the RHS is bounded by the number of non-zero walk terms.

<a id="pdf-9c5df3bb4a04-p050-b002"></a>
<!-- pdf-source: page=50; block=2; confidence=0.75 -->
**Claim 8.7 (Non-zero terms are even multicovers).** If the walk term for $(u_1,S_1,u_2,S_2,\dots,u_{2r},S_{2r})$ is non-zero, then for every $h\in[2r]$ there exist $C_h\neq C_h'\in\mathcal{H}_{u_h}$ with $S_{h+1}=S_h\triangle C_h^{(1)}\triangle C_h'^{(2)}$. Moreover $\sum_{h\le 2r}(u_h,C_h)\triangle(u_h,C_h')=\emptyset$, i.e. $\{(u_h,C_h),(u_h,C_h')\}_{h\le 2r}$ is an even multicover in $\mathcal{H}$.

<a id="pdf-9c5df3bb4a04-p050-b003"></a>
<!-- pdf-source: page=50; block=3; confidence=0.72 -->
**Proof.** By definition of the Kikuchi matrix, the walk term equals
$$\prod_{h\le r} b_{u_{2h-1},C_{2h-1}}b_{u_{2h-1},C_{2h-1}'}b_{u_{2h},C_{2h}}b_{u_{2h},C_{2h}'}\,\mathbf{1}\big[S_{2h-1}\xrightarrow{C_{2h-1}^{(1)},C_{2h-1}'^{(2)}}S_{2h}\big]\mathbf{1}\big[S_{2h}\xrightarrow{C_{2h}^{(1)},C_{2h}'^{(2)}}S_{2h+1}\big],\tag{8.2}$$
with $C_{2h-1},C_{2h-1}'\in\mathcal{H}_{u_{2h-1}}$ and $C_{2h},C_{2h}'\in\mathcal{H}_{u_{2h}}$. Non-zero forces every indicator to equal $1$, giving $S_{2h}=S_{2h-1}\triangle C_{2h-1}^{(1)}\triangle C_{2h-1}'^{(2)}$ and $S_{2h+1}=S_{2h}\triangle C_{2h}^{(1)}\triangle C_{2h}'^{(2)}$. Summing all these equations, $\sum_{h=2}^{2r+1}S_h=\sum_{h=1}^{2r}S_h\triangle\sum_{h=1}^{2r}(C_h^{(1)}\triangle C_h'^{(2)})$; since $S_{2r+1}:=S_1$ the $S_h$ cancel, yielding $\sum_{h\le 2r}C_h^{(1)}\triangle C_h'^{(2)}=\emptyset$. This gives $\sum_{h\le 2r}C_h=\sum_{h\le 2r}C_h'=\emptyset$, hence $\sum_{h\le 2r}(u_h,C_h)\triangle(u_h,C_h')=\emptyset$. $\square$

<a id="pdf-9c5df3bb4a04-p050-b004"></a>
<!-- pdf-source: page=50; block=4; confidence=0.80 -->
The even multicover $\{(u_h,C_h),(u_h,C_h')\}_{h\le 2r}$ need not be an even *cover* since the $(u_h,C_h)$ need not be distinct. The key point ahead: with no small even covers in $\mathcal{H}$, the $(u_h,C_h)$ must occur in pairs (each appears an even number of times).

<a id="pdf-9c5df3bb4a04-p050-b005"></a>
<!-- pdf-source: page=50; block=5; confidence=0.75 -->
**Claim 8.8 (No short even cover $\Rightarrow$ short multicovers are unions of pairs).** Suppose $\mathcal{H}=\{\mathcal{H}_u\}_{u\in[p]}$ has no even cover of length $\le 4r$. Then if the walk term in (8.1) for $\{u_h,S_h,C_h,C_h'\}_{h\le 2r}$ is non-zero, each $(u,C)\in\bigcup_{u\in[p]}\mathcal{H}_u$ occurs an even number of times in the multiset $\{(u_h,C_h),(u_h,C_h')\}_{h\le 2r}$.

<a id="pdf-9c5df3bb4a04-p051-b001"></a>
<!-- pdf-source: page=51; block=1; confidence=0.75 -->
**Claim 8.8 (cont.).** In particular $\{(u_h,C_h,C_h')\}_{h\le 2r}$ is an even walk sequence for $S_1$ (Definition 6.16).

**Proof.** From Claim 8.7, $\sum_{h=1}^{2r}(u_h,C_h)\triangle(u_h,C_h')=\emptyset$. Starting from the multiset $\{(u_h,C_h),(u_h,C_h')\}_{h\le 2r}$, greedily remove equal pairs until impossible; the symmetric difference of the remainder stays empty. If a non-zero number of hyperedges remains (i.e. the conclusion fails), then $\le 4r$ distinct hyperedges have empty symmetric difference, forming an even cover of length $\le 4r$ in $\mathcal{H}$ — a contradiction. $\square$

<a id="pdf-9c5df3bb4a04-p051-b002"></a>
<!-- pdf-source: page=51; block=2; confidence=0.80 -->
Combining Claims 8.7 and 8.8, the RHS of (8.1) is upper bounded by $\sum_{S\in\mathcal{F}_i}\#\{\text{even walk sequences }(u_1,C_1,C_1'),\dots,(u_{2r},C_{2r},C_{2r}')\text{ for }S\}$, finishing the proof of Proposition 8.6.

<a id="pdf-9c5df3bb4a04-p051-b003"></a>
<!-- pdf-source: page=51; block=3; confidence=0.72 -->
**9. Polynomial Size Refutation Witnesses Below the Spectral Threshold.** Using the smoothed refutation algorithm and the proof of Feige's conjecture to show polynomial-size refutation witnesses exist below the spectral threshold for smoothed Boolean CSPs. Building on Theorems 5.1 and 8.2, the plan follows Feige–Kim–Ofek [FKO06] (fully random 3-SAT with $\ge \tilde O(n^{1/4})$ constraints), extending it to semirandom/smoothed instances and giving a simpler witness even for fully random 3-SAT.

<a id="pdf-9c5df3bb4a04-p051-b004"></a>
<!-- pdf-source: page=51; block=4; confidence=0.85 -->
**Definition 9.1 (Nondeterministic refutation).** Fix $k\in\mathbb{N}$ and a predicate $P:\{\pm1\}^k\to\{0,1\}$. A nondeterministic algorithm $V$ is a *nondeterministic efficient weak refutation algorithm* if, on a CSP instance $\psi$ with predicate $P$ in $n$ variables and $m$ clauses, it runs in $\mathrm{poly}(n,m)$ nondeterministic time and outputs "unsatisfiable" or "don't know", such that for every $\psi$, if $V(\psi)$ outputs "unsatisfiable" then $\psi$ is unsatisfiable (then $V$ *weakly refutes* $\psi$). The string $\pi\in\{0,1\}^{\mathrm{poly}(n,m)}$ of nondeterministic guesses is the *weak refutation witness*.

<a id="pdf-9c5df3bb4a04-p051-b005"></a>
<!-- pdf-source: page=51; block=5; confidence=0.85 -->
**Theorem 9.2.** Let $k\ge 3$ and $P:\{\pm1\}^k\to\{0,1\}$ be a non-trivial predicate. Then there is a nondeterministic efficient weak refutation algorithm $V$ with the following properties. Let $\psi$ be a CSP instance with predicate $P$, $n$ variables and $m$ clauses, specified by a collection of $m$ $k$-tuples $\mathcal{H}$ and literal patterns $\xi$. Then:
(1) If $\psi$ is a uniformly random instance with $m\ge \tilde O(1)\cdot n^{\,k/2 - (k-2)/(2(k+2))}$ clauses, then $V$ weakly refutes $\psi$ with probability at least $1-1/\mathrm{poly}(n)$.

<a id="pdf-9c5df3bb4a04-p052-b001"></a>
<!-- pdf-source: page=52; block=1; confidence=0.85 -->
**Theorem 9.2 (items 2–3, continued).** (2) If $\psi$ is a semirandom instance with $m \geq \tilde{O}(1)\cdot n^{\,k/2 - (k-2)/(2(k+8))}$ clauses, then $V$ weakly refutes $\psi$ with probability at least $1 - 1/\mathrm{poly}(n)$. (3) If $\psi$ is a smoothed instance obtained using smoothing parameters $\vec p = \{p_{C,i}\}_{C\in\mathcal{H}, i\in[k]}$ with $m \geq \tilde{O}(1)\cdot n^{\,k/2 - (k-2)/(2(k+8))}/q(\vec p)$ clauses, where $q(\vec p) := \tfrac{1}{m}\sum_{C\in\mathcal{H}}\prod_{i\in C} p_{C,i}$, then $V$ weakly refutes $\psi$ with probability at least $1 - 1/\mathrm{poly}(n)$. Finally, if $k = 3$, the threshold on $m$ for the semirandom/smoothed case can be improved to $\tilde{O}(n^{1.4})$ and $\tilde{O}(n^{1.4})/q(\vec p)$ respectively, matching the random case.

<a id="pdf-9c5df3bb4a04-p052-b002"></a>
<!-- pdf-source: page=52; block=2; confidence=0.90 -->
Work first focuses on $k$-XOR; as in Section 7, refuting arbitrary predicates $P$ reduces to refuting XOR. Following [FKO06], "ideal FKO witnesses" enable non-trivial weak refutation of $k$-XOR when the $b_C$ are chosen uniformly and independently at random; informally they are a disjoint collection of even covers in $\mathcal{H}$.

<a id="pdf-9c5df3bb4a04-p052-b003"></a>
<!-- pdf-source: page=52; block=3; confidence=0.94 -->
**Definition 9.3 (Ideal FKO witnesses).** Let $\mathcal{H}$ be a $k$-uniform hypergraph on $[n]$. A collection of even covers $E_1, E_2, \dots, E_r \subseteq \mathcal{H}$ is an *ideal FKO witness of length $h$* if $E_i \cap E_j = \emptyset$ for every $i\neq j$ and $|E_i| \leq h$ for every $i$, where $|E_i|$ denotes the length of the even cover $E_i$. Its size is $s = \sum_{i=1}^{r} |E_i| \leq hr$.

<a id="pdf-9c5df3bb4a04-p052-b004"></a>
<!-- pdf-source: page=52; block=4; confidence=0.92 -->
**Lemma 9.4.** Let $\psi = (\mathcal{H}, b)$ be an instance of $k$-XOR on $n$ variables, and let $E_1, \dots, E_r \subseteq \mathcal{H}$ be an ideal FKO witness in $\mathcal{H}$. Suppose each $b_C$ is a uniformly random independent bit in $\pm 1$. Then with probability at least $1 - \exp(-\Omega(r))$ over the draw of $b = \{b_C\}_{C\in\mathcal{H}}$, $\mathrm{val}(\psi) \leq 1 - \tfrac{r}{3m}$.

<a id="pdf-9c5df3bb4a04-p052-b005"></a>
<!-- pdf-source: page=52; block=5; confidence=0.92 -->
**Proof.** For each $i$ set $Z_i = \prod_{C\in E_i} b_C$; the $Z_1, \dots, Z_r$ are independent, each uniform on $\{\pm 1\}$. By a Chernoff bound, with probability $\geq 1 - \exp(-\Omega(r))$ at least $r/3$ of the $E_i$ satisfy $Z_i = -1$. If some $x\in\{\pm1\}^n$ satisfies all constraints of $\psi$ for the $k$-tuples $C\in E_i$, then $\prod_{C\in E_i} b_C = \prod_{C\in E_i}\prod_{j\leq k} x_{C_j}$; since $E_i$ is an even cover every variable appears an even number of times, so the RHS $=1$, contradicting $Z_i = -1$. Hence every $x$ violates at least one constraint in each such $E_i$; as the $E_i$ are disjoint, every $x$ violates at least $r/3$ constraints, giving the bound on $\mathrm{val}(\psi)$.

<a id="pdf-9c5df3bb4a04-p052-b006"></a>
<!-- pdf-source: page=52; block=6; confidence=0.90 -->
The key question is whether ideal FKO witnesses exist in the $k$-uniform hypergraph of the $k$-XOR instance. [FKO06] study finding such witnesses in random sufficiently dense hypergraphs; they expect existence but note that proving it appears hard. (Footnote 8: Gaussian elimination decides unsatisfiability of a $k$-XOR instance in polynomial time — a trivial weak refutation.)

<a id="pdf-9c5df3bb4a04-p053-b001"></a>
<!-- pdf-source: page=53; block=1; confidence=0.90 -->
[FKO06] instead prove existence of "almost disjoint" even covers (rather than perfectly disjoint) via a second moment method argument. Here, ideal FKO witnesses are shown to exist not only in random dense hypergraphs but in arbitrary hypergraphs of the same density, following almost immediately from Theorem 8.2.

<a id="pdf-9c5df3bb4a04-p053-b002"></a>
<!-- pdf-source: page=53; block=2; confidence=0.88 -->
**Lemma 9.5.** Fix $k\in\mathbb{N}$ and $\ell = \ell(n)$. Let $\mathcal{H}$ be any $k$-uniform hypergraph with $m \geq 2m_0$ hyperedges, where $m_0 = \Gamma^k\cdot n\,(n/\ell)^{k/2 - 1}\log^{4k+1} n$ is the threshold appearing in Theorem 8.2. Then $\mathcal{H}$ contains a collection of $m_0/h(n)$ hyperedge-disjoint even covers, each of length at most $h(n) = O(\ell \log n)$.

<a id="pdf-9c5df3bb4a04-p053-b003"></a>
<!-- pdf-source: page=53; block=3; confidence=0.85 -->
**Proof.** With $m_0$ the constraint count of Theorem 8.2, choose $m \geq 2m_0$. Theorem 8.2 gives an even cover $E_1$ with $|E_1| \leq h(n) = O(\ell\log n)$. Set $\mathcal{H}_0 = \mathcal{H}$ and repeat for $i = 1, 2, \dots, r$: apply Theorem 8.2 to $\mathcal{H}_i := \mathcal{H}_{i-1} \setminus E_i$ to obtain $E_{i+1} \subseteq \mathcal{H}_i$ of size $\leq h(n)$. The hypotheses of Theorem 8.2 hold as long as $|\mathcal{H}_i| \geq m - h(n)\,r \geq m/2$, i.e. $r \leq 0.5\, m_0/h(n)$. The $E_1, \dots, E_r$ are pairwise disjoint by construction.

<a id="pdf-9c5df3bb4a04-p053-b004"></a>
<!-- pdf-source: page=53; block=4; confidence=0.88 -->
Combined with semirandom refutation algorithms, ideal FKO witnesses yield weak refutation witnesses for all $k$-CSPs at densities polynomially below $n^{k/2}$. A key FKO insight is using this non-trivial weak refutation to establish poly-size weak-refutation witnesses for random 3-SAT with $m = \tilde{\Omega}(n^{1/4})$ constraints — a regime where known spectral algorithms and the polynomial-time canonical sum-of-squares relaxation provably fail. Theorem 8.2 (via Lemma 9.5) extends this to arbitrary constraint hypergraphs up to additional $\mathrm{polylog}(n)$ factors in the number of constraints.

<a id="pdf-9c5df3bb4a04-p053-b005"></a>
<!-- pdf-source: page=53; block=5; confidence=0.86 -->
**Lemma 9.6.** Let $\psi = (\mathcal{H}, \xi)$ be an instance of 3-SAT given by a 3-uniform hypergraph $\mathcal{H}$ on $[n]$ with $m \geq \tilde{O}(n^{1/4})$ arbitrary constraints and uniformly randomly generated literal patterns. Then with probability at least $1 - 1/10^{\mathrm{poly}(n)}$ over the draw of literal patterns, there is a polynomial-size refutation witness certifying $\mathrm{val}(\psi) < 1$.

<a id="pdf-9c5df3bb4a04-p053-b006"></a>
<!-- pdf-source: page=53; block=6; confidence=0.83 -->
**Proof Sketch.** For the 3-SAT predicate $P:\{\pm1\}^3\to\{0,1\}$, $P(\zeta) = \tfrac{7}{8} + \tfrac{1}{8}(\zeta_1+\zeta_2+\zeta_3) - \tfrac{1}{8}(\zeta_1\zeta_2 + \zeta_2\zeta_3 + \zeta_1\zeta_3 - \zeta_1\zeta_2\zeta_3)$. Then $\psi(x) = \tfrac{1}{|\mathcal{H}|}\sum_{C\in\mathcal{H}} P(x_{C_1}\xi_{C,1}, x_{C_2}\xi_{C,2}, x_{C_3}\xi_{C,3}) = \tfrac{7}{8} + \tfrac{1}{8|\mathcal{H}|}\sum_{C\in\mathcal{H}}\big(\xi_{C,1}x_{C_1} + \xi_{C,2}x_{C_2} + \xi_{C,3}x_{C_3} - \xi_{C,1}x_{C_1}\xi_{C,2}x_{C_2} - \xi_{C,2}x_{C_2}\xi_{C,3}x_{C_3} - \xi_{C,1}x_{C_1}\xi_{C,3}x_{C_3} + \xi_{C,1}\xi_{C,2}\xi_{C,3}x_{C_1}x_{C_2}x_{C_3}\big)$, with $\xi_{C,i}\in\{\pm1\}$ the literal negation patterns. Here $\psi(x)$ is the fraction of constraints satisfied by $x\in\{\pm1\}^n$; each of the 7 non-constant terms is refuted separately as its own XOR instance.

<a id="pdf-9c5df3bb4a04-p054-b001"></a>
<!-- pdf-source: page=54; block=1; confidence=0.86 -->
**Proof (continued).** Collecting coefficients: the first three terms each give a linear polynomial $\sum_i B_i x_i$; the next three give a homogeneous quadratic $\tfrac{1}{|\mathcal{H}|}\sum_{C\in\mathcal{H}} x_{C_i}x_{C_j}$; the last gives a cubic $\tfrac{1}{|\mathcal{H}|}\sum_{C\in\mathcal{H}} x_{C_1}x_{C_2}x_{C_3}$. The witness for each linear polynomial is $\|B\|_1$ with $B=(B_1,\dots,B_n)$, exactly the hypercube maximum of that term. For the quadratic case the witness is the value of the SDP relaxation for the $\infty\to 1$ norm, giving a $\sqrt{2}$-factor approximation to the maximum of bilinear forms over the hypercube. For the homogeneous degree-3 term the witness is an ideal FKO witness from Lemma 9.5.

<a id="pdf-9c5df3bb4a04-p054-b002"></a>
<!-- pdf-source: page=54; block=2; confidence=0.80 -->
**Proof (continued).** By Chernoff and union bound (over every $x\in\{\pm1\}^n$), $\|B\|_1$ for any linear term is at most $O(\sqrt{n/m})$. Similarly the $\infty\to1$ norm of the 2-XOR constraint matrix is at most $O(\sqrt{n/m})$, which by Grothendieck's inequality (Fact 3.6) is certifiable efficiently via an SDP with an extra loss of at most a factor $<2$. Thus all terms except the homogeneous degree-3 one are certified $\leq O(\sqrt{n/m})$. When $m \geq \tilde{\Omega}(n)\,n^{0.5(1-\delta)}$, i.e. $\ell = n^{\delta}$, Lemma 9.5 gives $\tfrac{m}{\tilde{O}(n^{\delta})}$ pairwise disjoint even covers of length $\leq \tilde{O}(n^{\delta})$; by Chernoff at least $1/3$ are violated, certifying an upper bound of $1 - \tfrac{1}{\tilde{O}(n^{\delta})}$ on the final term. Combining, the 3-SAT value is at most $\tfrac{7}{8} + \tfrac{1}{8}O(\sqrt{n/m}) + \tfrac{1}{8}\big(1 - \tfrac{1}{\tilde{O}(n^{\delta})}\big)$. For $\delta = 0.2$, $\sqrt{n/m} = \tilde{O}(n^{-0.25 + \delta/4}) \ll \tfrac{1}{\tilde{O}(n^{\delta})}$, so for $m \geq \tilde{O}(n^{1.4})$ a refutation is obtained with probability at least $1 - 1/\mathrm{poly}(n)$.

<a id="pdf-9c5df3bb4a04-p054-b003"></a>
<!-- pdf-source: page=54; block=3; confidence=0.90 -->
Lemma 9.6 generalizes to all $k$-CSPs with a non-trivial predicate $P$ (i.e. $P \not\equiv 1$). This requires only the basic fact below (Lemma 9.7), with the rest of the proof unchanged, plus known spectral refutation results for random $(k-1)$-arity and smaller XOR instances.

<a id="pdf-9c5df3bb4a04-p054-b004"></a>
<!-- pdf-source: page=54; block=4; confidence=0.93 -->
**Lemma 9.7.** Let $P:\{\pm1\}^k \to \{0,1\}$ with Fourier representation $\sum_{S\subseteq[k]} \hat{P}(S)\, x^S$. Then $\hat{P}(\emptyset) + |\hat{P}([k])| \leq 1$.

<a id="pdf-9c5df3bb4a04-p054-b005"></a>
<!-- pdf-source: page=54; block=5; confidence=0.92 -->
**Proof.** For each $b\in\{\pm1\}$, take the distribution uniform on all $x$ with $\prod_i x_i = b$. The expectation of $P$ under it equals exactly $\hat{P}(\emptyset) + b\,\hat{P}([k])$. Since $P$ takes values in $\{0,1\}$, this expectation is at most $1$, so $1 \geq \hat{P}(\emptyset) + b\,\hat{P}([k])$ for both $b$, giving $1 \geq \hat{P}(\emptyset) + |\hat{P}([k])|$.

<a id="pdf-9c5df3bb4a04-p054-b006"></a>
<!-- pdf-source: page=54; block=6; confidence=0.80 -->
A proof sketch generalizes Lemma 9.6 to all fully random CSPs, captured by Item (1) of Theorem 9.2. One assumes the Fourier coefficient $\hat{P}([k])$ is nonzero, since otherwise Theorem 7.4 already provides enough constraints for a polynomial-time deterministic refutation. (Footnote 9: there can be no $(k-1)$-uniform distribution $\mu$ supported on $P^{-1}(1)$, else $1 = \mathbb{E}_{x\sim\mu}[P(x)] = \hat{P}(\emptyset) < 1$, where $\hat{P}(\emptyset) < 1$ since $P$ is nontrivial; the instance then has [text continues off page].)

<a id="pdf-9c5df3bb4a04-p055-b001"></a>
<!-- pdf-source: page=55; block=1; confidence=0.85 -->
**Lemma 9.8** (Polynomial-size refutation witnesses for all random $k$-CSPs). Let $P:\{\pm1\}^k\to\{0,1\}$ be an arbitrary $k$-ary Boolean predicate, $k\ge 3$. Let $\psi$ be a CSP instance with predicate $P$ specified by $\mathcal H$, a collection of $m\ge m_0 = \tilde O(1)\cdot n^{\,k/2 - (k-2)/(2(k+2))}$ i.i.d. uniformly random $k$-tuples, together with i.i.d. uniformly random literal patterns $\{\xi(C,i)\}_{C\in\mathcal H,\,i\in[k]}$. Then with probability at least $1-1/\mathrm{poly}(n)$ over the draw of $\mathcal H$ and the $\xi(C,i)$, there exists a polynomial-size refutation witness for $\psi$.

<a id="pdf-9c5df3bb4a04-p055-b002"></a>
<!-- pdf-source: page=55; block=2; confidence=0.80 -->
**Proof.** The instance $\psi$ has $m = \tilde O(1)\cdot(n/\ell)^{k/2}\,\ell$ constraints for $\ell\le \tilde O(n^{1/(k+2)})$. Fourier-decompose $\psi(x):=\tfrac1{|\mathcal H|}\sum_{C\in\mathcal H}P(x_{C_1}\xi_{C,1},\dots,x_{C_k}\xi_{C,k})$ into $2^k$ polynomials, each of degree $t\le k$. Linear polynomials use the certificate of Lemma 9.6. For quadratic and higher degree ($\le k-1$) terms, use spectral refutation of fully random CSPs (e.g. Theorem 1 of [AOW15]): a degree-$t$ polynomial ($t\le k-1$) needs $\gtrsim \tilde O(n^{t/2}/\varepsilon^2)$ constraints to certify value $\le\varepsilon$, so one certifies $\varepsilon=\sqrt{n^{(k-1)/2}/m}$ on each polynomial, which is $\le 1$ by choice of $m$. For the top-degree polynomial (the $[k]$-indexed Fourier coefficient of $P$), use the Ideal FKO witness of Lemma 9.4. As in the earlier 3-SAT argument, this yields (w.p. $\ge 1-1/\mathrm{poly}(n)$) a certified upper bound $\hat P(\emptyset)+\tilde O(\sqrt{n^{(k-1)/2}/m})+|\hat P([k])|\cdot(1-\tilde O(1)/(\ell\log n))$ on $\psi$, via Lemma 9.5. Witness size $s(n)\le m_0=\mathrm{poly}(n)$ since the degree-$<k$ terms use deterministic refutations. By Lemma 9.7 this certifies $\psi(x)\le 1+\tilde O(\sqrt{n^{(k-1)/2}/m})-\tilde O(1)/(\ell\log n)=1-o(1)$, using $\ell\le\tilde O(1)\,n^{1/(k+2)}$. $\square$

<a id="pdf-9c5df3bb4a04-p055-b003"></a>
<!-- pdf-source: page=55; block=3; confidence=0.85 -->
**Remark (Item (2)).** Replacing the [AOW15] refutation with the semirandom refutation of Theorem 5.1 yields Item (2) of Theorem 9.2: polynomial-size refutation witnesses exist below the $n^{k/2}$ threshold for semirandom instances (proof omitted, being similar). The required $m$ is strictly larger than in Lemma 9.8 but still polynomially below $n^{k/2}$, because the semirandom refutation-strength dependence is $1/\varepsilon^5$ rather than $1/\varepsilon^2$; one takes $\varepsilon=(n^{(k-1)/2}/m)^{1/5}$ instead of $(n^{(k-1)/2}/m)^{1/2}$, giving $\ell=n^{1/(k+8)}$ and $m\ge\tilde O(1)\,n^{\,k/2-(k-2)/(2(k+8))}$. The $1/\varepsilon^5$ dependence is believed suboptimal but inherent to current techniques.

<a id="pdf-9c5df3bb4a04-p055-b004"></a>
<!-- pdf-source: page=55; block=4; confidence=0.70 -->
**Remark (large $k$).** For large $k$, the density needed for polynomial-size refutation witnesses in both Item (1) and Item (2) is $\sim n^{k/2-1/2-o_k(1)}$, a $\sqrt n$-factor "win" over the threshold at which spectral (and sum-of-squares) methods succeed.

<a id="pdf-9c5df3bb4a04-p055-b005"></a>
<!-- pdf-source: page=55; block=5; confidence=0.60 -->
**Remark ($k=3$).** For $k=3$ the semirandom bound improves to match the random-case $\tilde O(n^{1/4})$, because the instances in the decomposition are all semirandom 2-XOR instances, refutable with the correct $1/\varepsilon^2$ dependence.

<a id="pdf-9c5df3bb4a04-p056-b001"></a>
<!-- pdf-source: page=56; block=1; confidence=0.65 -->
(continued) via Proposition 5.2.2 and Theorem 5.2.3 of [Wit17], combined with the fact that a semirandom 2-XOR instance has value at most $\tfrac12+\varepsilon$ once $m\gg n/\varepsilon^2$.

<a id="pdf-9c5df3bb4a04-p056-b002"></a>
<!-- pdf-source: page=56; block=2; confidence=0.85 -->
**Remark (Item (3)).** By a Chernoff bound, if $m\ge O(1)\,m_0/q(\vec p)$ with $m_0=\tilde O(1)\,n^{\,k/2-(k-2)/(2(k+8))}$, then w.h.p. at least $m_0$ clauses of $\psi$ have all literals re-randomized by the smoothing process; call this subinstance $\psi'$. Being semirandom, $\psi'$ has a weak refutation by Item (2); nondeterministically guessing $\psi'$ shows the smoothed instance $\psi$ also has a weak refutation.

<a id="pdf-9c5df3bb4a04-p056-b003"></a>
<!-- pdf-source: page=56; block=3; confidence=0.75 -->
**Remark.** The smoothed nondeterministic refutation algorithm $V$ differs from the random/semirandom $V$ by the extra step of guessing $\psi'$; the smoothed $V$ can also serve in the random/semirandom settings by simply guessing $\psi'=\psi$.

<a id="pdf-9c5df3bb4a04-p056-b004"></a>
<!-- pdf-source: page=56; block=4; confidence=0.85 -->
**References.** Bibliography entries appearing on this page: [AF09] Alon–Feige, power of two/three/four probes (SODA 2009); [AGK21] Abascal–Guruswami–Kothari, strongly refuting all semi-random Boolean CSPs (SODA 2021); [AHL02] Alon–Hoory–Linial, Moore bound for irregular graphs; [Ahn20] Ahn, simpler strong refutation of random k-XOR (APPROX/RANDOM 2020); [AKK95] Arora–Karger–Karpinski, PTAS for dense NP-hard problems (STOC 1995); [ALWZ20] Alweiss–Lovett–Wu–Zhang, improved sunflower-lemma bounds (STOC 2020); [AOW15] Allen–O'Donnell–Witmer, how to refute a random CSP (FOCS 2015); [BCK15] Barak–Chan–Kothari, SoS lower bounds from pairwise independence (STOC 2015).

<a id="pdf-9c5df3bb4a04-p057-b001"></a>
<!-- pdf-source: page=57; block=1; confidence=0.85 -->
**References (continued).** [BM16] Barak–Moitra, noisy tensor completion via SoS (COLT 2016); [BS16] Barak–Steurer, proofs/beliefs/algorithms through SoS (lecture notes); [CGL04] Coja-Oghlan–Goerdt–Lanka, strong refutation heuristics for random k-SAT; [Cha13] Chan, approximation resistance from pairwise independent subgroups (STOC 2013); [Fei07] Feige, refuting smoothed 3CNF (FOCS 2007); [Fei08] Feige, small linear dependencies for low-weight binary vectors; [FKO06] Feige–Kim–Ofek, witnesses for non-satisfiability of dense random 3CNF (FOCS 2006); [FKP19] Fleming–Kothari–Pitassi, semialgebraic proofs and efficient algorithm design; [FLP16] Fotakis–Lampis–Paschos, sub-exponential approximation schemes for CSPs (STACS 2016); [FW16] Feige–Wagner, generalized girth problems in graphs/hypergraphs; [IP01] Impagliazzo–Paturi, complexity of k-SAT; [JHL+12] Dellamonica Jr. et al., even-degree subgraphs of linear hypergraphs; [KMOW17] Kothari–Mori–O'Donnell–Witmer, SoS lower bounds for refuting any CSP (STOC 2017); [KV00] Kim–Vu, concentration of multivariate polynomials.

<a id="pdf-9c5df3bb4a04-p058-b001"></a>
<!-- pdf-source: page=58; block=1; confidence=0.90 -->
Reference-list tail: [LPS88] Lubotzky–Phillips–Sarnak, *Ramanujan graphs*, Combinatorica 8(3):261–277, 1988; [Mar88] Margulis, explicit group-theoretic expander/concentrator constructions, Problemy Peredachi Informatsii 24(1):51–60, 1988; [MR10] Moshkovitz–Raz, two-query PCP with subconstant error, J. ACM 57(5), 2010; [NV08] Naor–Verstraëte, parity check matrices and product representations of squares, Combinatorica 28(2):163–185, 2008; [Rao19] Rao, *Coding for sunflowers*, CoRR abs/1909.04774, 2019; [RRS17] Raghavendra–Rao–Schramm, strongly refuting random CSPs below the spectral threshold, STOC 2017, 121–131; [SS12] Schudy–Sviridenko, concentration and moment inequalities for polynomials of independent random variables, SODA 2012, 437–446; [ST03] Spielman–Teng, smoothed analysis, LNCS 2748, 256–270, 2003; [Tro12] Tropp, user-friendly tail bounds for sums of random matrices, Found. Comput. Math. 12(4):389–434, 2012; [WAM19] Wein–El Alaoui–Moore, *The Kikuchi hierarchy and tensor PCA*, FOCS 2019, 1446–1468; [Wit17] Witmer, PhD thesis, Carnegie Mellon University, 2017.

<a id="pdf-9c5df3bb4a04-p058-b002"></a>
<!-- pdf-source: page=58; block=2; confidence=0.85 -->
**Appendix A. Analyzing the [WAM19] Approach for Random 3-XOR.**

<a id="pdf-9c5df3bb4a04-p058-b003"></a>
<!-- pdf-source: page=58; block=3; confidence=0.80 -->
Goal: show the [WAM19] approach (their Appendix F.1, F.2) for strongly refuting random $k$-XOR with $k$ odd does not give the right trade-off for $m$ as a function of $n/\ell$. The proof reduces to showing that a certain matrix defined in [WAM19] does *not* have small spectral norm. The argument is presented for $k=3$.

<a id="pdf-9c5df3bb4a04-p058-b004"></a>
<!-- pdf-source: page=58; block=4; confidence=0.80 -->
Let $\phi$ be a random 3-XOR instance in $n$ variables and $m$ clauses, with hypergraph $\mathcal{H}$ and coefficients $\{b_C\}_{C\in\mathcal{H}}$. Assume each pair $C_1\neq C_2\in\mathcal{H}$ satisfies $|C_1\cap C_2|\le 1$; this holds w.h.p. when $m\ll n^2$ (working regime $m\sim n^{1/5}$ or smaller; for $m\gg n^{1/5}$ a poly-time refutation exists [AGK21]). More precisely, when $m\ll n^2$, w.h.p. over $\mathcal{H}$ one can remove $o(m)$ constraints so the remaining hypergraph satisfies the condition.

<a id="pdf-9c5df3bb4a04-p059-b001"></a>
<!-- pdf-source: page=59; block=1; confidence=0.85 -->
Partition the hyperedges $\mathcal{H}$ arbitrarily into $\mathcal{H}_1,\dots,\mathcal{H}_n$ so that if $C\in\mathcal{H}_u$ then $u\in C$; write $\mathcal{H}=\bigcup_{u=1}^n\mathcal{H}_u$. The lower bound holds regardless of the partition chosen.

<a id="pdf-9c5df3bb4a04-p059-b002"></a>
<!-- pdf-source: page=59; block=2; confidence=0.75 -->
Let $\phi(x):=\frac{1}{m}\sum_{C\in\mathcal{H}} b_C x_C$, where $x_C:=\prod_{i\in C} x_i$. By Cauchy–Schwarz,
$$\phi(x)^2 \le \Big(\tfrac{1}{m}\sum_{u=1}^n x_u^2\Big)\Big(\tfrac{n}{m^2}\sum_{u=1}^n \sum_{C\neq C'\in\mathcal{H}_u} b_C b_{C'} x_{C\setminus u} x_{C'\setminus u}\Big) = \tfrac{n}{m}\,f(x),$$
where $f(x):=\frac{n}{m^2}\sum_{u=1}^n \sum_{C\neq C'\in\mathcal{H}_u} b_C b_{C'} x_{C\setminus u} x_{C'\setminus u}$.

<a id="pdf-9c5df3bb4a04-p059-b003"></a>
<!-- pdf-source: page=59; block=3; confidence=0.85 -->
**Definition A.1.** Let $\ell\in\mathbb{N}$ and $\mathcal{H}=\bigcup_{u=1}^n\mathcal{H}_u$ a 3-uniform hypergraph. For $\vec S,\vec T\in[n]^\ell$ and $C_1=\{u,v_1,w_1\}, C_2=\{u,v_2,w_2\}\in\mathcal{H}_u$ with $\{v_1,w_1\}\cap\{v_2,w_2\}=\emptyset$, write $\vec S \overset{C_1,C_2}{\leftrightarrow} \vec T$ if there exist $i\neq j\in[\ell]$ such that (1) $\vec S_t=\vec T_t$ for all $t\neq i,j$, and (2) $\{\vec S_i,\vec S_j\}$ contains exactly one element from each of $\{v_1,w_1\}$ and $\{v_2,w_2\}$, while $\{\vec T_i,\vec T_j\}$ contains the other two remaining elements ($\vec S_i$ = $i$-th element of $\vec S$). If $\vec S \overset{C_1,C_2}{\leftrightarrow} \vec T$ for some $C_1,C_2$, then no other pair $C_1',C_2'$ can give $\vec S \overset{C_1',C_2'}{\leftrightarrow} \vec T$.

<a id="pdf-9c5df3bb4a04-p059-b004"></a>
<!-- pdf-source: page=59; block=4; confidence=0.88 -->
**Definition (matrix $A$).** Let $A_u\in\mathbb{R}^{n^\ell\times n^\ell}$ be defined by $A_u(\vec S,\vec T)=b_{C_1}b_{C_2}$ if $\vec S \overset{C_1,C_2}{\leftrightarrow}\vec T$ for some $C_1\neq C_2\in\mathcal{H}_u$, and $0$ otherwise. Let $A:=\sum_{u=1}^n A_u$.

<a id="pdf-9c5df3bb4a04-p059-b005"></a>
<!-- pdf-source: page=59; block=5; confidence=0.88 -->
Observation: $\max_{x\in\{\pm1\}^n} f(x) \le \frac{n}{m^2}\cdot O\!\big(\frac{n^2}{\ell^2}\big)\cdot\|A\|_2$, since for all $x\in\{\pm1\}^n$,
$$\tfrac{m^2}{n} f(x) = \frac{1}{4\binom{\ell}{2}(n-4)^{\ell-2}}\,(x^{\otimes\ell})^\top A\, x^{\otimes\ell},$$
because each pair $C_1\neq C_2\in\mathcal{H}_u$ "appears" exactly $4\binom{\ell}{2}(n-4)^{\ell-2}$ times in $A$. To obtain the correct $m=n^{1.5}/\sqrt{\ell}$ trade-off one needs $\|A\|_2\le O(\ell)$ w.h.p. over $\mathcal{H}$ and the $b_C$'s.

<a id="pdf-9c5df3bb4a04-p059-b006"></a>
<!-- pdf-source: page=59; block=6; confidence=0.88 -->
Main claim: w.h.p. $\|A\|_2=\Omega\!\big(\min(\ell^2,\, m^2/n^2)\big)$, so the [WAM19] approach fails. Implications: if the min is $m^2/n^2$, the certified upper bound on $f$ is $\Omega(n/\ell^2)$, hence on $\phi$ it is $\Omega(\sqrt n/\ell)$, which exceeds $1$ when $\ell\ll\sqrt n$ (useless). If the min is $\ell^2$, a good bound on $f$ (and $\phi$) follows only when $m\ge n^{1.5}$, higher than the desired threshold $n^{1.5}/\sqrt\ell$.

<a id="pdf-9c5df3bb4a04-p059-b007"></a>
<!-- pdf-source: page=59; block=7; confidence=0.80 -->
**Proposition A.2.** Let $\phi$ be a 3-XOR instance with $n$ variables, $m$ constraints, hypergraph $\mathcal{H}=\bigcup_{u=1}^n\mathcal{H}_u$ and coefficients $\{b_C\}_{C\in\mathcal{H}}$. Suppose that $2n\le m$ and $|C_1\cap C_2|\le 1$ for every pair $C_1\neq C_2\in\mathcal{H}$. Let $\ell\le n$. Then $\|A\|_2 \ge \binom{\ell'}{2}$, where $\ell':=\min\!\big(\lceil m/(2n)\rceil,\,\ell\big)$.

<a id="pdf-9c5df3bb4a04-p059-b008"></a>
<!-- pdf-source: page=59; block=8; confidence=0.80 -->
Proposition A.2 holds regardless of the partition of $\mathcal{H}$ into the $\mathcal{H}_u$ and for any choice of the $b_C$ (in particular random $b_C$). It also holds essentially for random $\mathcal{H}$ provided $m\ll n^2$: w.h.p. after removing $o(m)$ constraints the resulting $\mathcal{H}'$ satisfies $|C_1\cap C_2|\le1$ for all pairs.

<a id="pdf-9c5df3bb4a04-p060-b001"></a>
<!-- pdf-source: page=60; block=1; confidence=0.80 -->
**Proof.** Since $m\ge 2n$, some variable $u\in[n]$ appears in $\ge m/n$ constraints, so $\ge \lceil m/(2n)\rceil$ of them include $u$ with the same sign $b\in\{\pm1\}$. Set $\ell':=\min(\lceil m/(2n)\rceil,\ell)$; get constraints $\{C_i\}_{i\in[\ell']}=\{\{u,v_i,w_i\}\}_{i\in[\ell']}$ with $b_{C_i}=b$. By the assumption $|C_i\cap C_j|\le1$ and since $u\in C_i\cap C_j$, we get $\{v_i,w_i\}\cap\{v_j,w_j\}=\emptyset$.

Fix arbitrary padding element $\diamond\in[n]$. Let $\mathcal{R}$ be the set of tuples $(r_1,\dots,r_{\ell'},\diamond,\dots,\diamond)\in[n]^\ell$ with $r_i\in\{v_i,w_i\}$ for all $i\in[\ell']$ ($\diamond$ pads to length $\ell$ when $\ell'<\ell$). Let $M$ be the submatrix of $A$ indexed by $\mathcal{R}$; then $M$ is $2^{\ell'}\times 2^{\ell'}$ since $|\mathcal{R}|=2^{\ell'}$. Claim: each row of $M$ has exactly $\binom{\ell'}{2}$ nonzero entries, all equal to $1$.

Contribution from $A_u$: fix row $\vec S\in\mathcal{R}$. For each pair $i\neq j\in[\ell']$, replacing the $i$-th and $j$-th entries of $\vec S$ by the elements of $\{v_i,w_i\},\{v_j,w_j\}$ not used in $\vec S$ yields $\vec T\in\mathcal{R}$ with $\vec S \overset{\{u,v_i,w_i\},\{u,v_j,w_j\}}{\leftrightarrow}\vec T$, so $A_u(\vec S,\vec T)=b^2=1$. Any other $\vec T\in\mathcal{R}$ differs from $\vec S$ in $\ge2$ entries, giving $A_u(\vec S,\vec T)=0$.

Contribution from $A_{u'}$, $u'\neq u$: it suffices to consider $\vec T$ obtained by swapping the $i,j$ entries. If $A_{u'}(\vec S,\vec T)\neq0$ then $\vec S\overset{\{u',v_i,w_i\},\{u',v_j,w_j\}}{\leftrightarrow}\vec T$, so $\{u',v_i,w_i\},\{u',v_j,w_j\}\in\mathcal{H}_{u'}$; but then $|\{u,v_i,w_i\}\cap\{u',v_i,w_i\}|=2>1$, contradicting the assumption.

Hence $M$ is $2^{\ell'}\times2^{\ell'}$ with each row having exactly $\binom{\ell'}{2}$ nonzero entries all equal to $1$. Therefore $\|A\|_2\ge\|M\|_2\ge \dfrac{(\mathbf{1}_{2^{\ell'}})^\top M\,\mathbf{1}_{2^{\ell'}}}{2^{\ell'}}=\binom{\ell'}{2}$. $\qquad\blacksquare$
