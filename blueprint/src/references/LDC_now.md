<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: 4377a4b7ed99c28302f5e670a8defa94d0c931bcfaf1f8d0122797ce2e6a357c -->

<a id="pdf-4377a4b7ed99-p073-b001"></a>
<!-- pdf-source: page=73; block=1; confidence=0.85 -->
**Proof (continued).** Taking one representative per equivalence class, the orbits of U′ cover all of Z_m^n, so |U′| = |U|/φ(m) ≤ m^n/φ(m). For the orbit of a vector u ∈ U contributing u_1 = λ_1u, …, u_t = λ_tu (λ_i ∈ Z_m) with matching vectors v_1,…,v_t ∈ V, the sets U′ = {λ_1,…,λ_t} and V′ = {(u,v_1),…,(u,v_t)} form a matching-vector family in one dimension, so t ≤ k(m,1). Hence k(m,n) ≤ (m^n/φ(m))·k(m,1) ≤ m^{n−1+o_m(1)}. Uses the standard lower bound [54], φ(m) ≥ Ω(m/log log m), and lemma 5.24.

<a id="pdf-4377a4b7ed99-p073-b002"></a>
<!-- pdf-source: page=73; block=2; confidence=0.95 -->
**Notes.**

<a id="pdf-4377a4b7ed99-p073-b003"></a>
<!-- pdf-source: page=73; block=3; confidence=0.90 -->
Grolmusz's original construction of set systems with restricted intersections modulo composites is given in [49, 50]; an important ingredient is the low-degree representation of the OR-function from [10]. Our proof of Lemma 5.5 follows [48, theorem 2.16]; Lemma 5.7 is from [34, 18]; the construction in section 5.2 and the upper bounds in sections 5.4–5.6 are from [34].

<a id="pdf-4377a4b7ed99-p073-b004"></a>
<!-- pdf-source: page=73; block=4; confidence=0.90 -->
The combinatorial study of set systems with restricted modular intersections relates to the maximal cardinality of a (Z_m∖{0})-matching family of vectors in Z_m^n. The precise combinatorial problem: bound the largest set family F on [n] whose sets have cardinality ≡ 0 (mod m) while all pairwise intersections have nonzero cardinality (mod m). Classically, for prime-power m an upper bound of n^{O(m)} holds [6]; no such bound applies when m is composite [49]. The best bound for general m is |F| ≤ 2^{n/2} [84].

<a id="pdf-4377a4b7ed99-p074-b001"></a>
<!-- pdf-source: page=74; block=1; confidence=0.90 -->
**5 Lower bounds.**

<a id="pdf-4377a4b7ed99-p074-b002"></a>
<!-- pdf-source: page=74; block=2; confidence=0.85 -->
Reviews existing lower bounds on the codeword length of general locally decodable codes. High-level strategy: (1) convert an LDC into a normal form whose decoder outputs a modulo-2 sum of r codeword coordinates drawn from a family of disjoint r-tuples; (2) argue any normal-form code requires large codeword length. Roadmap: §5.1 — the normal-form conversion; §5.2 — polynomial lower bounds for r-query codes for general r (degrading rapidly as r grows); §5.3 — tight exponential lower bounds for the special case of 2-query codes. Throughout, attention is restricted to binary codes of constant query complexity.

<a id="pdf-4377a4b7ed99-p074-b003"></a>
<!-- pdf-source: page=74; block=3; confidence=0.80 -->
**5.1 Preliminaries.**

<a id="pdf-4377a4b7ed99-p074-b004"></a>
<!-- pdf-source: page=74; block=4; confidence=0.85 -->
General locally decodable codes can be complex: decoders may invoke complicated adaptive procedures to decide which codeword bits to query… (continues on next page).

<a id="pdf-4377a4b7ed99-p075-b001"></a>
<!-- pdf-source: page=75; block=1; confidence=0.85 -->
…to query, and may perform arbitrary computation to produce the output. To prove lower bounds it is convenient to first convert such codes into the following normal form.

<a id="pdf-4377a4b7ed99-p075-b002"></a>
<!-- pdf-source: page=75; block=2; confidence=0.92 -->
**Definition 6.1.** A binary code C: 𝔽_2^k → 𝔽_2^N is (r, η, β)-normally decodable if for each i ∈ [k] there is a collection M_i of η·N disjoint tuples of exactly r indices from [N] such that for every t ∈ M_i:

Pr_{x∈𝔽_2^n}[ x_i = ∑_{j∈t} C(x)_j ] ≥ 1/2 + β   (6.1)

where the probability is taken uniformly over x.

<a id="pdf-4377a4b7ed99-p075-b003"></a>
<!-- pdf-source: page=75; block=3; confidence=0.85 -->
To decode x_i from B(x), the decoder adds up the coordinates of a randomly chosen tuple from L_i. Normally decodable codes are weaker than usual LDCs: they provide only an average-case guarantee of correct decoding. The section's goal is to prove the following lemma.

<a id="pdf-4377a4b7ed99-p075-b004"></a>
<!-- pdf-source: page=75; block=4; confidence=0.90 -->
**Lemma 6.2.** If there exists a (r, δ, ε)-locally decodable code encoding k-bit messages to N-bit codewords where ε < 1/2, then there exists a (r, η, β)-normally decodable code encoding k-bit messages to O(N)-bit codewords, where η ≥ (1/2−ε)δ/(3·r²2^{r−1}) and β ≥ (1/2−ε)/2^{2r}.

<a id="pdf-4377a4b7ed99-p075-b005"></a>
<!-- pdf-source: page=75; block=5; confidence=0.85 -->
**Proof.** Proceeds in four steps. (1) Turn a possibly adaptive decoder of B into a non-adaptive one that makes all codeword queries simultaneously. (2) Turn the code into a smooth one, where no codeword coordinate is queried too often. (3) Ensure the r-tuples of coordinates that may be read by the decoder for the i-th message bit are all disjoint. (4) Finally … (text continues past the supplied pages).

<a id="pdf-4377a4b7ed99-p076-b001"></a>
<!-- pdf-source: page=76; block=1; confidence=0.85 -->
**§6.1 Preliminaries.** Sets up the multi-step reduction turning an arbitrary local decoder for code $C$ into normal form; on the fourth step the decoder is forced to always return the modulo-2 sum of the accessed codeword coordinates, and each step incurs some loss in code parameters. Let $\alpha = 1/2 - \varepsilon$ denote the advantage of $C$'s local decoder over random guessing.

<a id="pdf-4377a4b7ed99-p076-b002"></a>
<!-- pdf-source: page=76; block=2; confidence=0.88 -->
**Step 1.** Let $A$ be the (possibly adaptive) local decoder for $C$. Construct a non-adaptive local decoder $A'$ for the same code, at the price of reducing the advantage from $\alpha$ to $\alpha/2^{r-1}$. $A'$ guesses the values of the first $r-1$ coordinates that $A$ may access and submits the whole query set determined by that guess; if the guess is correct, decoding succeeds (probability $\ge \tfrac12+\alpha$ on that branch), otherwise $A'$ outputs a uniformly random bit, correct with probability $\tfrac12$.

<a id="pdf-4377a4b7ed99-p076-b003"></a>
<!-- pdf-source: page=76; block=3; confidence=0.90 -->
**Step 2.** Adjust the non-adaptive $r$-query decoder $A$ into $A'$ so that for all $x\in\{0,1\}^k$ and $i\in[k]$:

$$\Pr[A'(C(x),i)=x_i]\ \ge\ \tfrac12+\alpha/2^{r-1}\qquad(6.2)$$
$$\forall i\in[k],\,j\in[N]:\ \Pr[A'(\cdot,i)\text{ reads index }j]\ \le\ \tfrac{r}{\delta N}\qquad(6.3)$$

For each $i$ let $S_i\subseteq[N]$ be the coordinates $A$ reads (on message index $i$) with probability above $\tfrac{r}{\delta N}$; since $A$ reads $\le r$ indices per invocation, $|S_i|\le\delta N$. Define $A'(\cdot,i)$ to run $A(\cdot,i)$ as a black box, but whenever $A$ queries an index in $S_i$, $A'$ returns $0$ instead of reading it. Thus $A'(C(x))$ equals $A$'s output on some string $y$ with relative Hamming distance $\Delta(C(x),y)\le\delta$, and on any such $y$, $A$ still outputs $x_i$ with probability $\ge\tfrac12+\alpha/2^{r-1}$.

<a id="pdf-4377a4b7ed99-p076-b004"></a>
<!-- pdf-source: page=76; block=4; confidence=0.50 -->
**Step 2.** Modify $A$ so that, for each $i$, the coordinate-tuples the decoder may read for the $i$-th message bit are pairwise disjoint. Fix $i\in[k]$; for arbitrary $R\subseteq[M]$ with $|R|\le r$, call $R$ **$\gamma$-good** if

$$\Pr_x\big[\,A(B(x),i)=x_i\ \wedge\ A\text{ reads its coordinates within }R\,\big]\ \ge\ \tfrac12+\gamma.\qquad(5.3)$$

<a id="pdf-4377a4b7ed99-p079-b001"></a>
<!-- pdf-source: page=79; block=1; confidence=0.88 -->
**Normal form (continued).** Replacing every coordinate $c$ of $C(x)$ with a triple $\{0,c,\bar c\}$ brings the decoder to normal form: for each $i\in[k]$ it picks one of the $r$-tuples of coordinates from a matching $M_i$ at random and outputs the modulo-2 sum. The construction yields matchings of size at least $\tfrac{(1/2-\varepsilon)\,\delta N}{3\,r^{2}2^{r-1}}$, and the advantage over random guessing is at least $\alpha/2^{2r}$.

<a id="pdf-4377a4b7ed99-p079-b002"></a>
<!-- pdf-source: page=79; block=2; confidence=0.55 -->
**§ Polynomial lower bound for $r$-query codes.** Goal: prove an $\Omega\!\big(k^{\,r/(r-1)}\big)$ lower bound on the codeword length $M$ of any $r$-query locally decodable code. Proof idea (random restriction): if $B$ is short, restricting $B$ to a randomly chosen small subset of coordinates still carries too much information about the message. $H(\cdot)$ denotes the binary entropy function.

<a id="pdf-4377a4b7ed99-p079-b003"></a>
<!-- pdf-source: page=79; block=3; confidence=0.90 -->
**Lemma 6.3.** Let $C:\mathbb{F}_2^k\to D$ be an arbitrary function. If there exists a randomized algorithm $A$ such that for all $i\in[k]$, $\Pr[A(C(x),i)=x_i]\ge \tfrac12+\beta$ (probability over $A$'s coins and over uniform $x$), then $\log|D|\ge (1-H(1/2+\beta))\,k$.

<a id="pdf-4377a4b7ed99-p079-b004"></a>
<!-- pdf-source: page=79; block=4; confidence=0.60 -->
**Proof.** Let $I(x;B(x))$ be the mutual information between the message $x$ and $B(x)$. Then $I(x;B(x))\le H(B(x))\le\log|C|$. *(continued on next page)*

<a id="pdf-4377a4b7ed99-p080-b001"></a>
<!-- pdf-source: page=80; block=1; confidence=0.55 -->
**Proof (continued).** Also $I(x;B(x))=H(x)-H(x\mid B(x))\ge H(x)-\sum_{i}H(x_i\mid B(x))\ge (1-H(\beta))\,k$, using $H(x)=k$ for uniform $x\in\{0,1\}^k$ and Fano ($H(x_i\mid B(x))\le H(\beta)$). Combining with $I(x;B(x))\le\log|C|$ yields $\log|C|\ge(1-H(\beta))k$. $\square$

<a id="pdf-4377a4b7ed99-p080-b002"></a>
<!-- pdf-source: page=80; block=2; confidence=0.85 -->
**Theorem 6.4.** Suppose there exists an $(r,\delta,\varepsilon)$-locally decodable code encoding $k$-bit messages into $N$-bit codewords; then for sufficiently large $k$,

$$N\ \ge\ \Omega\!\Big(\Big(\tfrac{(1/2-\varepsilon)\delta}{r^{2}}\Big)^{1/(r-1)}\Big(\big(1-H\big(\tfrac12+\tfrac{1/2-\varepsilon}{2^{2r}}\big)\big)\cdot k\Big)^{r/(r-1)}\Big).$$

<a id="pdf-4377a4b7ed99-p080-b003"></a>
<!-- pdf-source: page=80; block=3; confidence=0.85 -->
**Proof.** Assume the contrary: for infinitely many $k$ there is a code $C$ violating the stated bound. Apply Lemma 6.2 to put $C$ in normal form, obtaining an $(r,\eta,\beta)$-normally decodable code with $\eta\ge\tfrac{(1/2-\varepsilon)\delta}{3\,r^{2}2^{r-1}}$ and $\beta\ge\tfrac{1/2-\varepsilon}{2^{2r}}$, using matchings $\{M_i\}_{i\in[k]}$. Let $\alpha$ be a constant (chosen later). Pick $S\subseteq[N]$ at random, including each element independently with probability $\alpha k/N$. Let $y$ count the matchings $M_i$ having at least one hyperedge completely contained in $S$. Then

$$\mathbb{E}[y]\ \ge\ \Big[1-\big(1-(\alpha k/N)^{r}\big)^{\eta N}\Big]k\ \ge\ \Big[1-(1/e)^{\eta(\alpha k)^{r}/N^{\,r-1}}\Big]k.$$

Since $C$ violates the theorem's bound, $N=O_{r,\delta,\varepsilon}(k^{\,r/(r-1)})$; substituting bounds the right-hand side of the inequality above from below.

<a id="pdf-4377a4b7ed99-p081-b001"></a>
<!-- pdf-source: page=81; block=1; confidence=0.90 -->
**Proof (continued).** The right-hand side is at least $\Omega_{r,\delta,\varepsilon}(k)$. Since $y$ takes non-negative integer values up to $k$, there is a positive constant probability that $y$ is larger than $\mathbb{E}[y]/2$. By a Chernoff bound the probability that $|S|>2\alpha k$ is exponentially small in $k$. Hence there exists a set $S\subseteq[N]$ with $|S|\le 2\alpha k$ that contains a hyperedge from at least

$$m=0.5\cdot\Big[1-(1/e)^{\eta(\alpha k)^{r}/N^{\,r-1}}\Big]\cdot k$$

distinct matchings $\{M_i\}_{i\in[k]}$. Thus restricting $C$ to the coordinates in $S$ lets one make $(1/2+\beta)$-accurate predictions about $m$ coordinates of $x$. By Lemma 6.3 this forces

$$\Big[1-(1/e)^{\eta(\alpha k)^{r}/N^{\,r-1}}\Big]\cdot(1-H(1/2+\beta))\cdot k\ \le\ 4\alpha k;$$

setting $\alpha=(1-H(1/2+\beta))$ and simplifying yields $N\ge\Omega\big(k^{\,r/(r-1)}\cdot\eta^{1/(r-1)}\cdot\alpha^{r/(r-1)}\big)$. Expressing $\eta$ and $\alpha$ in terms of $\delta$ and $\varepsilon$ concludes the proof. ∎

<a id="pdf-4377a4b7ed99-p081-b002"></a>
<!-- pdf-source: page=81; block=2; confidence=0.92 -->
**§6.3 Exponential lower bound for 2-query codes.** Establishes an asymptotically tight $2^{\Omega(k)}$ lower bound on the codeword length of any 2-query locally decodable code, via quantum information theory: short 2-query LDCs yield short quantum random access codes, then Nayak's theorem [70] bounds the length of such codes. A brief self-contained introduction to the needed quantum information theory follows (comprehensive treatment in [71]).

<a id="pdf-4377a4b7ed99-p081-b003"></a>
<!-- pdf-source: page=81; block=3; confidence=0.82 -->
**§6.3.1 Quantum information theory.** For a positive integer n, an n-qubit quantum state is a vector φ ∈ ℂ^{2^n} with Σ_{j∈[2^n]} |φ_j|² = 1. Given an orthonormal basis B = {b_j}_{j∈[2^n]} of ℂ^{2^n}, measuring φ in basis B yields outcome j ∈ [2^n] with probability |⟨φ, b_j⟩|².

<a id="pdf-4377a4b7ed99-p082-b001"></a>
<!-- pdf-source: page=82; block=1; confidence=0.90 -->
**Definition (quantum random access code).** An encoding x ↦ q_x mapping k-bit strings x to n-qubit states q_x such that any individual bit x_i (i ∈ [k]) can be recovered with probability p ≥ 1/2 + β from q_x, where the probability is taken over a uniform choice of x and the measurement randomness.

<a id="pdf-4377a4b7ed99-p082-b002"></a>
<!-- pdf-source: page=82; block=2; confidence=0.95 -->
**Theorem 6.5 (Nayak [70], special case of the Holevo bound [55]).** Any encoding x ↦ q_x of k-bit strings into n-qubit states with recovery probability at least 1/2 + β necessarily satisfies n ≥ (1 − H(1/2 + β)) · k, where H is the binary entropy function.

<a id="pdf-4377a4b7ed99-p082-b003"></a>
<!-- pdf-source: page=82; block=3; confidence=0.92 -->
**§6.3.2 Lower bound. Theorem 6.6.** If there exists a (2, δ, ε)-locally decodable code C encoding k-bit messages to N-bit codewords, then N ≥ 2^{Ω((1/2−ε)^4 δ² k)}.

<a id="pdf-4377a4b7ed99-p082-b004"></a>
<!-- pdf-source: page=82; block=4; confidence=0.90 -->
**Proof.** Apply Lemma 6.2 to turn C into normal form, yielding a (2, η, β)-normally decodable code with η ≥ Ω((1/2−ε)δ) and β ≥ Ω(1/2−ε). Pad with zeros so the codeword length N is a power of two, N = 2^n. For every x ∈ {0,1}^k consider the n-qubit state q_x, where q_j = (−1)^{C(x)_j} / √N for all j ∈ [N] (eq. 6.6). We claim that x ↦ q_x is a quantum random access code. Fix i ∈ [k]; to recover x_i from q_x, measure in a suitable basis: let e_m denote the m-th unit vector in ℝ^N and let M_i = {(c_1^ℓ, c_2^ℓ)}_{ℓ∈[ηN]} be the matching used by the decoder for bit i. [Text truncated at end of page.]
