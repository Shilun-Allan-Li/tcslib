<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: 26d95080dbde050d736933aacc8a97ed1f204cbb37b868dfa35d5d8b7125d0ae -->

<a id="pdf-26d95080dbde-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.97 -->
# Chapter 7: Randomized Computation

_Opening quote (Michael Rabin, 1976) on incorporating randomization into the algorithm itself, with two examples: nearest pair among n points in ℝ^k, and an extremely efficient algorithm for primality testing._

<a id="pdf-26d95080dbde-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.92 -->
Introduction. So far the standard model was the deterministic TM; real-life computers have "random number generators." Whether the universe has true randomness is open (quantum mechanics suggests yes); assuming true random generators exist, a realistic model is a TM with a random number generator, called a Probabilistic Turing Machine (PTM). The chapter defines BPP (languages decidable by polynomial-time PTMs) and relates it to P/poly and PH; one consequence: if PH does not collapse, then 3SAT has no efficient probabilistic algorithm. Error can be reduced to minuscule quantities. BPP and sister classes RP, coRP, ZPP are arguably as important as P in capturing efficient computation. Related notions: probabilistic logspace algorithms and probabilistic reductions.

<a id="pdf-26d95080dbde-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.90 -->
Randomization has led to more efficient and simpler algorithms in combinatorial optimization, algebraic computation, machine learning, network routing; cryptography and interactive/probabilistically checkable proofs rely on randomness essentially. Later chapters: if a plausible complexity conjecture is true, every probabilistic algorithm can be derandomized with polynomial overhead (Chapters 16, 17). Elementary probability on finite sample spaces is assumed (Appendix A).

<a id="pdf-26d95080dbde-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.93 -->
## 7.1 Probabilistic Turing machines

A PTM is syntactically identical to an NDTM: a TM with two transition functions δ₀, δ₁. The difference is interpretation: instead of asking whether some choice sequence accepts, we ask how large the fraction of choices is. In every step, M applies δ₀ or δ₁ each with probability 1/2. M decides a language if it outputs the right answer with probability at least 2/3. Picking δ₀/δ₁ with equal probability at each step is equivalent to a "fair coin" whose tosses are Heads/Tails with equal probability regardless of past history.

<a id="pdf-26d95080dbde-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.97 -->
**Definition 7.1 (The classes BPTIME and BPP).** For T : ℕ → ℕ and L ⊆ {0,1}*, a PTM M decides L in time T(n) if for every x ∈ {0,1}*, M halts in T(|x|) steps regardless of its random choices, and Pr[M(x) = L(x)] ≥ 2/3, where L(x) = 1 if x ∈ L and L(x) = 0 otherwise. **BPTIME**(T(n)) is the class of languages decided by PTMs in O(T(n)) time; **BPP** = ⋃_c **BPTIME**(n^c).

<a id="pdf-26d95080dbde-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.90 -->
**Remark 7.2.** The definition is robust (Section 7.4): the coin need not be fair; the constant 2/3 is arbitrary — any constant greater than half gives the same classes BPTIME(T(n)) and BPP; one could also allow expected polynomial time rather than always halting in polynomial time.

<a id="pdf-26d95080dbde-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.92 -->
**Remark 7.3.** Definition 7.1 allows M(x) to err with positive probability, but only over M's random choices: for *every* input x, M(x) outputs L(x) with probability ≥ 2/3. Thus BPP, like P, is a class capturing *worst-case* computation.

<a id="pdf-26d95080dbde-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.92 -->
A deterministic TM is a special case of a PTM (both transition functions equal), so P ⊆ BPP. Under plausible assumptions BPP = P, but as far as we know it may even be that BPP = EXP. (BPP ⊆ EXP: in time 2^{poly(n)} one can enumerate all random choices of a polynomial-time PTM and compute exactly the probability that M(x) = 1.)

<a id="pdf-26d95080dbde-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.97 -->
**Definition 7.4 (BPP, alternative definition).** BPP contains a language L if there exists a polynomial-time TM M and a polynomial p : ℕ → ℕ such that for every x ∈ {0,1}*, Pr_{r ∈_R {0,1}^{p(|x|)}}[M(x, r) = L(x)] ≥ 2/3. (As with NP, the "probabilistic choices" are provided to a deterministic TM as an additional input.)

<a id="pdf-26d95080dbde-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.90 -->
## 7.2 Some examples of PTMs

### 7.2.1 Probabilistic Primality Testing

Primality testing: given integer N, decide whether it is prime, ideally in time poly(log n) (polynomial in the representation size). The first efficient algorithms (1970s) were probabilistic; Agrawal–Kayal–Saxena later gave a deterministic polynomial-time algorithm.

<a id="pdf-26d95080dbde-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.85 -->
Formally, primality testing is membership in PRIMES = {⌊N⌋ : N is a prime number} (N in binary). The corresponding search problem, FACTORING, seems much harder; its conjectured hardness underlies cryptosystems; Chapter 20 covers Shor's quantum algorithm.

<a id="pdf-26d95080dbde-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.90 -->
Sketch that PRIMES ∈ BPP (in fact coRP). For number N and A ∈ [N−1], define QR_N(A) = 0 if gcd(A,N) ≠ 1; +1 if A is a quadratic residue mod N (A = B² (mod N) with gcd(B,N)=1); −1 otherwise. Facts (elementary number theory): (i) for odd prime N and A ∈ [N−1], QR_N(A) = A^{(N−1)/2} (mod N); (ii) for odd N, A, the Jacobi symbol (N/A) := ∏_{i=1}^k QR_{P_i}(A) over N's prime factorization is computable in time O(log A · log N); (iii) for odd composite N, |{A ∈ [N−1] : gcd(N,A)=1 and (N/A) = A^{(N−1)/2}}| ≤ ½|{A ∈ [N−1] : gcd(N,A)=1}|. Algorithm (N odd wlog): choose random 1 ≤ A < N; if gcd(A,N) > 1 or (N/A) ≠ A^{(N−1)/2} (mod N) output "composite", else "prime". Always says "prime" on primes; on composite N outputs "composite" with probability ≥ 1/2 (amplifiable by repetition).

<a id="pdf-26d95080dbde-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.92 -->
### 7.2.2 Polynomial identity testing

Given a polynomial with integer coefficients in implicit form as an *arithmetic circuit*: an n-variable arithmetic circuit is a DAG with sources labeled by variables x₁,…,x_n, each non-source node with in-degree two labeled by an operator from {+, −, ×}, and a single output sink; it computes a polynomial ℤⁿ → ℤ. ZEROP = the set of arithmetic circuits computing the identically zero polynomial.

<a id="pdf-26d95080dbde-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.90 -->
Deciding equality of two circuits C, C′ reduces to ZEROP via D = C − C′ (this is *polynomial identity testing*). Expanding a circuit may produce exponentially many monomials, so ZEROP membership seems hard, yet has a simple efficient probabilistic algorithm, based on the Schwartz–Zippel Lemma (proof in Appendix A, Lemma A.25):

<a id="pdf-26d95080dbde-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.97 -->
**Lemma 7.5 (Schwartz–Zippel).** Let p(x₁, x₂, …, x_m) be a polynomial of total degree at most d and S any finite set of integers. When a₁, a₂, …, a_m are randomly chosen with replacement from S, then Pr[p(a₁, a₂, …, a_m) ≠ 0] ≥ 1 − d/|S|. (Implicitly: p is not the identically zero polynomial.)

<a id="pdf-26d95080dbde-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.90 -->
A size-m circuit C on n variables defines a polynomial of degree at most 2^m. Algorithm: choose x₁,…,x_n from 1 to 10·2^m (O(n·m) random bits), evaluate C, accept iff the output y = 0. If C ∈ ZEROP we always accept; otherwise reject with probability ≥ 9/10 by the lemma. Problem: intermediate values can be as large as (10·2^m)^{2^m} — exponentially many bits.

<a id="pdf-26d95080dbde-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.88 -->
Fix via *fingerprinting*: evaluate C modulo a random k ∈ [2^{2m}], computing y (mod k). If y = 0 then y (mod k) = 0. Claim: if y ≠ 0 then with probability at least δ = 1/(10m), k ∤ y (repeat O(1/δ) times to detect with probability ≥ 9/10). Proof: suffices that k is a prime not among y's distinct prime factors 𝒮 = {p₁,…,p_ℓ}; by the prime number theorem Pr[k prime] ≥ 1/(5m) = 2δ; y ≤ (10·2^m)^{2^m} has log y ≤ 5m2^m distinct factors, so Pr[k ∈ 𝒮] ≤ 5m2^m/2^{2m} ≪ 1/(10m) = δ; union bound gives Pr ≥ δ that k is prime and k ∤ y.

<a id="pdf-26d95080dbde-p005-b005"></a>
<!-- pdf-source: page=5; block=5; confidence=0.90 -->
### 7.2.3 Testing for perfect matching in a bipartite graph

G = (V₁, V₂, E) bipartite with |V₁| = |V₂| = n; a perfect matching is E′ ⊆ E where every node appears exactly once, equivalently a permutation σ on {1,…,n} with (i, σ(i)) ∈ E for all i. Lovász's randomized algorithm uses the Schwartz–Zippel lemma.

<a id="pdf-26d95080dbde-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.92 -->
Let X be the n×n matrix with X_{ij} the variable x_{ij} if (i,j) ∈ E and 0 otherwise. det(X) = Σ_{σ ∈ S_n} (−1)^{sign(σ)} ∏_{i=1}^n X_{i,σ(i)}  (equation (1)). Every permutation is a potential perfect matching, and its monomial in det(X) is nonzero iff the matching exists in G; so G has a perfect matching iff det(X) ≢ 0. The polynomial has |E| variables and total degree at most n, and can be evaluated efficiently for any integer assignment (determinant is polynomial-time, even NC²). Lovász's algorithm: pick random values for the X_{ij} from [1,…,2n], compute the determinant, accept iff nonzero. Advantage: implementable as a randomized NC circuit — fast in parallel (Section 6.5.1).

<a id="pdf-26d95080dbde-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.92 -->
## 7.3 One-sided and zero-sided error: RP, coRP, ZPP

BPP captures two-sided error. Many probabilistic algorithms have *one-sided* error: if x ∉ L they never output 1. This is RP.

<a id="pdf-26d95080dbde-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.95 -->
**Definition 7.6.** **RTIME**(t(n)) contains every language L for which there is a probabilistic TM M running in t(n) time such that x ∈ L ⇒ Pr[M accepts x] ≥ 2/3, and x ∉ L ⇒ Pr[M accepts x] = 0. **RP** = ⋃_{c>0} **RTIME**(n^c).

<a id="pdf-26d95080dbde-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.92 -->
RP ⊆ NP: every accepting branch is a certificate. (In contrast, BPP ⊆ NP is not known.) **coRP** = {L : L̄ ∈ RP} — one-sided error in the other direction (may wrongly accept x ∉ L, never wrongly rejects x ∈ L). For a PTM M and input x, the random variable T_{M,x} is the running time of M on x: Pr[T_{M,x} = T] = p if with probability p over the random choices M halts within T steps. M has *expected running time* T(n) if E[T_{M,x}] ≤ T(|x|) for every x ∈ {0,1}*.

<a id="pdf-26d95080dbde-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.95 -->
**Definition 7.7.** The class **ZTIME**(T(n)) contains all languages L for which there is an expected-time O(T(n)) machine that never errs: x ∈ L ⇒ Pr[M accepts x] = 1, and x ∉ L ⇒ Pr[M halts without accepting x] = 1. **ZPP** = ⋃_{c>0} **ZTIME**(n^c).

<a id="pdf-26d95080dbde-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.95 -->
**Theorem 7.8.** ZPP = RP ∩ coRP. (Proof left to the reader, Exercise 4. Slightly surprising since the corresponding statement for nondeterminism — P = NP ∩ coNP? — is open.) Summary of relations: ZPP = RP ∩ coRP; RP ⊆ BPP; coRP ⊆ BPP.

<a id="pdf-26d95080dbde-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.92 -->
## 7.4 The robustness of our definitions

### 7.4.1 Role of precise constants, error reduction

The constant 2/3 can be replaced by any constant larger than 1/2, and in fact even by 1/2 + n^{−c} for constant c > 0.

<a id="pdf-26d95080dbde-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.95 -->
**Lemma 7.9.** For c > 0, let BPP_{n^{−c}} denote the class of languages L for which there is a polynomial-time PTM M satisfying Pr[M(x) = L(x)] ≥ 1/2 + |x|^{−c} for every x ∈ {0,1}*. Then BPP_{n^{−c}} = BPP. (Clearly BPP ⊆ BPP_{n^{−c}}; the other direction is by the much stronger error-reduction Theorem 7.10.)

<a id="pdf-26d95080dbde-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.95 -->
**Theorem 7.10 (Error reduction).** Let L ⊆ {0,1}* be a language and suppose there exists a polynomial-time PTM M such that for every x ∈ {0,1}*, Pr[M(x) = L(x)] ≥ 1/2 + |x|^{−c}. Then for every constant d > 0 there exists a polynomial-time PTM M′ such that for every x ∈ {0,1}*, Pr[M′(x) = L(x)] ≥ 1 − 2^{−|x|^d}.

**Proof.** M′: on input x, run M(x) k times obtaining outputs y₁, …, y_k ∈ {0,1}, where k = 8|x|^{2d+c}; accept iff the majority of the values are 1. Analysis: let X_i = 1 if y_i = L(x), else 0; X₁,…,X_k are independent Boolean random variables with E[X_i] = Pr[X_i = 1] ≥ 1/2 + n^{−c} (n = |x|). Apply the Chernoff bound (Theorem A.18).

<a id="pdf-26d95080dbde-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.93 -->
**Corollary 7.11.** Let X₁, …, X_k be i.i.d. Boolean random variables with Pr[X_i = 1] = p for every i, and δ ∈ (0,1). Then Pr[|((1/k)Σ_{i=1}^k X_i) − p| > δ] < e^{−(δ²/4)pk}. In our case p = 1/2 + n^{−c}; plugging δ = n^{−c}/2, the probability of a wrong answer is bounded by Pr[(1/k)Σ X_i ≤ 1/2 + n^{−c}/2] ≤ e^{−(1/(4n^{2c}))·(1/2)·8n^{2c+d}} ≤ 2^{−n^d}. ∎ (The draft's displayed intermediate expression writes (1/n)Σ; the intended normalization is (1/k)Σ.)

<a id="pdf-26d95080dbde-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.93 -->
**Theorem 7.12 (RP error reduction).** Let L ⊆ {0,1}* be such that there exists a polynomial-time PTM M satisfying for every x: (1) x ∈ L ⇒ Pr[M(x) = 1] ≥ n^{−c}; (2) x ∉ L ⇒ Pr[M(x) = 1] = 0. Then for every d > 0 there is a polynomial-time PTM M′ with: (1) x ∈ L ⇒ Pr[M′(x) = 1] ≥ 1 − 2^{−n^d}; (2) x ∉ L ⇒ Pr[M′(x) = 1] = 0. (For RP the constant 2/3 can be replaced by any positive constant, even n^{−c}.)

<a id="pdf-26d95080dbde-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.90 -->
Consequence: modest success probability can be amplified to overwhelming; error 2^{−n} is negligible for all practical purposes. If the original algorithm used m coins, running k independent trials and taking majority uses O(m·k) random coins to make the error exponentially small in k; surprisingly, O(m + k) random bits suffice (Section 7.5).

<a id="pdf-26d95080dbde-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.88 -->
**Note 7.13 (The Chernoff Bound).** Typical scenario: a universe 𝒰 of objects, a fraction μ with a certain property; estimate μ by sampling n members independently at random and taking k/n where k counts sampled members with the property. Allow error ±ε and failure probability δ. The Chernoff bound says the required number of samples is O(log(1/δ)/ε²) (μ treated as constant). Sampling n elements, the probability that k is ρ√n away from μn decays exponentially with ρ (the bell curve). Used throughout the book, starting with Theorem 7.17 (BPP ⊆ P/poly). [Figure: bell curve centered at μn with width ~√n — unavailable in source.]

<a id="pdf-26d95080dbde-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.90 -->
### 7.4.2 Expected running time versus worst-case running time

RTIME(T(n)) and BPTIME(T(n)) required halting in T(n) time regardless of random choices. Using *expected* running time instead yields an equivalent definition: add a time counter to a PTM M with expected running time T(n) and halt after 100·T(n) steps; by Markov's inequality (Lemma A.10), Pr[M runs longer] ≤ 1/100, so the acceptance probability changes by at most 1/100.

<a id="pdf-26d95080dbde-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.92 -->
### 7.4.3 Allowing more general random choices than a fair random coin

A ρ-coin comes up heads with probability ρ (possibly irrational, e.g. 1/e). **Lemma 7.14.** A coin with Pr[Heads] = ρ can be simulated by a PTM in expected time O(1), provided the i-th bit of ρ is computable in poly(i) time. **Proof.** Let ρ = 0.p₁p₂p₃…. Generate random bits b₁, b₂, … one by one (b_i at step i); if b_i < p_i output "heads" and stop; if b_i > p_i output "tails" and halt; else continue. The machine reaches step i+1 iff b_j = p_j for all j ≤ i (probability 1/2^i), so Pr[heads] = Σ_i p_i/2^i = ρ; expected running time Σ_i i^c · 1/2^i = O(1) (Exercise 1). ∎

<a id="pdf-26d95080dbde-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.92 -->
**Lemma 7.15 (Von-Neumann).** A coin with Pr[Heads] = 1/2 can be simulated by a probabilistic TM with access to a stream of ρ-biased coins in expected time O(1/(ρ(1−ρ))). **Proof.** Toss pairs of ρ-coins until the two results differ; on "heads-tails" output heads, on "tails-heads" output tails. Each pair: HH with probability ρ², TT with (1−ρ)², HT with ρ(1−ρ), TH with (1−ρ)ρ; conditioned on halting (probability 2ρ(1−ρ) per pair) the two outputs are equiprobable. Knowledge of ρ is not needed. ∎

<a id="pdf-26d95080dbde-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.90 -->
**Weak random sources.** Conceivably computers only have access to *imperfect* randomness — unpredictable but not independent coins. Chapter 16: probabilistic algorithms designed for perfect independent 1/2-coins can be simulated even with such a weak random source.

<a id="pdf-26d95080dbde-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.90 -->
## 7.5 Randomness efficient error reduction

Goal: error reduction without independent runs, "recycling" random bits (general theory in Chapter 16). Main tool: *expander graphs*. Informal combinatorial view: graphs where every not-too-big vertex subset S has a boundary (neighbors outside S) proportional, up to constant factor, to |S|. The n×n grid is not an expander: a k×k square (size k²) has boundary only O(k) (Figure 7.1: combinatorial expander vs grid; unavailable in source).

<a id="pdf-26d95080dbde-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.90 -->
Precise definitions deferred to Section 7.B. An *expander graph family* is a sequence {G_N}_{N∈ℕ} where G_N is an N-vertex D-degree graph, D a constant. Deep (and more recently, simpler) mathematics constructs such families; these constructions are algorithmically useful: given the binary representation of N and the index of a node in G_N, the indices of the node's D neighbors can be produced in poly(log N) time.

<a id="pdf-26d95080dbde-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.90 -->
Error reduction for RP via expander walks. Given an RP algorithm M using m coins with one-sided success probability ≥ 1/2 (i.e., x ∈ L ⇒ Pr_{r∈_R{0,1}^m}[M(x,r) = 1] ≥ 1/2; x ∉ L ⇒ M(x,r) = 0 for all r): let N = 2^m and G_N an N-vertex expander family member. Use m coins to pick a random vertex v, then log Dk coins for a (k−1)-step random walk from v (each step: choose i ∈ [D] at random, move to the i-th neighbor). Let v₁ = v, …, v_k be the visited vertices, treated as elements of {0,1}^m; run M on x with each of these as coins; output 1 iff at least one run outputs 1. Resulting error 2^{−Ω(k)} using m + O(k)·O(1) coins: if fewer than half the r's make M output 0, the probability the walk is fully contained in these "bad" r's is exponentially small in k.

<a id="pdf-26d95080dbde-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.93 -->
**Theorem 7.16.** Let G be an expander graph of N vertices and B a subset of G's vertices of size at most βN, where β < 1. Then the probability that a k-vertex random walk is fully contained in B is at most ρ^k, where ρ < 1 is a constant depending only on β (and independent of k). (Intuition: a constant fraction of edges adjacent to B's vertices leave B. Precise formulation and analysis in Section 7.B.)

<a id="pdf-26d95080dbde-p012-b003"></a>
<!-- pdf-source: page=12; block=3; confidence=0.93 -->
## 7.6 BPP ⊆ P/poly

All BPP languages have polynomial-sized circuits; together with the Karp–Lipton theorem this implies that if 3SAT ∈ BPP then PH = Σ₂^p. (The draft cites "Theorem ??" for the Karp–Lipton consequence.)

**Theorem 7.17 (Adleman).** BPP ⊆ P/poly.

**Proof (start).** Suppose L ∈ BPP; by the alternative definition (Def 7.4) and the error reduction of Theorem 7.10, there exists a TM M that on inputs of size n uses m random bits and satisfies: x ∈ L ⇒ Pr_r[M(x,r) accepts] ≥ 1 − 2^{−(n+2)}; x ∉ L ⇒ Pr_r[M(x,r) accepts] ≤ 2^{−(n+2)}.

<a id="pdf-26d95080dbde-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.92 -->
**Proof of Theorem 7.17 (end).** Call r ∈ {0,1}^m *bad* for x ∈ {0,1}^n if M(x,r) is incorrect, else *good* for x. For every x, at most 2·2^m/2^{(n+2)} values of r are bad; summing over all x ∈ {0,1}^n, at most 2^n × 2^m/2^{(n+1)} = 2^m/2 strings r are bad for *some* x. So at least 2^m − 2^m/2 choices of r are good for *every* x ∈ {0,1}^n. Hardwire such an r₀ to obtain a circuit C (of size at most quadratic in M's running time) that on input x outputs M(x, r₀); then C(x) = L(x) for every x ∈ {0,1}^n. ∎

<a id="pdf-26d95080dbde-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.92 -->
## 7.7 BPP is in PH

**Theorem 7.18 (Sipser–Gács).** BPP ⊆ Σ₂^p ∩ Π₂^p.

**Proof (start).** It suffices to prove BPP ⊆ Σ₂^p since BPP is closed under complementation (BPP = coBPP). Suppose L ∈ BPP. By Def 7.4 and error reduction (Thm 7.10) there is a polynomial-time deterministic TM M for L using m = poly(n) random bits on length-n inputs with: x ∈ L ⇒ Pr_r[M(x,r) accepts] ≥ 1 − 2^{−n}; x ∉ L ⇒ Pr_r[M(x,r) accepts] ≤ 2^{−n}. For x ∈ {0,1}^n let S_x ⊆ {0,1}^m be the set of r's for which M accepts (x,r). Either |S_x| ≥ (1 − 2^{−n})2^m or |S_x| ≤ 2^{−n}2^m according to whether x ∈ L; two alternations can distinguish the cases. (Figure 7.2: a huge S_x can be "shifted" a few times to cover {0,1}^m, a tiny one cannot — unavailable in source.)

<a id="pdf-26d95080dbde-p013-b003"></a>
<!-- pdf-source: page=13; block=3; confidence=0.90 -->
For k = ⌈m/n⌉ + 1, let U = {u₁, …, u_k} be a set of k strings in {0,1}^m. Define G_U as the graph with vertex set {0,1}^m and edges (r, s) whenever r = s + u_i for some i ∈ [k] (+ = bitwise XOR).

<a id="pdf-26d95080dbde-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.90 -->
**Proof of Theorem 7.18 (end).** The degree of G_U is k. For S ⊆ {0,1}^m define Γ_U(S) as all neighbors of S in G_U (r ∈ Γ_U(S) iff r = s + u_i for some s ∈ S, i ∈ [k]). Claim 1: for every S with |S| ≤ 2^{m−n} and every U of size k, Γ_U(S) ≠ {0,1}^m — since |Γ_U(S)| ≤ k|S| < 2^m. Claim 2: for every S with |S| ≥ (1 − 2^{−n})2^m there exists U of size k with Γ_U(S) = {0,1}^m — by the probabilistic method: choose u₁,…,u_k at random; for r ∈ {0,1}^m the "bad event" B_r that r ∉ Γ_U(S) is ∩_{i∈[k]} B_r^i where B_r^i is the event r + u_i ∉ S (using a+b=c ⇔ a=c+b mod 2); r + u_i is uniform, so Pr[B_r^i] ≤ 2^{−n}, independently over i, giving Pr[B_r] ≤ (2^{−n})^k < 2^{−m}; union bound: Pr[Γ_U(S) ≠ {0,1}^m] ≤ Σ_{r∈{0,1}^m} Pr[B_r] < 1. Claims 1+2 give: x ∈ L iff ∃u₁,…,u_k ∈ {0,1}^m ∀r ∈ {0,1}^m ⋁_{i=1}^k M(x, r ⊕ u_i) accepts — a Σ₂ statement, so L ∈ Σ₂^p. ∎

<a id="pdf-26d95080dbde-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.90 -->
## 7.8 State of our knowledge about BPP

Known: P ⊆ BPP ⊆ P/poly, and BPP ⊆ Σ₂^p ∩ Π₂^p; if NP = P then BPP = P. Believed: BPP ⊆ DTIME(2^ε) for every ε > 0 [sic: 2^{n^ε}], suspected BPP = P; yet BPP = NEXP not ruled out. **Complete problems for BPP?** No complete languages known for BPP under deterministic polynomial-time reductions. The defining property of BPTIME machines is *semantic* (every input accepted w.p. ≥ 2/3 or rejected w.p. ≥ 1/3 — undecidable to test), vs *syntactic* for NDTMs. Natural attempt L = {⟨M, x⟩ : Pr[M(x) = 1] ≥ 2/3} is BPP-hard but not known to be in BPP, and not in any level of PH unless it collapses. If BPP = P then BPP has a complete problem. Promise problems sidestep some issues (not explored).

<a id="pdf-26d95080dbde-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.90 -->
**Does BPTIME have a hierarchy theorem?** Is BPTIME(n^c) ⊆ BPTIME(n) for some c > 1? Presumably not, but we currently cannot even show BPTIME(n^{log² n}) ⊄ BPTIME(n); standard diagonalization fails for semantic classes. Recent progress on hierarchy theorems for closely related classes (see notes).

<a id="pdf-26d95080dbde-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.93 -->
## 7.9 Randomized reductions

**Definition 7.19.** Language A reduces to language B under a randomized polynomial-time reduction, A ≤_r B, if there is a probabilistic TM M such that for every x ∈ {0,1}*, Pr[B(M(x)) = A(x)] ≥ 2/3. If A ≤_r B and B ∈ BPP then A ∈ BPP. **Definition 7.20 (BP·NP).** BP·NP = {L : L ≤_r 3SAT}. (Analogous to NP = {L : L ≤_p 3SAT} via Cook–Levin. Properties explored in exercises, incl. whether ¬3SAT ∈ BP·NP; Chapter 9 gives a randomized reduction from 3SAT to solving 3SAT instances promised unsatisfiable-or-uniquely-satisfiable.)

<a id="pdf-26d95080dbde-p015-b003"></a>
<!-- pdf-source: page=15; block=3; confidence=0.92 -->
## 7.10 Randomized space-bounded computation

A PTM works in space S(n) if every branch requires space O(S(n)) on inputs of size n and terminates in 2^{O(S(n))} time (read-only input tape; work space counts read/write work tapes only; two transition functions applied with equal probability). Most interesting: O(log n) work tape. BPL and RL are the two-sided and one-sided error probabilistic analogs of L (Chapter 4).

<a id="pdf-26d95080dbde-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.93 -->
**Definition 7.21 (The classes BPL and RL).** A language L is in **BPL** if there is an O(log n)-space probabilistic TM M with Pr[M(x) = L(x)] ≥ 2/3. A language L is in **RL** if there is an O(log n)-space probabilistic TM M such that x ∈ L ⇒ Pr[M(x) = 1] ≥ 2/3 and x ∉ L ⇒ Pr[M(x) = 1] = 0. (The draft's header carries a stray "([" — citation bracket glitch.)

<a id="pdf-26d95080dbde-p016-b002"></a>
<!-- pdf-source: page=16; block=2; confidence=0.92 -->
Error reduction works with only logarithmic space overhead, so the constants are again insignificant. RL ⊆ NL ⊆ P, and BPL ⊆ P (exercise). UPATH: given an n-vertex undirected graph G and vertices s, t, decide whether s is connected to t.

**Theorem 7.22 ([AKL+79]).** UPATH ∈ RL.

Algorithm: take a random walk of length n³ starting from s (v ← s; repeatedly move to a random neighbor); accept iff the walk reaches t within n³ steps. If s ̸∼ t, never accepts. If s ∼ t, the expected number of steps to hit t is at most (4/27)n³, so accept with probability ≥ 3/4 [the intended bound via Markov: reject probability ≤ (4/27)/1 < 1/4]. Analysis deferred to Section 7.A (with a somewhat larger walk; see also Exercise 9). Chapter 16: a deterministic logspace algorithm for the same problem (Reingold); BPL (hence RL) ⊆ SPACE(log^{3/2} n); also a simulation of BPL in log² n space and polynomial time.

<a id="pdf-26d95080dbde-p017-b001"></a>
<!-- pdf-source: page=17; block=1; confidence=0.92 -->
**What have we learned?** BPP: languages solvable by probabilistic polynomial-time algorithms, probability over the coins only — arguably a better formalization of efficient computation than P. RP, coRP, ZPP: subclasses with one-sided and "zero-sided" error. Repetition amplifies success probability considerably. P ⊆ BPP ⊆ EXP is all we know, but BPP = P is suspected. BPP ⊆ P/poly and BPP ⊆ PH; the latter implies that if NP = P then BPP = P. Randomness also appears in randomized reductions and randomized logspace algorithms.

<a id="pdf-26d95080dbde-p017-b002"></a>
<!-- pdf-source: page=17; block=2; confidence=0.90 -->
**Chapter notes and history.** Probabilistic TMs: von Neumann [von61], de Leeuw et al. [LMSS56]. Definitions of BPP, RP, ZPP: Gill [Gil77]. PRIMES ∈ coRP: Solovay–Strassen [SS77]; also Rabin [Rab80]; later AKS proved PRIMES ∈ P. Lovász's randomized NC matching algorithm [Lov79]; finding matchings: [KUW86, MVV87]. BPP ⊆ P/poly: Adleman [Adl78]. BPP ⊆ PH: Sipser [Sip83]; the stronger BPP ⊆ Σ₂^p ∩ Π₂^p: P. Gács. Recent work places BPP in seemingly weaker classes. BPP/1 hierarchy theorems [Bar02, ...].

<a id="pdf-26d95080dbde-p018-b001"></a>
<!-- pdf-source: page=18; block=1; confidence=0.90 -->
Notes (cont.). Books on randomized algorithms: Mitzenmacher–Upfal [MU05], Motwani–Raghavan [MR95]. Expanders' application to pseudorandomness: Ajtai–Komlós–Szemerédi [AKS87]; recycling random bits: Cohen–Wigderson [CW89], Impagliazzo–Zuckerman (1989), as in Section 7.B.3. Introductory text: Hoory–Linial–Wigderson. Explicit expander construction: Reingold–Vadhan–Wigderson [RVW00] (presented via the replacement product rather than zig-zag). Deterministic logspace undirected connectivity: Reingold.

<a id="pdf-26d95080dbde-p018-b002"></a>
<!-- pdf-source: page=18; block=2; confidence=0.90 -->
**Exercises 1–7.** §1: for every c > 0, Σ_{i≥1} i^c/2^i is finite. §2: given a, n, p in binary, compute a^n (mod p) in polynomial time (hint: repeated squaring). §3: describe a real ρ such that a TM with a ρ-biased coin can decide an undecidable language in polynomial time (hint: ρ as an advice string). §4: show ZPP = RP ∩ coRP. §5: a nondeterministic circuit C has two inputs x, y; it accepts x iff ∃y C(x,y) = 1; size measured in |x|; NP/poly = languages decided by polynomial-size nondeterministic circuits; show BP·NP ⊆ NP/poly. §6: Karp–Lipton-style: if ¬3SAT ∈ BP·NP then PH collapses to Σ₃^p (so 3SAT ≤_r ¬3SAT is unlikely). §7: show BPL ⊆ P (hint: compute the acceptance probability via dynamic programming or matrix multiplication).

<a id="pdf-26d95080dbde-p019-b001"></a>
<!-- pdf-source: page=19; block=1; confidence=0.88 -->
**Exercises 8–9.** §8: the random-walk idea fails for directed graphs: a digraph on n vertices and start s with a directed path s→t but expected time Ω(2^n) to reach t. §9: G an n-vertex regular graph. (a) A distribution 𝐩 over vertices is *stable* if one random step from 𝐩 yields 𝐩; the uniform distribution is stable. (b) Δ(𝐩) = max_i |𝐩_i − 1/n|; 𝐩^k = distribution after k random steps from 𝐩; if G is connected there is k with Δ(𝐩^k) ≤ (1 − n^{−10n})Δ(𝐩); conclude (i) uniform is the only stable distribution, (ii) for every u, v and ε > 0 there is k such that the k-step walk from u hits v between (1−ε)k/n and (1+ε)k/n times with probability ≥ 1−ε. (c) E_u = expected steps for a walk from u to return to u; E_u ≤ 10n². (d) E_{u,v} = expected steps from u to reach v; if u, v connected by a path of length ≤ k then E_{u,v} ≤ 100kn²; conclude that for connected s, t the probability a 1000n³-step walk from s misses t is ≤ 1/10. (e) G non-regular: add parallel self-loops per vertex to make G′ regular; if a k-step walk in G′ from s hits t with probability ≥ 0.9, then a 10n²k-step walk in G from s hits t with probability ≥ 1/2.

<a id="pdf-26d95080dbde-p020-b001"></a>
<!-- pdf-source: page=20; block=1; confidence=0.90 -->
**Exercises 10–12 (based on Sections 7.A, 7.B).** §10: A symmetric stochastic matrix (A = A†, rows and columns nonnegative summing to 1) has ‖A‖ ≤ 1 (hint: show ‖A‖ ≤ n² first, then use ‖A^k v‖₂ ≥ ‖Av‖₂^k-type bootstrapping via ⟨w, Bz⟩ = ⟨B†w, z⟩ and ⟨w,z⟩ ≤ ‖w‖₂‖z‖₂). §11: for symmetric stochastic A, B: λ(A+B) ≤ λ(A) + λ(B) [sic — presumably for the averaged/appropriately normalized sum]. §12: an (n,d) random graph: choose d random permutations π₁,…,π_d ["ldots" typo in draft] from [n] to [n]; G contains edge (u,v) iff v = π_i(u) for some i ≤ d. A random (n,d) graph is an (n, 2d, (2/3)d) combinatorial expander with probability 1 − o(1) (hint: for every S, |S| ≤ n/2, and T with |T| ≤ (1 + (2/3)d)|S| [as printed], bound the probability that π_i(S) ⊆ T for every i).

<a id="pdf-26d95080dbde-p021-b001"></a>
<!-- pdf-source: page=21; block=1; confidence=0.92 -->
## 7.A Random walks and eigenvalues

Random walks on (undirected regular) graphs; the spectral gap of the adjacency matrix; corollary: correctness of the random-walk algorithm for UPATH (Theorem 7.22). Assumes elementary linear algebra (Appendix A). **Remark 7.23.** Restriction to *regular* graphs; definitions and results generalize suitably to non-regular graphs.

<a id="pdf-26d95080dbde-p021-b002"></a>
<!-- pdf-source: page=21; block=2; confidence=0.92 -->
### 7.A.1 Distributions as vectors and the parameter λ(G)

G a d-regular n-vertex graph. A probability distribution 𝐩 over vertices is a column vector in ℝⁿ with |𝐩|₁ = Σ|𝐩_i| = 1. One random-walk step from 𝐩 gives 𝐪 = A𝐩 where A = A(G) is the *normalized adjacency matrix*: A_{i,j} = (number of edges between i and j)/d. A is symmetric with entries in [0,1] and each row and column summing to 1 (*symmetric stochastic*). With {𝐞^i} the standard basis, A^T 𝐞^s is the distribution X_T of a T-step random walk from s.

<a id="pdf-26d95080dbde-p021-b003"></a>
<!-- pdf-source: page=21; block=3; confidence=0.95 -->
**Definition 7.25 (The parameter λ(G)).** Let **1** = (1/n, …, 1/n) (uniform distribution) and **1**^⊥ = {𝐯 : ⟨𝐯, **1**⟩ = (1/n)Σ_i 𝐯_i = 0}. The parameter λ(A), also denoted λ(G), is the maximum of ‖A𝐯‖₂ over all 𝐯 ∈ **1**^⊥ with ‖𝐯‖₂ = 1.

<a id="pdf-26d95080dbde-p022-b001"></a>
<!-- pdf-source: page=22; block=1; confidence=0.90 -->
**Note 7.24 (L_p norms).** A norm satisfies ‖𝐯‖ ≥ 0 with equality iff 𝐯 = 0; ‖α𝐯‖ = |α|‖𝐯‖; triangle inequality. L_p norm: ‖𝐯‖_p = (Σ|𝐯_i|^p)^{1/p}; p = 2 Euclidean; p = 1 written |𝐯|₁; p = ∞: max_i |𝐯_i|. Hölder: for 1/p + 1/q = 1, ‖𝐮‖_p‖𝐯‖_q ≥ Σ|𝐮_i 𝐯_i| (proof by scaling + weighted AM–GM a^α b^{1−α} ≤ αa + (1−α)b from concavity of log). Consequences: ‖𝐯‖₂² ≤ |𝐯|₁‖𝐯‖_∞; Cauchy–Schwarz (p = q = 2): Σ|𝐮_i 𝐯_i| ≤ ‖𝐮‖₂‖𝐯‖₂; with 𝐮 = (1/√n,…,1/√n): |𝐯|₁/√n ≤ ‖𝐯‖₂.

<a id="pdf-26d95080dbde-p023-b001"></a>
<!-- pdf-source: page=23; block=1; confidence=0.92 -->
**Remark 7.26.** λ(G) is the *second largest eigenvalue* (in absolute value): A symmetric gives an orthogonal eigenbasis 𝐯¹,…,𝐯ⁿ with |λ₁| ≥ |λ₂| ≥ … ≥ |λ_n|; A**1** = **1** so **1** is an eigenvector with eigenvalue 1; all eigenvalues of a symmetric stochastic matrix have absolute value ≤ 1 (Exercise 10), so take λ₁ = 1, 𝐯¹ = **1**; on **1**^⊥ = Span{𝐯²,…,𝐯ⁿ} the maximum of ‖A𝐯‖₂ is attained at 𝐯², so λ(G) = |λ₂|. 1 − λ(G) is the *spectral gap*. (Some texts use un-normalized adjacency matrices: λ(G) ∈ [0,d], spectral gap d − λ(G).)

<a id="pdf-26d95080dbde-p023-b002"></a>
<!-- pdf-source: page=23; block=2; confidence=0.93 -->
**Lemma 7.27.** For every regular n-vertex graph G = (V,E) and any probability distribution 𝐩 over V, ‖A^T 𝐩 − **1**‖₂ ≤ λ^T. **Proof.** By definition ‖A𝐯‖₂ ≤ λ‖𝐯‖₂ for 𝐯 ⊥ **1**; if 𝐯 ⊥ **1** then A𝐯 ⊥ **1** (since ⟨**1**, A𝐯⟩ = ⟨A†**1**, 𝐯⟩ = ⟨**1**, 𝐯⟩ = 0, using A = A† and A**1** = **1**), so A maps **1**^⊥ to itself, shrinking by λ each application: λ(A^T) ≤ λ(A)^T (in fact λ(A^T) = λ(A)^T). Write 𝐩 = α**1** + 𝐩′ with 𝐩′ ⊥ **1**; α = 1 since 𝐩 is a distribution (coordinates of 𝐩′ sum to 0). Then A^T 𝐩 = **1** + A^T 𝐩′; orthogonality gives ‖𝐩‖₂² = ‖**1**‖₂² + ‖𝐩′‖₂², so ‖𝐩′‖₂ ≤ ‖𝐩‖₂ ≤ |𝐩|₁ · 1 ≤ 1 (Note 7.24), hence ‖A^T 𝐩 − **1**‖₂ = ‖A^T 𝐩′‖₂ ≤ λ^T. ∎

<a id="pdf-26d95080dbde-p023-b003"></a>
<!-- pdf-source: page=23; block=3; confidence=0.92 -->
**Lemma 7.28.** Every connected graph has a noticeable spectral gap: for every d-regular connected G with self-loops at each vertex, λ(G) ≤ 1 − 1/(8dn³). **Proof (start).** Let 𝐮 ⊥ **1** be a unit vector, 𝐯 = A𝐮. Show 1 − ‖𝐯‖₂² ≥ 1/(4dn³), which implies ‖𝐯‖₂² ≤ 1 − 1/(4dn³) and hence ‖𝐯‖₂ ≤ 1 − 1/(8dn³).

<a id="pdf-26d95080dbde-p024-b001"></a>
<!-- pdf-source: page=24; block=1; confidence=0.90 -->
**Proof of Lemma 7.28 (end).** Since ‖𝐮‖₂ = 1: 1 − ‖𝐯‖₂² = ‖𝐮‖₂² − ‖𝐯‖₂². Claim: this equals Σ_{i,j} A_{i,j}(𝐮_i − 𝐯_j)², since Σ_{i,j} A_{i,j}(𝐮_i − 𝐯_j)² = Σ A_{i,j}𝐮_i² − 2Σ A_{i,j}𝐮_i𝐯_j + Σ A_{i,j}𝐯_j² = ‖𝐮‖₂² − 2⟨A𝐮, 𝐯⟩ + ‖𝐯‖₂² = ‖𝐮‖₂² − 2‖𝐯‖₂² + ‖𝐯‖₂² (rows/columns of A sum to 1; ‖𝐯‖₂² = ⟨𝐯,𝐯⟩ = ⟨A𝐮,𝐯⟩ = Σ A_{i,j}𝐮_i𝐯_j). It suffices that A_{i,j}(𝐮_i − 𝐯_j)² ≥ 1/(4n³)·(1/d) for *some* i, j. Self-loops give A_{i,i} ≥ 1/d, so assume |𝐮_i − 𝐯_i| < 1/(2n^{1.5}) for all i (else done). Sort 𝐮₁ ≥ 𝐮₂ ≥ … ≥ 𝐮_n; Σ𝐮_i = 0 and unit norm force 𝐮₁ ≥ 1/√n or 𝐮_n ≤ −1/√n, so 𝐮₁ − 𝐮_n ≥ 1/√n; some consecutive gap has 𝐮_{i₀} − 𝐮_{i₀+1} ≥ 1/n^{1.5}; set S = {1,…,i₀}. G connected gives an edge (i,j) ∈ S × S̄; for it, 𝐮_i − 𝐯_j ≥ 𝐮_i − 𝐮_j − 1/(2n^{1.5}) ≥ 1/(2n^{1.5}), so A_{i,j}(𝐮_i − 𝐯_j)² ≥ (1/d)·(1/(4n³)). ∎ **Remark 7.29.** Strengthens to every connected non-bipartite graph (self-loops not needed); some condition is essential: bipartite A has a vector with A𝐯 = −𝐯.

<a id="pdf-26d95080dbde-p024-b002"></a>
<!-- pdf-source: page=24; block=2; confidence=0.92 -->
### 7.A.2 Analysis of the randomized algorithm for undirected connectivity

**Corollary 7.30.** Let G be a d-regular n-vertex graph with all vertices having a self-loop, s a vertex, T > 10dn³ log n, and X_T the distribution of the T-th step of a random walk from s. Then for every j connected to s, Pr[X_T = j] > 1/(2n). **Proof.** Restrict to the connected component of s; by Lemmas 7.27 and 7.28, for any probability vector 𝐩 and T ≥ 10dn³ log n, ‖A^T 𝐩 − **1**‖₂ < 1/(2n^{1.5}) (**1** uniform over the component). By L₁–L₂ relations (Note 7.24), |A^T 𝐩 − **1**|₁ < 1/(2n), so every element of the component has probability ≥ 1/n − 1/(2n) ≥ 1/(2n) in A^T 𝐩. ∎ Repeating the 10dn³ log n walk 10n times (equivalently a walk of length 100dn⁴ log n) hits t with probability ≥ 3/4.

<a id="pdf-26d95080dbde-p025-b001"></a>
<!-- pdf-source: page=25; block=1; confidence=0.92 -->
## 7.B Expander graphs

Two equivalent definitions of expanders: *combinatorial* — a constant-degree regular graph where every subset S of less than half the vertices has a constant fraction of the edges touching S go to its complement; *algebraic* — a constant-degree regular graph with λ(G) ≤ 1 − ε for a constant ε > 0. "Constant" = independent of the graph size, over an infinite family. Below: precise definitions, their equivalence, and completion of the analysis of the randomness-efficient error reduction of Section 7.5.

<a id="pdf-26d95080dbde-p025-b002"></a>
<!-- pdf-source: page=25; block=2; confidence=0.95 -->
### 7.B.1 The Algebraic Definition

**Definition 7.31 ((n,d,λ)-graphs).** If G is an n-vertex d-regular graph with λ(G) ≤ λ for some number λ < 1, then G is an (n,d,λ)-graph. A family {G_n}_{n∈ℕ} is an *expander graph family* if there are constants d ∈ ℕ and λ < 1 such that for every n, G_n is an (n,d,λ)-graph.

<a id="pdf-26d95080dbde-p025-b003"></a>
<!-- pdf-source: page=25; block=3; confidence=0.90 -->
**Explicit constructions.** A family {G_n} (indexed by n ∈ I) is *explicit* if a polynomial-time algorithm on input 1ⁿ outputs the adjacency matrix of G_n; *strongly explicit* if a polynomial-time algorithm on ⟨n, v, i⟩ (1 ≤ v ≤ n, 1 ≤ i ≤ d) outputs the i-th neighbor of v (time polynomial in the input length, polylogarithmic in n). Expander families exist by the probabilistic method (below), but explicit and strongly explicit constructions are what applications need.

<a id="pdf-26d95080dbde-p026-b001"></a>
<!-- pdf-source: page=26; block=1; confidence=0.88 -->
**Note 7.33 (Explicit construction of pseudorandom objects).** Recurring theme: random objects easily satisfy nice properties, but applications need *explicit* objects with efficient deterministic neighborhood computation. Explicit expander constructions turn out to yield a deterministic logspace algorithm for undirected connectivity. Another instance in Chapter 17 (error-correcting codes).

<a id="pdf-26d95080dbde-p026-b002"></a>
<!-- pdf-source: page=26; block=2; confidence=0.90 -->
The smallest possible λ for a d-regular n-vertex graph is Ω(1/√d); constructions meet (1 − o(1))·(2√(d−1))/d (*Ramanujan graphs*). For most CS applications any constant d, λ < 1 suffices. **Remark 7.32.** Constants are not crucial: λ can be made arbitrarily smaller at the expense of degree, since λ(G^T) = λ(G)^T where G^T (T-th matrix power) has an edge per length-T path: an (n,d,λ)-graph becomes an (n, d^T, λ^T)-graph. Chapter 16: the *replacement product* decreases degree at the expense of increasing λ (and vertex count).

<a id="pdf-26d95080dbde-p027-b001"></a>
<!-- pdf-source: page=27; block=1; confidence=0.93 -->
### 7.B.2 Combinatorial expansion and existence of expanders

**Definition 7.34 (Combinatorial (edge) expansion).** An n-vertex d-regular graph G = (V,E) is an (n,d,ρ)-*combinatorial expander* if for every S ⊆ V with |S| ≤ n/2, |E(S, S̄)| ≥ ρd|S|, where E(S,T) = {(s,t) ∈ E : s ∈ S, t ∈ T}. (Bigger ρ = better expansion; the term "expander" is used loosely for any (n,d,ρ) with ρ a positive constant. The draft's header carries a stray "([" — citation bracket glitch.)

<a id="pdf-26d95080dbde-p027-b002"></a>
<!-- pdf-source: page=27; block=2; confidence=0.93 -->
**Theorem 7.35 (Existence of expanders).** Let ε > 0 be a constant. Then there exist d = d(ε) and N ∈ ℕ such that for every n > N there exists an (n, d, 1−ε)-combinatorial expander. (Probabilistic method; Exercise 12 asks for a slightly weaker version.)

<a id="pdf-26d95080dbde-p027-b003"></a>
<!-- pdf-source: page=27; block=3; confidence=0.95 -->
**Theorem 7.36 (Combinatorial and algebraic expansion).** (1) If G is an (n,d,λ)-graph then it is an (n, d, (1−λ)/2)-combinatorial expander. (2) If G is an (n,d,ρ)-combinatorial expander then it is an (n, d, 1 − ρ²/2)-graph.

<a id="pdf-26d95080dbde-p027-b004"></a>
<!-- pdf-source: page=27; block=4; confidence=0.93 -->
**Lemma 7.37 (Expander Mixing Lemma).** Let G = (V,E) be an (n,d,λ)-graph and S, T ⊆ V. Then | |E(S,T)| − (d/n)|S||T| | ≤ λd√(|S||T|). **Proof.** Let 𝐬 be the indicator vector of S and 𝐭 of T ["the corresponding vector for the set S" is a draft typo — 𝐭 indicates T]; with 𝐬 as row vector, the statement is equivalent to |𝐬A𝐭 − |S||T|/n| ≤ λ√(|S||T|)  (2), where A is the normalized adjacency matrix. By Lemma 7.40, A = (1−λ)J + λC with J the all-(1/n) matrix and ‖C‖ ≤ 1. Then 𝐬A𝐭 = (1−λ)𝐬J𝐭 + λ𝐬C𝐭 ≤ |S||T|/n + λ√(|S||T|), using 𝐬J𝐭 = |S||T|/n and 𝐬C𝐭 = ⟨𝐬, C𝐭⟩ ≤ ‖𝐬‖₂‖𝐭‖₂ = √(|S||T|). ∎ (Part 1 of Theorem 7.36 follows by plugging T = S̄.)

<a id="pdf-26d95080dbde-p028-b001"></a>
<!-- pdf-source: page=28; block=1; confidence=0.90 -->
**Proof of second part of Theorem 7.36** (relaxed: constant 2 replaced by 8). G an (n,d,ρ)-combinatorial expander, A its normalized adjacency matrix, λ = λ(G); show λ ≤ 1 − ρ²/8. There is 𝐮 ⊥ **1** with A𝐮 = λ𝐮 (λ the second eigenvalue). Write 𝐮 = 𝐯 + 𝐰 where 𝐯 = 𝐮 on coordinates where 𝐮 > 0 (else 0) and 𝐰 = 𝐮 on coordinates where 𝐮 < 0 (else 0); both nonzero since 𝐮 ⊥ **1**; wlog 𝐮 nonzero on at most n/2 coordinates (else use −𝐮), i.e. 𝐯 supported on ≤ n/2 coordinates. From A𝐮 = λ𝐮, ⟨𝐯,𝐰⟩ = 0: ⟨A𝐯,𝐯⟩ + ⟨A𝐰,𝐯⟩ = ⟨A𝐮,𝐯⟩ = λ‖𝐯‖₂²; since ⟨A𝐰,𝐯⟩ ≤ 0, ⟨A𝐯,𝐯⟩/‖𝐯‖₂² ≥ λ, so 1 − λ ≥ 1 − ⟨A𝐯,𝐯⟩/‖𝐯‖₂² = (‖𝐯‖₂² − ⟨A𝐯,𝐯⟩)/‖𝐯‖₂² = Σ_{i,j}A_{i,j}(𝐯_i − 𝐯_j)²/(2‖𝐯‖₂²) (each row/column of A sums to 1). Multiply numerator and denominator by Σ_{i,j}A_{i,j}(𝐯_i² + 𝐯_j²); by generalized Cauchy–Schwarz (footnote: Σμ_i x_i y_i ≤ √(Σμ_i x_i²)(Σμ_i y_i²)): (Σ A_{i,j}(𝐯_i−𝐯_j)²)(Σ A_{i,j}(𝐯_i+𝐯_j)²) ≥ (Σ A_{i,j}(𝐯_i−𝐯_j)(𝐯_i+𝐯_j))² = (Σ A_{i,j}(𝐯_i²−𝐯_j²))². Using (a−b)(a+b) = a²−b² and Σ A_{i,j}(𝐯_i+𝐯_j)² = 2‖𝐯‖₂² + 2⟨A𝐯,𝐯⟩ ≤ 4‖𝐯‖₂² (matrix norm ≤ 1 gives ⟨A𝐯,𝐯⟩ ≤ ‖𝐯‖₂²): 1 − λ ≥ (Σ_{i,j}A_{i,j}(𝐯_i²−𝐯_j²))²/(8‖𝐯‖₂⁴). It remains to show Σ_{i,j}A_{i,j}(𝐯_i²−𝐯_j²) ≥ ρ‖𝐯‖₂²  (3).

<a id="pdf-26d95080dbde-p029-b001"></a>
<!-- pdf-source: page=29; block=1; confidence=0.90 -->
**Proof (end).** [Establishing (3):] sort 𝐯₁ ≥ 𝐯₂ ≥ … ≥ 𝐯_n (with 𝐯_i = 0 for i > n/2). Then Σ_{i,j}A_{i,j}(𝐯_i² − 𝐯_j²) ≥ Σ_{i=1}^{n/2} Σ_{j=i+1}^{n} A_{i,j}(𝐯_i² − 𝐯_{i+1}²) = Σ_{i=1}^{n/2} c_i(𝐯_i² − 𝐯_{i+1}²), where c_i = Σ_{j>i} A_{i,j} = (edges from {k : k ≤ i} to its complement)/d ≥ ρi by expansion (using 𝐯_i = 0 for i ≥ n/2). Hence Σ ≥ Σ_{i=1}^{n/2}(ρi𝐯_i² − ρ(i−1)𝐯_i²) = ρ‖𝐯‖₂². This gives 1 − λ ≥ ρ²‖𝐯‖₂⁴/(8‖𝐯‖₂⁴) = ρ²/8. ∎

<a id="pdf-26d95080dbde-p029-b002"></a>
<!-- pdf-source: page=29; block=2; confidence=0.92 -->
### 7.B.3 Error reduction using expanders

Completing Section 7.5's analysis. Procedure: N = 2^m, m = number of coins of the randomized algorithm; use m + O(k) coins to select a k-vertex random walk in expander G_N; output 1 iff the algorithm outputs 1 on at least one walk vertex used as coins. Need: if the algorithm outputs 1 on ≥ half the coins, the probability that all walk vertices land on coins where it outputs 0 is exponentially small in k. (Think of B below as the coins where the algorithm outputs 0.)

**Theorem 7.38 (Expander walks).** Let G be an (N,d,λ)-graph, B ⊆ [N] with |B| ≤ βN. Let X₁,…,X_k be random variables denoting a (k−1)-step random walk from X₁, where X₁ is chosen uniformly in [N]. Then Pr[∀_{1≤i≤k} X_i ∈ B]  (call this (∗))  ≤ ((1−λ)√β + λ)^{k−1}. (If λ and β are constants < 1, so is (1−λ)√β + λ.)

**Proof (start).** Let B_i be the event X_i ∈ B; (∗) = Pr[B₁]·Pr[B₂|B₁]⋯Pr[B_k|B₁,…,B_{k−1}]. Let 𝐩^i ∈ ℝ^N be the distribution of X_i conditioned on B₁,…,B_i. Let B̂ be the linear map (B̂𝐮)_j = 𝐮_j if j ∈ B, else 0. Then 𝐩¹ = (1/Pr[B₁]) B̂**1**.

<a id="pdf-26d95080dbde-p030-b001"></a>
<!-- pdf-source: page=30; block=1; confidence=0.90 -->
**Proof (cont.).** Similarly 𝐩² = (1/Pr[B₂|B₁])(1/Pr[B₁]) B̂AB̂**1** with A = A(G), and (∗) = |(B̂A)^{k−1} B̂**1**|₁. Bound via ‖(B̂A)^{k−1} B̂**1**‖₂ ≤ ((1−λ)√β + λ)^{k−1}/√N  (4), which suffices since |𝐯|₁ ≤ √N‖𝐯‖₂ (Note 7.24). **Definition 7.39 (Matrix Norm).** For an m×n matrix A, ‖A‖ is the maximum α [sic — minimum such bound / maximum of ‖A𝐯‖₂/‖𝐯‖₂] such that ‖A𝐯‖₂ ≤ α‖𝐯‖₂ for every 𝐯 ∈ ℝⁿ. A normalized adjacency matrix has ‖A‖ = 1; ‖A+B‖ ≤ ‖A‖+‖B‖ and ‖AB‖ ≤ ‖A‖‖B‖. **Lemma 7.40.** Let A be the normalized adjacency matrix of an (n,d,λ)-graph G, J the matrix with J_{i,j} = 1/n for all i,j. Then A = (1−λ)J + λC  (5), where ‖C‖ ≤ 1. (Interpretation: a step on an (n,d,λ)-graph is "like" going to the uniform distribution with probability 1−λ; not literally accurate — C may have negative entries — but good enough for the analysis.) **Proof.** C := (1/λ)(A − (1−λ)J). For 𝐯 = 𝐮 + 𝐰 (𝐮 = α**1**, 𝐰 ⊥ **1**): C𝐮 = (1/λ)(𝐮 − (1−λ)𝐮) = 𝐮 (A**1** = J**1** = **1**); with 𝐰′ = A𝐰, ‖𝐰′‖₂ ≤ λ‖𝐰‖₂ and J𝐰 = 0, so C𝐰 = (1/λ)𝐰′; ‖C𝐯‖₂² = ‖𝐮 + (1/λ)𝐰′‖₂² = ‖𝐮‖₂² + (1/λ²)‖𝐰′‖₂² ≤ ‖𝐮‖₂² + ‖𝐰‖₂² = ‖𝐯‖₂². ∎

<a id="pdf-26d95080dbde-p031-b001"></a>
<!-- pdf-source: page=31; block=1; confidence=0.90 -->
**Proof of Theorem 7.38 (end).** B̂A = B̂((1−λ)J + λC), so ‖B̂A‖ ≤ (1−λ)‖B̂J‖ + λ‖B̂C‖. J's output is always of the form α**1**, and B̂ keeps |B| of its N coordinates, so ‖B̂J‖ ≤ √β. B̂ merely zeros out coordinates, so ‖B̂‖ ≤ 1, giving ‖B̂C‖ ≤ 1. Thus ‖B̂A‖ ≤ (1−λ)√β + λ. Since B**1** [i.e. B̂**1**] has value 1/N in |B| places, ‖B̂**1**‖₂ = √β/√N, hence ‖(B̂A)^{k−1} B̂**1**‖₂ ≤ ((1−λ)√β + λ)^{k−1} √β/√N, establishing (4). ∎

<a id="pdf-26d95080dbde-p031-b002"></a>
<!-- pdf-source: page=31; block=2; confidence=0.92 -->
A similar procedure handles *two-sided error*: use the k sets of coins from a (k−1)-step random walk and decide by *majority*. The analysis rests on:

**Theorem 7.41 (Expander Chernoff Bound).** Let G be an (N,d,λ)-graph and B ⊆ [N] with |B| = βN. Let X₁,…,X_k be random variables denoting a (k−1)-step random walk in G (X₁ chosen uniformly). For i ∈ [k] define B_i = 1 if X_i ∈ B, else 0. Then, for every δ > 0, Pr[ |(Σ_{i=1}^k B_i)/k − β| > δ ] < 2e^{(1−λ)δ²k/60}. [Sic: as printed the exponent is positive, making the bound vacuous; the intended bound is 2e^{−(1−λ)δ²k/60} — the minus sign is missing in the draft. Proof omitted in the book.]

<a id="pdf-26d95080dbde-p033-b001"></a>
<!-- pdf-source: page=33; block=1; confidence=0.95 -->
[Page 32 is blank except headers. Page 33 begins Chapter 8 (Interactive proofs), outside the scope of this reference.]
