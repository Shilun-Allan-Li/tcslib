<!-- generated-by: maintainer ingest for EF-H12 (2026-11-19; ruling EF-H12-R4 A / Q-H12-2 A), transcribed from the scoped pypdf raw extraction and checked against page images -->
<!-- source-pdf-sha256: da0881782a35bde6a0779a2eb1a8d480f39fbddf70bbb92824d1dc5550a033b2 -->
<!-- validation-status: awaiting Codex source review -->

# Arora–Barak, Chapter 2: NP and NP completeness (authors' web draft)

**Source.** S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, the authors' public
web draft, downloaded on 2026-11-19 from <https://theory.cs.princeton.edu/complexity/book.pdf>
(489 pages; SHA-256 `da0881782a35bde6a0779a2eb1a8d480f39fbddf70bbb92824d1dc5550a033b2`; page
footers "Web draft 2007-01-08 21:59"). This file covers **PDF pages 55–80**, the whole of the
draft's Chapter 2 (Chapter 3 begins on PDF page 81). The PDF is not committed.

**Numbering.** This is the draft, **not** the Cambridge University Press 2009 edition that the
tag [AB09] names. Every chapter, section, definition, theorem, lemma, example, exercise and page
number below is the **draft's and may differ from the CUP 2009 edition**. Anchors use the
physical PDF page; the draft's printed page is the PDF page minus 16 (PDF p. 61 is printed
"p2.7 (45)"). Known differences from the numbers TCSlib cites are recorded in
`briefs/efficiency-gaps/wave1/EF-H12/ingest-report.md`; for example, the draft inserts a
Remark 2.11 after Theorem 2.10, so its Lemma 2.12 (SAT is NP-hard) and Lemma 2.15
(SAT ≤p 3SAT) are, by content, the lemmas TCSlib cites as [AB09, Lemma 2.11] and [AB09, Lemma 2.14].

**Form.** As in the chapter 7 and 13 ingests, definitions and statements are transcribed close to
the draft's wording (mathematics in Unicode, overbars written as ¬ or as an overline where the
draft has one); proofs, examples and discussion are condensed; exercises are summarised by
number. Bold block labels are the ingester's, and notes marked *Transcription note* are not part
of the source.

<a id="pdf-da0881782a35-p055-b001"></a>
<!-- pdf-source: page=55; block=1; confidence=0.93 -->
# Chapter 2: NP and NP completeness

_Epigraphs: Gödel's 1956 letter to von Neumann (if φ(n) ≈ Kn² — footnote: in modern terms, if SAT has a quadratic-time algorithm — the mathematician's effort on yes-or-no questions could be replaced by machines); Jack Edmonds, 1966 (conjecture that there is no good algorithm for the traveling salesman problem); Richard Karp, 1972 (theorems that suggest, but do not imply, that these problems will remain intractable)._

<a id="pdf-da0881782a35-p055-b002"></a>
<!-- pdf-source: page=55; block=2; confidence=0.92 -->
Introduction. Solving a problem from scratch differs from verifying a given solution. Chapter 1 introduced P (decision problems that can be efficiently solved); this chapter defines NP, which aims to capture problems whose solutions can be efficiently verified; the P versus NP question asks whether the two are the same (Section 2.7). The chapter also introduces NP-completeness: problems that are in P iff P = NP. Reductions and completeness motivate many later definitions.

<a id="pdf-da0881782a35-p056-b001"></a>
<!-- pdf-source: page=56; block=1; confidence=0.92 -->
## 2.1 The class NP

NP is the formal model of problems having efficiently verifiable solutions: a language is in NP if, given x and a polynomial-size solution certifying that x is a YES instance, the claim can be verified easily. Several equivalent definitions are given; the first is:

<a id="pdf-da0881782a35-p056-b002"></a>
<!-- pdf-source: page=56; block=2; confidence=0.97 -->
**Definition 2.1 (The class NP).** A language L ⊆ {0,1}* is in **NP** if there exists a polynomial p : ℕ → ℕ and a polynomial-time TM M such that for every x ∈ {0,1}*,

x ∈ L ⇔ ∃u ∈ {0,1}^{p(|x|)} s.t. M(x, u) = 1.

If x ∈ L and u ∈ {0,1}^{p(|x|)} satisfy M(x, u) = 1 then we call u a *certificate* for x (with respect to the language L and machine M). (Footnote 1: some texts use the term *witness* instead of certificate.)

<a id="pdf-da0881782a35-p056-b003"></a>
<!-- pdf-source: page=56; block=3; confidence=0.92 -->
**Example 2.2 (decision problems in NP).** Independent set (graph G and number k; is there a k-size independent subset of G's vertices? certificate: the k vertices). Traveling salesperson (n nodes, the C(n,2) distances d_{i,j}, number k; is there a closed tour visiting every node exactly once of total length ≤ k? certificate: the sequence of nodes). Subset sum (numbers A₁,…,A_n and T; does some subset sum to T? certificate: the subset). Linear programming (m linear inequalities with rational coefficients over u₁,…,u_n; is there a rational assignment satisfying all? certificate: the assignment). Integer programming (the same with integer assignments; certificate: the assignment).

<a id="pdf-da0881782a35-p057-b001"></a>
<!-- pdf-source: page=57; block=1; confidence=0.92 -->
**Example 2.2 (continued).** Graph isomorphism (two n×n adjacency matrices M₁, M₂; do they define the same graph up to renaming? certificate: the permutation π : [n] → [n]). Composite numbers (is N composite? certificate: the factorization). Factoring (N, L, U; does N have a factor M in [L, U]? certificate: M). Connectivity (graph G, vertices s, t; is s connected to t? certificate: the path).

<a id="pdf-da0881782a35-p057-b002"></a>
<!-- pdf-source: page=57; block=2; confidence=0.97 -->
### 2.1.1 Relation between NP and P

**Claim 2.3.** P ⊆ NP ⊆ ⋃_{c>1} DTIME(2^{n^c}).

<a id="pdf-da0881782a35-p057-b003"></a>
<!-- pdf-source: page=57; block=3; confidence=0.92 -->
**Proof (Claim 2.3).** (P ⊆ NP): if L ∈ P is decided in polynomial time by a TM N, take N as the machine M of Definition 2.1 and p the zero polynomial (u is the empty string). (NP ⊆ ⋃_{c>1} DTIME(2^{n^c})): with M, p as in Definition 2.1, decide L in time 2^{O(p(n))} by enumerating all u and using M to check each; accept iff some u is found. Since p(n) = O(n^c) for some c > 1, this runs in 2^{O(n^c)} time. ∎

<a id="pdf-da0881782a35-p057-b004"></a>
<!-- pdf-source: page=57; block=4; confidence=0.90 -->
No stronger relation between NP and deterministic time classes is known. Whether P = NP is the central open question of complexity theory (Section 2.7); most researchers believe P ≠ NP since years of effort have failed to yield efficient algorithms for certain NP languages.

<a id="pdf-da0881782a35-p057-b005"></a>
<!-- pdf-source: page=57; block=5; confidence=0.90 -->
**Example 2.4 (current knowledge on Example 2.2).** Connectivity, Composite Numbers and Linear Programming are in P: connectivity by breadth-first search [KT06, CLRS01]; composite numbers only recently, by Agrawal, Kayal and Saxena [?]; linear programming by Khachiyan's Ellipsoid algorithm [?] (faster algorithms follow Karmarkar's interior-point paradigm [?]).

<a id="pdf-da0881782a35-p058-b001"></a>
<!-- pdf-source: page=58; block=1; confidence=0.90 -->
**Example 2.4 (continued).** The rest are not known to be in P. Independent Set, Traveling Salesperson, Subset Sum and Integer Programming are NP-complete, so not in P unless P = NP. Graph Isomorphism and Factoring are not known to be either in P or NP-complete.

<a id="pdf-da0881782a35-p058-b002"></a>
<!-- pdf-source: page=58; block=2; confidence=0.92 -->
### 2.1.2 Non-deterministic Turing machines

NP can also be defined with non-deterministic TMs (NDTMs) — the original definition and the source of the name. An NDTM has two transition functions δ₀ and δ₁ and a special state q_accept; at each step it arbitrarily chooses which transition function to apply. M outputs 1 on x if some sequence of these choices (its *non-deterministic choices*) makes M reach q_accept on x; otherwise (every sequence makes M halt without reaching q_accept) M(x) = 0. M runs in T(n) time if for every input x and every sequence of non-deterministic choices M reaches the halting state or q_accept within T(|x|) steps.

<a id="pdf-da0881782a35-p058-b003"></a>
<!-- pdf-source: page=58; block=3; confidence=0.97 -->
**Definition 2.5.** For every function T : ℕ → ℕ and L ⊆ {0,1}*, we say that L ∈ **NTIME**(T(n)) if there is a constant c > 0 and a c·T(n)-time NDTM M such that for every x ∈ {0,1}*, x ∈ L ⇔ M(x) = 1.

<a id="pdf-da0881782a35-p058-b004"></a>
<!-- pdf-source: page=58; block=4; confidence=0.97 -->
**Theorem 2.6.** NP = ⋃_{c∈ℕ} NTIME(n^c). (The alternative definition of NP that appears in most texts.)

<a id="pdf-da0881782a35-p058-b005"></a>
<!-- pdf-source: page=58; block=5; confidence=0.90 -->
**Proof (Theorem 2.6), first part.** The non-deterministic choices of an accepting computation can serve as a certificate, and vice versa. If L is decided by an NDTM N running in time p(n), the sequence of choices that makes N reach q_accept on x has length p(|x|) and can be checked in polynomial time by a deterministic machine, so L ∈ NP by Definition 2.1. Conversely, if L ∈ NP by Definition 2.1, an NDTM N on input x non-deterministically writes a string u of length p(|x|) (δ₀ writes 0, δ₁ writes 1) and then runs the deterministic verifier M …

<a id="pdf-da0881782a35-p059-b001"></a>
<!-- pdf-source: page=59; block=1; confidence=0.92 -->
**Proof (Theorem 2.6), end.** … of Definition 2.1 to check that u is a valid certificate for x, entering q_accept if so. N enters q_accept on x iff a valid certificate exists; since p(n) = O(n^c) for some c > 1, L ∈ NTIME(n^c). ∎

<a id="pdf-da0881782a35-p059-b002"></a>
<!-- pdf-source: page=59; block=2; confidence=0.90 -->
NDTMs can be represented as strings and there is a universal NDTM (Exercise 1); using non-determinism the universal simulation can even be made slightly more efficient.

<a id="pdf-da0881782a35-p059-b003"></a>
<!-- pdf-source: page=59; block=3; confidence=0.92 -->
## 2.2 Reducibility and NP-completeness

The independent set problem is at least as hard as any other NP language: a polynomial-time algorithm for it would give one for every NP problem. This property is NP-hardness; since most scientists conjecture NP ≠ P, NP-hardness is evidence that a language cannot be decided in polynomial time. The crucial tool for comparing hardness is a reduction (Figure 2.1).

<a id="pdf-da0881782a35-p059-b004"></a>
<!-- pdf-source: page=59; block=4; confidence=0.97 -->
**Definition 2.7 (Reductions, NP-hardness and NP-completeness).** We say that a language A ⊆ {0,1}* is *polynomial-time Karp reducible* to a language B ⊆ {0,1}* (sometimes shortened to just "polynomial-time reducible"), denoted by A ≤p B, if there is a polynomial-time computable function f : {0,1}* → {0,1}* such that for every x ∈ {0,1}*, x ∈ A if and only if f(x) ∈ B.

We say that B is *NP-hard* if A ≤p B for every A ∈ NP. We say that B is *NP-complete* if B is NP-hard and B ∈ NP.

(Footnote 2: some texts call this notion "many-to-one reducibility" or "polynomial-time mapping reducibility".)

<a id="pdf-da0881782a35-p059-b005"></a>
<!-- pdf-source: page=59; block=5; confidence=0.88 -->
**Figure 2.1.** A Karp reduction from L to L′ is a polynomial-time function f that maps strings in L to strings in L′ and strings in L̄ = {0,1}* \ L to strings in L̄′. It transforms a polynomial-time TM M′ deciding L′ into a polynomial-time TM M for L by setting M(x) = M′(f(x)). *Transcription note:* the diagram itself (two Venn-style blobs and an algorithm box) is not transcribed; the raw text carries its labels as debris.

<a id="pdf-da0881782a35-p060-b001"></a>
<!-- pdf-source: page=60; block=1; confidence=0.90 -->
Properties of polynomial-time reductions: part 1 of the next theorem is transitivity (all later notions of reduction will also be transitive); part 2 explains the term NP-hard; part 3 explains NP-complete — to study P versus NP it suffices to study whether any NP-complete problem can be decided in polynomial time.

<a id="pdf-da0881782a35-p060-b002"></a>
<!-- pdf-source: page=60; block=2; confidence=0.97 -->
**Theorem 2.8.** 1. (Transitivity) If A ≤p B and B ≤p C, then A ≤p C. 2. If language A is NP-hard and A ∈ P then P = NP. 3. If language A is NP-complete then A ∈ P if and only if P = NP.

<a id="pdf-da0881782a35-p060-b003"></a>
<!-- pdf-source: page=60; block=3; confidence=0.92 -->
**Proof (Theorem 2.8).** The main observation: if p, q have polynomial growth, so does p(q(n)). Part 1 is proved, the others are left as simple exercises. If f₁ is a polynomial-time reduction from A to B and f₂ from B to C, then x ↦ f₂(f₁(x)) is a polynomial-time reduction from A to C: it takes polynomial time to compute, and f₂(f₁(x)) ∈ C iff x ∈ A. ∎

<a id="pdf-da0881782a35-p060-b004"></a>
<!-- pdf-source: page=60; block=4; confidence=0.95 -->
**Theorem 2.9.** The following language is NP-complete:

TMSAT = {⟨α, x, 1ⁿ, 1ᵗ⟩ : ∃u ∈ {0,1}ⁿ s.t. M_α outputs 1 on input ⟨x, u⟩ within t steps},

where M_α denotes the TM represented by the string α. (Footnote 3: 1ᵏ denotes the string of k ones; it is a common convention to give a polynomial TM such an input to allow it to run in time polynomial in k.)

<a id="pdf-da0881782a35-p060-b005"></a>
<!-- pdf-source: page=60; block=5; confidence=0.90 -->
The proof of Theorem 2.9 is straightforward once NP is internalised and is left as Exercise 2. TMSAT is not a very useful NP-complete problem: its definition is tied to Turing machines, so its NP-completeness gives little new insight.

<a id="pdf-da0881782a35-p060-b006"></a>
<!-- pdf-source: page=60; block=6; confidence=0.90 -->
## 2.3 The Cook-Levin Theorem: Computation is Local

Around 1971 Cook and Levin independently discovered NP-completeness and gave combinatorial NP-complete problems whose definitions seem to have nothing to do with Turing machines. Soon after, Karp showed that NP-completeness occurs widely; thousands of problems are now known to be NP-complete.

<a id="pdf-da0881782a35-p061-b001"></a>
<!-- pdf-source: page=61; block=1; confidence=0.96 -->
### 2.3.1 Boolean formulae and the CNF form

A Boolean formula over the variables u₁,…,u_n consists of the variables and the logical operators AND (∧), NOT (¬) and OR (∨) (Appendix A); e.g. (a ∧ b) ∨ (a ∧ c) ∨ (b ∧ c) is True iff the majority of a, b, c are True. If φ is a Boolean formula over u₁,…,u_n and z ∈ {0,1}ⁿ, then φ(z) denotes the value of φ when the variables are assigned the values z (1 identified with True, 0 with False). A formula φ is *satisfiable* if there exists some assignment z such that φ(z) is True; otherwise φ is *unsatisfiable*.

A Boolean formula over u₁,…,u_n is in *CNF form* (Conjunctive Normal Form) if it is an AND of OR's of variables or their negations; e.g. the 3CNF formula (u₁ ∨ ū₂ ∨ u₃) ∧ (u₂ ∨ ū₃ ∨ u₄) ∧ (ū₁ ∨ u₃ ∨ ū₄), where ū denotes the negation of u. In general a CNF formula has the form ⋀_i (⋁_j v_{ij}), where each v_{ij} is either a variable u_k or its negation ¬u_k. The terms v_{ij} are the *literals* of the formula and the terms (⋁_j v_{ij}) are its *clauses*. A *kCNF* is a CNF formula in which all clauses contain at most k literals.

<a id="pdf-da0881782a35-p061-b002"></a>
<!-- pdf-source: page=61; block=2; confidence=0.97 -->
### 2.3.2 The Cook-Levin Theorem

**Theorem 2.10 (Cook-Levin Theorem [Coo71, Lev73]).** Let SAT be the language of all satisfiable CNF formulae and 3SAT be the language of all satisfiable 3CNF formulae. Then, 1. SAT is NP-complete. 2. 3SAT is NP-complete.

<a id="pdf-da0881782a35-p061-b003"></a>
<!-- pdf-source: page=61; block=3; confidence=0.97 -->
**Remark 2.11.** An alternative proof of the Cook-Levin theorem, using the notion of Boolean circuits, is described in Section 6.7. *Transcription note:* the draft's Section 6.7 is ingested in `arora-barak-ch06-circuits.md` (anchor `pdf-da0881782a35-p128-b001` onward).

<a id="pdf-da0881782a35-p061-b004"></a>
<!-- pdf-source: page=61; block=4; confidence=0.92 -->
Both SAT and 3SAT are clearly in NP, since a satisfying assignment can serve as the certificate that a formula is satisfiable. So only NP-hardness needs proof: first SAT is shown NP-hard, then SAT is shown polynomial-time Karp reducible to 3SAT …

<a id="pdf-da0881782a35-p062-b001"></a>
<!-- pdf-source: page=62; block=1; confidence=0.92 -->
… which implies that 3SAT is NP-hard by transitivity of polynomial-time reductions. The following lemma is the key to the proof.

<a id="pdf-da0881782a35-p062-b002"></a>
<!-- pdf-source: page=62; block=2; confidence=0.97 -->
**Lemma 2.12.** SAT is NP-hard.

<a id="pdf-da0881782a35-p062-b003"></a>
<!-- pdf-source: page=62; block=3; confidence=0.90 -->
To prove this, every NP language L must be reduced to SAT: a polynomial-time transformation turning any x ∈ {0,1}* into a CNF formula φ_x such that x ∈ L iff φ_x is satisfiable. Since nothing is known about L except that it is in NP, the reduction must rely only on the definition of computation and express it with a Boolean formula.

<a id="pdf-da0881782a35-p062-b004"></a>
<!-- pdf-source: page=62; block=4; confidence=0.95 -->
### 2.3.3 Warmup: Expressiveness of boolean formulae

**Example 2.13.** The formula (a ∨ b̄) ∧ (ā ∨ b) is in CNF form; it is satisfied only by values of a, b that are equal. Thus (x₁ ∨ ȳ₁) ∧ (x̄₁ ∨ y₁) ∧ ⋯ ∧ (x_n ∨ ȳ_n) ∧ (x̄_n ∨ y_n) is True iff the strings x, y ∈ {0,1}ⁿ are equal. Though = is not a standard Boolean operator, it is used as shorthand: φ₁ = φ₂ is equivalent to (has the same satisfying assignments as) (φ₁ ∨ ¬φ₂) ∧ (¬φ₁ ∨ φ₂).

<a id="pdf-da0881782a35-p062-b005"></a>
<!-- pdf-source: page=62; block=5; confidence=0.97 -->
**Claim 2.14.** For every Boolean function f : {0,1}^ℓ → {0,1} there is an ℓ-variable CNF formula φ of size ℓ2^ℓ such that φ(u) = f(u) for every u ∈ {0,1}^ℓ, where the size of a CNF formula is defined to be the number of ∧/∨ symbols it contains. (Sometimes known as *universality* of AND, OR and NOT.)

<a id="pdf-da0881782a35-p062-b006"></a>
<!-- pdf-source: page=62; block=6; confidence=0.93 -->
**Proof sketch (Claim 2.14).** For every v ∈ {0,1}^ℓ there is a clause C_v with C_v(v) = 0 and C_v(u) = 1 for every u ≠ v; e.g. for v = ⟨1,1,0,1⟩ the clause is ū₁ ∨ ū₂ ∨ u₃ ∨ ū₄. Let φ be the AND of the clauses C_v for all v with f(v) = 0 (size at most ℓ2^ℓ). If f(u) = 0 then C_u(u) = 0, so φ(u) = 0; if f(u) = 1 then C_v(u) = 1 for every v with f(v) = 0, so φ(u) = 1. Hence φ(u) = f(u) for every u. ∎

<a id="pdf-da0881782a35-p062-b007"></a>
<!-- pdf-source: page=62; block=7; confidence=0.92 -->
In this chapter Claim 2.14 is used only when the number of variables is some fixed constant.

<a id="pdf-da0881782a35-p063-b001"></a>
<!-- pdf-source: page=63; block=1; confidence=0.92 -->
### 2.3.4 Proof of Lemma 2.12

Let L be an NP language and M the polynomial-time TM such that for every x ∈ {0,1}*, x ∈ L ⇔ M(x, u) = 1 for some u ∈ {0,1}^{p(|x|)}, p a polynomial. L is shown polynomial-time Karp reducible to SAT by transforming, in polynomial time, every x into a CNF formula φ_x with x ∈ L iff φ_x is satisfiable. By Claim 2.14 the map u ↦ M(x, u) is a CNF ψ_x, but of size up to p(|x|)2^{p(|x|)}; a smaller formula uses that M runs in polynomial time and that each TM step is highly local.

<a id="pdf-da0881782a35-p063-b002"></a>
<!-- pdf-source: page=63; block=2; confidence=0.90 -->
Simplifying assumptions: (1) M has only two tapes, an input tape and a work/output tape; (2) M is *oblivious* — its head movement does not depend on the contents of its input, so its running time is the same for all inputs of size n and the head locations at step i depend only on i and the input length. These are without loss of generality: every T(n)-time TM has a two-tape oblivious equivalent running in O(T(n)²) time (Remark 1.10, Exercise 8 of Chapter 1; footnote 4: even O(T(n) log T(n)) with more tapes, Exercise 9 of Chapter 1, and the proof generalises). So for L ∈ NP there is a two-tape oblivious polynomial-time M and a polynomial p with x ∈ L ⇔ ∃u ∈ {0,1}^{p(|x|)} s.t. M(x, u) = 1.

<a id="pdf-da0881782a35-p063-b003"></a>
<!-- pdf-source: page=63; block=3; confidence=0.90 -->
Because M is oblivious, for each input length there are functions inputpos(i) (the input-head location at step i) and prev(i) (the last step before i at which M visited the same work-tape location; footnote 5: prev(i) = 1 if step i is the first visit), computable in polynomial time by simulating M on, say, the all-zeroes input (Figure 2.3).

<a id="pdf-da0881782a35-p063-b004"></a>
<!-- pdf-source: page=63; block=4; confidence=0.88 -->
With Q the state set and Γ the alphabet, the *snapshot* of M's execution on input y at step i is the triple ⟨a, b, q⟩ ∈ Γ × Γ × Q of the symbols read by the two heads and the current state (Figure 2.2). The snapshot at step i depends on the state at step i − 1 and the contents of the current input and work cells: z_i = F(z_{i−1}, z_{prev(i)}, y_{inputpos(i)}), where z_i encodes the i-th snapshot as a binary string of some length c and F is a function derived from M's transition function …

<a id="pdf-da0881782a35-p064-b001"></a>
<!-- pdf-source: page=64; block=1; confidence=0.85 -->
**Figure 2.2.** A snapshot of a TM contains the current state and the symbols read at a particular step: if at step i M reads 0, 1 from its tapes and is in state q₇, its snapshot is ⟨0, 1, q₇⟩. (Diagram of input tape, work/output tape and state register not transcribed.)

<a id="pdf-da0881782a35-p064-b002"></a>
<!-- pdf-source: page=64; block=2; confidence=0.88 -->
… F maps {0,1}^{2c+1} to {0,1}^c (c is a constant depending only on M's state and alphabet size, independent of the input size). **Figure 2.3.** The snapshot of M at step i depends on its previous state (in the snapshot of step i − 1) and on the symbols read from the input tape at position inputpos(i) and from the work tape, last written at step prev(i). (Diagram not transcribed.)

<a id="pdf-da0881782a35-p064-b003"></a>
<!-- pdf-source: page=64; block=3; confidence=0.92 -->
Let n ∈ ℕ and x ∈ {0,1}ⁿ; a CNF φ_x with x ∈ L ⇔ φ_x ∈ SAT is needed. x ∈ L iff some u ∈ {0,1}^{p(n)} has M(y) = 1 for y = x ∘ u (∘ is concatenation). Since the snapshot sequence determines the outcome, this holds iff there exist y ∈ {0,1}^{n+p(n)} and z₁,…,z_T ∈ {0,1}^c (T = T(n) the number of steps of M on inputs of length n + p(n)) satisfying: 1. the first n bits of y equal x; 2. z₁ encodes the initial snapshot ⟨▷, □, q_start⟩ (start symbol of the input tape, blank symbol, initial state) …

<a id="pdf-da0881782a35-p065-b001"></a>
<!-- pdf-source: page=65; block=1; confidence=0.92 -->
… 3. for every i ∈ {2,…,T}, z_i = F(z_{i−1}, z_{inputpos(i)}, z_{prev(i)}); 4. the last string z_T encodes a snapshot in which the machine halts and outputs 1. φ_x takes variables y ∈ {0,1}^{n+p(n)} and z ∈ {0,1}^{cT} and checks the AND of the four conditions, so x ∈ L ⇔ φ_x ∈ SAT. Condition 1 is a CNF of size 4n (Example 2.13); conditions 2 and 4 depend on c variables each, hence CNFs of size c2^c by Claim 2.14; condition 3 is an AND of T conditions each on at most 3c + 1 variables, hence a CNF of size at most T(3c+1)2^{3c+1}. The whole is a CNF of size d(n + T), d a constant depending only on M, computable in time polynomial in the running time of M. ∎ *Transcription note:* condition 3 as printed reads z_{inputpos(i)} where p. 63 has y_{inputpos(i)} (the input bit), and the argument order differs from p. 63; the p. 63 form is the intended one.

<a id="pdf-da0881782a35-p065-b002"></a>
<!-- pdf-source: page=65; block=2; confidence=0.97 -->
### 2.3.5 Reducing SAT to 3SAT

Since SAT and 3SAT are clearly in NP, Lemma 2.12 completes the proof that SAT is NP-complete; all that is left for Theorem 2.10 is:

**Lemma 2.15.** SAT ≤p 3SAT.

<a id="pdf-da0881782a35-p065-b003"></a>
<!-- pdf-source: page=65; block=3; confidence=0.94 -->
**Proof (Lemma 2.15).** Map a CNF φ to a 3CNF ψ with ψ satisfiable iff φ is. For a 4CNF, take a clause C = u₁ ∨ ū₂ ∨ ū₃ ∨ u₄, add a new variable z and replace C by C₁ = u₁ ∨ ū₂ ∨ z and C₂ = ū₃ ∨ u₄ ∨ z̄. If C is true some value of z satisfies both C₁ and C₂; if C is false, every value of z falsifies C₁ or C₂. In general a clause C of size k > 3 becomes an equivalent pair, C₁ of size k − 1 and C₂ of size 3, over the k variables of C and a new auxiliary variable z; applying this repeatedly is a polynomial-time transformation of φ into an equivalent 3CNF ψ. ∎

<a id="pdf-da0881782a35-p065-b004"></a>
<!-- pdf-source: page=65; block=4; confidence=0.92 -->
### 2.3.6 More thoughts on the Cook-Levin theorem

The Cook-Levin theorem is an example of the power of abstraction: it holds whether the model is the C programming language or the Turing machine, but may have been considerably harder to discover in the former. The proof actually yields a result a bit stronger than the theorem's statement:

<a id="pdf-da0881782a35-p066-b001"></a>
<!-- pdf-source: page=66; block=1; confidence=0.95 -->
1. If we use the efficient simulation of a standard TM by an oblivious TM (see Exercise 9, Chapter 1) then for every x ∈ {0,1}*, the size of the formula φ_x (and the time to compute it) is O(T log T), where T is the number of steps the machine M takes on input x (see Exercise 10).

<a id="pdf-da0881782a35-p066-b002"></a>
<!-- pdf-source: page=66; block=2; confidence=0.97 -->
**Levin reductions and parsimonious reductions (§2.3.6, item 2).** 2. The reduction f from an NP-language L to SAT presented in Lemma 2.12 not only satisfied that x ∈ L ⇔ f(x) ∈ SAT but actually the proof yields an efficient way to transform a certificate for x to a satisfying assignment for f(x) and vice versa. We call a reduction with this property a *Levin* reduction. One can also verify that the proof supplied a one-to-one and onto map between the set of certificates for x and the set of satisfying assignments for f(x), implying that they are of the same size. A reduction with this property is called *parsimonious*. Most of the known NP-complete problems (including all the ones mentioned in this chapter) have parsimonious Levin reductions from all the NP languages (see Exercise 11). As we will see in this book, this fact is sometimes useful for certain applications.

<a id="pdf-da0881782a35-p066-b003"></a>
<!-- pdf-source: page=66; block=3; confidence=0.90 -->
**Why 3SAT?** Why is 3SAT's NP-completeness more interesting than that of TMSAT (Theorem 2.9)? 3SAT has very minimal combinatorial structure and is easy to use in reductions; propositional logic has a central historical role in logic (a reason Cook and Levin were interested in it); and it is a simple example of *constraint satisfaction problems*, ubiquitous in fields including artificial intelligence.

<a id="pdf-da0881782a35-p066-b004"></a>
<!-- pdf-source: page=66; block=4; confidence=0.90 -->
## 2.4 The web of reductions

Cook and Levin had to reduce every NP language to SAT; to prove another language L NP-complete it suffices to reduce SAT or 3SAT to L, and then L to further languages L′. This "web of reductions" shows thousands of languages NP-complete. A few are shown here, more in the exercises (Figure 2.4); see the classic book by Garey and Johnson [GJ79] and the Internet site [?].

<a id="pdf-da0881782a35-p066-b005"></a>
<!-- pdf-source: page=66; block=5; confidence=0.97 -->
**Theorem 2.16 (Independent set is NP-complete).** Let INDSET = {⟨G, k⟩ : G has independent set of size k}. Then INDSET is NP-complete.

<a id="pdf-da0881782a35-p066-b006"></a>
<!-- pdf-source: page=66; block=6; confidence=0.90 -->
**Proof (Theorem 2.16), first part.** INDSET is clearly in NP; reduce 3SAT to INDSET. For a 3CNF φ on n variables with m clauses, G has 7m vertices: a cluster of 7 vertices per clause C, one for each of the 7 partial assignments to C's three variables that satisfy C (for C = ū₂ ∨ ū₅ ∨ ū₇, the cluster …

<a id="pdf-da0881782a35-p067-b001"></a>
<!-- pdf-source: page=67; block=1; confidence=0.80 -->
**Figure 2.4.** Web of reductions between the NP-completeness problems described in this chapter and the exercises (thousands more are known). Edges as drawn: ∀L ∈ NP → SAT (Theorem 2.10 (Lemma 2.12)); SAT → 3SAT (Theorem 2.10 (Lemma 2.15)); SAT → INTEGERPROG (Theorem 2.17); SAT → dHAMPATH (Theorem 2.18); SAT → THEOREMS (Ex 6); SAT → QUADEQ (Ex 18); dHAMPATH → HAMPATH (Ex 17); HAMPATH → TSP and HAMCYCLE (Ex 17); 3SAT → INDSET (Theorem 2.16); 3SAT → Exactone3SAT (Ex 16) → SUBSETSUM (Ex 16); INDSET → CLIQUE and VERTEXCOVER (Ex 14); VERTEXCOVER → MAXCUT (Ex 15). *Transcription note:* the arrows are read from the page image; the text layer carries only the labels.

<a id="pdf-da0881782a35-p068-b001"></a>
<!-- pdf-source: page=68; block=1; confidence=0.88 -->
**Proof (Theorem 2.16), continued.** … corresponds to all partial assignments u₂ = a, u₅ = b, u₇ = c with ⟨a,b,c⟩ ≠ ⟨1,1,1⟩; if C has fewer than three variables, some partial assignment is repeated). Edges join vertices with inconsistent partial assignments (giving different values to a shared variable) and every two vertices in the same cluster. The map is polynomial-time. If u satisfies φ, choose in each cluster the vertex for the restriction of u: no two are inconsistent, giving an independent set of size m. Conversely, from an independent set S of size m set u_i = a if some vertex of S gives u_i the value a and u_i = 0 otherwise; this is well defined since S is independent, and S has exactly one vertex per cluster (clusters are cliques), so u satisfies every clause. ∎ *Transcription note:* the draft first says "G has a clique of size m" and then argues with an independent set; the independent set is the intended statement; the example partial assignment is printed as "u₁ = a, u₂ = b, u₃ = c".

<a id="pdf-da0881782a35-p068-b002"></a>
<!-- pdf-source: page=68; block=2; confidence=0.88 -->
So the answer to P vs. NP depends on whether one can efficiently plan an optimal dinner party. More NP-completeness results follow.

<a id="pdf-da0881782a35-p068-b003"></a>
<!-- pdf-source: page=68; block=3; confidence=0.96 -->
**Theorem 2.17 (Integer programming is NP-complete).** A set of linear inequalities with rational coefficients over variables u₁,…,u_n is in IPROG if there is an assignment of integer numbers in {0, 1, 2, …} to u₁,…,u_n that satisfies it. Then, IPROG is NP-complete.

<a id="pdf-da0881782a35-p068-b004"></a>
<!-- pdf-source: page=68; block=4; confidence=0.92 -->
**Proof (Theorem 2.17).** IPROG is clearly in NP. To reduce SAT to IPROG: add 0 ≤ u_i ≤ 1 for every i, then express every clause as an inequality, e.g. u₁ ∨ ū₂ ∨ ū₃ as u₁ + (1 − u₂) + (1 − u₃) ≥ 1. ∎

<a id="pdf-da0881782a35-p068-b005"></a>
<!-- pdf-source: page=68; block=5; confidence=0.96 -->
**Theorem 2.18 (Hamiltonian path is NP-complete).** Let dHAMPATH denote the set of all directed graphs that contain a path visiting all of their vertices exactly once. Then dHAMPATH is NP-complete.

<a id="pdf-da0881782a35-p068-b006"></a>
<!-- pdf-source: page=68; block=6; confidence=0.90 -->
**Proof (Theorem 2.18), first part.** dHAMPATH is clearly in NP. Map every CNF φ to a graph G such that φ is satisfiable iff G has a Hamiltonian path (a path visiting all of G's vertices exactly once).

<a id="pdf-da0881782a35-p069-b001"></a>
<!-- pdf-source: page=69; block=1; confidence=0.85 -->
**Figure 2.5.** Reducing SAT to dHAMPATH. A formula with n variables and m clauses maps to a graph with m clause vertices and n doubly linked chains of length 6m, one per variable; traversing a chain left to right sets the variable True, right to left False. Every Hamiltonian path taking the edge from u to the clause vertex c₁₀ (the figure's example clause c₁₀ = u₁ OR ū₂ OR ū₃; c₁₀ can be visited if chain 1 is traversed left to right or chains 2 or 3 right to left) must immediately take the edge from c₁₀ to v, as otherwise it would get "stuck" the next time it visits v. (Diagram not transcribed.)

<a id="pdf-da0881782a35-p069-b002"></a>
<!-- pdf-source: page=69; block=2; confidence=0.90 -->
**Proof (Theorem 2.18), construction.** G has (1) a vertex for each clause c₁,…,c_m, (2) a start vertex v_start and an end vertex v_end, (3) n chains of 6m vertices v₁,…,v_{6m}, with v_i and v_{i+1} joined by edges in both directions. Edges go from v_start to the two extreme points of the first chain, from the extreme points of chain j to those of chain j + 1 (j ∈ [n − 1]), and from the extreme points of chain n to v_end. For each clause C: if C contains u_j, pick neighbouring v_i, v_{i+1} on chain j and add edges v_i → C and C → v_{i+1}; if C contains ū_j, add them in the opposite direction (v_{i+1} → C, C → v_i). Links are never reused and an unused link is kept between used links (6m vertices suffice).

<a id="pdf-da0881782a35-p069-b003"></a>
<!-- pdf-source: page=69; block=3; confidence=0.90 -->
(φ ∈ SAT ⇒ G ∈ dHAMPATH.) For a satisfying u, start at v_start, traverse chain j left to right if u_j = 1 and right to left if u_j = 0, end at v_end; for each clause C use one link on the chain of a true literal of C to detour through v_C.

<a id="pdf-da0881782a35-p070-b001"></a>
<!-- pdf-source: page=70; block=1; confidence=0.90 -->
(G ∈ dHAMPATH ⇒ φ ∈ SAT.) A Hamiltonian path P must start at v_start (no incoming edges) and end at v_end (no outgoing edges), and must traverse the chains in order, each entirely left to right or right to left: if P takes u → w with u on a chain and w a clause vertex, it must next take w → v with v adjacent to u in the link, or it gets stuck the next time it visits v (the draft refers to "Figure 2.1" here; Figure 2.5 is meant). Set u_j = 1 iff P traverses chain j left to right; since P visits every clause vertex, u satisfies φ. ∎

<a id="pdf-da0881782a35-p070-b002"></a>
<!-- pdf-source: page=70; block=2; confidence=0.88 -->
**In praise of reductions.** Polynomial-time reductions (with their cousin, the randomized polynomial-time reduction of Section 7.9) have led to rich understanding beyond NP-completeness; much of complexity theory and cryptography consists of reductions connecting disparate conjectures. A possible explanation of why complexity theorists excel at reductions but not lower bounds: humans are more adept at algorithms (a reduction is an algorithm) than at lower bounds on Turing machines.

<a id="pdf-da0881782a35-p070-b003"></a>
<!-- pdf-source: page=70; block=3; confidence=0.88 -->
**Coping with NP hardness.** NP-complete problems arise widely (flight scheduling, genome sequencing). NP-completeness only means (assuming P ≠ NP) no algorithm solves the problem exactly on every input; approximate solutions on some inputs may suffice. Example: TSP. One need not solve all possible distance lists — e.g. cities as points in the plane with Euclidean distances (not every distance list arises this way) …

<a id="pdf-da0881782a35-p071-b001"></a>
<!-- pdf-source: page=71; block=1; confidence=0.88 -->
… and a tour within 1% of optimal may be good enough. Neither observation alone makes TSP tractable: TSP is NP-complete even for Euclidean distances, and if P ≠ NP it is hard to approximate within any constant factor. Together they help: for every ε there is a poly(n(log n)^{O(1/ε)})-time algorithm giving a tour at most (1 + ε) times optimal for Euclidean instances [Aro98]. NP-completeness indicates that more careful modelling is needed; Chapters 15 and 18 explore average-case complexity and approximation algorithms.

<a id="pdf-da0881782a35-p071-b002"></a>
<!-- pdf-source: page=71; block=2; confidence=0.90 -->
## 2.5 Decision versus search

NP is defined with Yes/No problems rather than search problems ("find a satisfying assignment if one exists"). Search is harder than decision, so if P ≠ NP neither can be solved for an NP-complete problem; but for NP-complete problems they are equivalent: if the decision problem is solvable (so P = NP), the search version of every NP problem is solvable in polynomial time.

<a id="pdf-da0881782a35-p071-b003"></a>
<!-- pdf-source: page=71; block=3; confidence=0.95 -->
**Theorem 2.19.** Suppose that P = NP. Then, for every NP language L there exists a polynomial-time TM B that on input x ∈ L outputs a certificate for x. That is, if, as per Definition 2.1, x ∈ L iff ∃u ∈ {0,1}^{p(|x|)} s.t. M(x, u) = 1 where p is some polynomial and M is a polynomial-time TM, then on input x ∈ L, B(x) will be a string u ∈ {0,1}^{p(|x|)} satisfying M(x, B(x)) = 1. *Transcription note:* the text layer renders "x ∈ L" in the first sentence with a glyph artefact ("/suppress"); the page image reads x ∈ L.

<a id="pdf-da0881782a35-p071-b004"></a>
<!-- pdf-source: page=71; block=4; confidence=0.90 -->
**Proof (Theorem 2.19), SAT case.** Given an algorithm A deciding SAT, an algorithm B finds a satisfying assignment of a satisfiable n-variable CNF φ with 2n + 1 calls to A plus polynomial-time work: check φ satisfiable; substitute x₁ = 0 and x₁ = 1 (a polynomial-time simplification leaving n − 1 variables) and use A to find a satisfiable choice; fix it and continue. After n variables every intermediate formula is satisfiable, so the final assignment satisfies φ.

<a id="pdf-da0881782a35-p072-b001"></a>
<!-- pdf-source: page=72; block=1; confidence=0.95 -->
**Proof (Theorem 2.19), general L.** To solve the search problem for an arbitrary NP-language L, we use the fact that the reduction of Theorem 2.10 from L to SAT is actually a *Levin* reduction. This means that we have a polynomial-time computable function f such that not only x ∈ L ⇔ f(x) ∈ SAT but actually we can map a satisfying assignment of f(x) into a certificate for x. Therefore, we can use the algorithm above to come up with an assignment for f(x) and then map it back into a certificate for x. ∎

<a id="pdf-da0881782a35-p072-b002"></a>
<!-- pdf-source: page=72; block=2; confidence=0.93 -->
**Remark 2.20.** The proof above shows that SAT is *downward self-reducible*: given an algorithm solving SAT on inputs of length smaller than n we can solve SAT on inputs of length n. Using the Cook-Levin reduction one can show all NP-complete problems have a similar property (not made formal).

<a id="pdf-da0881782a35-p072-b003"></a>
<!-- pdf-source: page=72; block=3; confidence=0.90 -->
## 2.6 coNP, EXP and NEXP

Related complexity classes very relevant to the P versus NP question.

<a id="pdf-da0881782a35-p072-b004"></a>
<!-- pdf-source: page=72; block=4; confidence=0.94 -->
### 2.6.1 coNP

If L ⊆ {0,1}* is a language, L̄ denotes the *complement* of L: L̄ = {0,1}* \ L.

**Definition 2.21.** coNP = {L : L̄ ∈ P}. *Transcription note:* so printed in the draft; the intended definition is {L : L̄ ∈ NP}, as the following discussion and Definition 2.22 show.

<a id="pdf-da0881782a35-p072-b005"></a>
<!-- pdf-source: page=72; block=5; confidence=0.90 -->
coNP is *not* the complement of NP: every language in P is in NP ∩ coNP (Exercise 19). Example: the complement of SAT, {φ : φ is not satisfiable}, is in coNP. A common mistaken NDTM for it (guess an assignment, accept if it does not satisfy φ) accepts every formula with a single unsatisfying assignment. Hence the following equivalent definition (Exercise 20) is preferred.

<a id="pdf-da0881782a35-p072-b006"></a>
<!-- pdf-source: page=72; block=6; confidence=0.97 -->
**Definition 2.22 (coNP, alternative definition).** For every L ⊆ {0,1}*, we say that L ∈ coNP if there exists a polynomial p : ℕ → ℕ and a polynomial-time TM M such that for every x ∈ {0,1}*, x ∈ L ⇔ ∀u ∈ {0,1}^{p(|x|)} s.t. M(x, u) = 1. (The key is "∀" where Definition 2.1 used ∃.)

<a id="pdf-da0881782a35-p072-b007"></a>
<!-- pdf-source: page=72; block=7; confidence=0.92 -->
A language is *coNP-complete* if it is in coNP and every coNP language is polynomial-time Karp reducible to it.

<a id="pdf-da0881782a35-p073-b001"></a>
<!-- pdf-source: page=73; block=1; confidence=0.92 -->
**Example 2.23.** TAUTOLOGY = {φ : φ is a Boolean formula that is satisfied by every assignment} is coNP-complete. It is in coNP by Definition 2.22; for L ∈ coNP, modify the Cook-Levin reduction from L̄ (in NP) to SAT: it gives φ_x satisfiable iff x ∈ L̄, and ¬φ_x ∈ TAUTOLOGY iff x ∈ L.

<a id="pdf-da0881782a35-p073-b002"></a>
<!-- pdf-source: page=73; block=2; confidence=0.90 -->
If P = NP then NP = coNP = P (simple exercise); so NP ≠ coNP would imply P ≠ NP. Most researchers believe NP ≠ coNP: it seems hard to believe there is a short certificate that a formula is a TAUTOLOGY.

<a id="pdf-da0881782a35-p073-b003"></a>
<!-- pdf-source: page=73; block=3; confidence=0.96 -->
### 2.6.2 EXP and NEXP

**Definition 2.24.** EXP = ⋃_{c≥0} DTIME(2^{n^c}). NEXP = ⋃_{c≥0} NTIME(2^{n^c}).

<a id="pdf-da0881782a35-p073-b004"></a>
<!-- pdf-source: page=73; block=4; confidence=0.90 -->
By brute-force search for the certificate, P ⊆ NP ⊆ EXP ⊆ NEXP. Studying exponential classes is motivated by results such as:

<a id="pdf-da0881782a35-p073-b005"></a>
<!-- pdf-source: page=73; block=5; confidence=0.97 -->
**Theorem 2.25.** If EXP ≠ NEXP then P ≠ NP.

<a id="pdf-da0881782a35-p073-b006"></a>
<!-- pdf-source: page=73; block=6; confidence=0.92 -->
**Proof (Theorem 2.25).** Contrapositive: assume P = NP. Let L ∈ NTIME(2^{n^c}) be decided by an NDTM M. Then L_pad = {⟨x, 1^{2^{|x|^c}}⟩ : x ∈ L} (1) is in NP: on y, check y = ⟨z, 1^{2^{|z|^c}}⟩ (else reject) and run M on z for 2^{|z|^c} steps — polynomial in |y|. So L_pad ∈ P, and then L ∈ EXP: pad x and run the polynomial-time machine for L_pad. ∎

<a id="pdf-da0881782a35-p074-b001"></a>
<!-- pdf-source: page=74; block=1; confidence=0.92 -->
**Remark 2.26.** The *padding* technique (padding every string of a language with useless symbols) is used in several other results: equalities between complexity classes "scale up" (if two resources solve the same problems within bound T(n), the same holds for larger T′), and, contrapositively, inequalities "scale down". Most classes studied later are also contained in EXP and NEXP.

<a id="pdf-da0881782a35-p074-b002"></a>
<!-- pdf-source: page=74; block=2; confidence=0.88 -->
## 2.7 More thoughts about P, NP, and all that

### 2.7.1 The philosophical importance of NP

Abstractly, P vs. NP asks about the power of nondeterminism for Turing machines (answered for simpler models such as finite automata). The certificate definition shows it captures a widespread phenomenon: recognising a correct answer is often easier than finding it (appreciating vs. composing a Beethoven sonata; checking vs. designing a suspension bridge; verifying vs. finding a proof, as in Gödel's letter). Finding answers seems to involve exhaustive search over an exponentially large set; P vs. NP asks whether it can be avoided in general — intuitively obvious, but turning this into a proof has proved difficult.

<a id="pdf-da0881782a35-p074-b003"></a>
<!-- pdf-source: page=74; block=3; confidence=0.90 -->
### 2.7.2 NP and mathematical proofs

NP is the set of languages whose membership has a short certificate, reminiscent of a mathematical proof. Mathematics can in principle be axiomatised; for most known systems (Peano arithmetic, ZF set theory) proof verification runs in time polynomial in the proof length, so for any usual axiomatic system A the problem theorems = {(φ, 1ⁿ) : φ has a formal proof of length ≤ n in system A} is in NP.

<a id="pdf-da0881782a35-p075-b001"></a>
<!-- pdf-source: page=75; block=1; confidence=0.88 -->
The exercises ask to prove this problem NP-complete; so P vs. NP rephrases Gödel's question whether proofs can be found in time polynomial in their length. Students believe intuitively that P ≠ NP.

<a id="pdf-da0881782a35-p075-b002"></a>
<!-- pdf-source: page=75; block=2; confidence=0.86 -->
### 2.7.3 What if P = NP?

If an NP-complete problem like 3SAT had a very efficient (say O(n²)) algorithm, the world would be mostly a Utopia: theorem-discovering programs, efficiently findable answers and certificates for every efficiently verifiable search problem, perfect AI search, optimal part and circuit design, automatically obtained simplest theories explaining data (Occam's Razor) — consequences of the Polynomial Hierarchy study of Chapter 5. This Utopia would need no randomness (Chapter 7), but would have no privacy: every encryption scheme would have a trivial decoding algorithm (no digital cash, SSL, RSA or PGP; Chapter 10). That it cannot be ruled out shows how little is known about computation.

<a id="pdf-da0881782a35-p075-b003"></a>
<!-- pdf-source: page=75; block=3; confidence=0.86 -->
### 2.7.4 What if NP = coNP?

Consequences would still seem dramatic, mostly short certificates for statements that seem to have none. Example: deciding whether a system of multivariate polynomials has a common root …

<a id="pdf-da0881782a35-p076-b001"></a>
<!-- pdf-source: page=76; block=1; confidence=0.86 -->
… i.e. whether f₁(x₁,…,x_n) = 0, …, f_m(x₁,…,x_n) = 0 has a solution, each f_i quadratic. A solution is a certificate (after showing it has a polynomial-size description, omitted); infeasibility is in coNP. Hilbert's Nullstellensatz says the system is infeasible iff there are polynomials g₁,…,g_m with Σ_i f_i g_i = 1, but the degrees of the g_i (hence their bit size) may be exponential in n, m (and sometimes must be). If NP = coNP there would be some other short certificate of infeasibility, with an effect on mathematics probably greater than the Nullstellensatz; any other coNP problem could replace it in this discussion.

<a id="pdf-da0881782a35-p076-b002"></a>
<!-- pdf-source: page=76; block=2; confidence=0.90 -->
**What have we learned?** NP consists of the languages whose membership can be certified to a polynomial-time algorithm; it contains many important problems not known to be in P, and can also be defined with non-deterministic TMs. NP-complete problems are the hardest in NP: they have polynomial-time algorithms iff P = NP; many natural ones, e.g. 3SAT, seem to have nothing to do with Turing machines. If P = NP then every efficiently verifiable search problem is efficiently solvable from scratch.

<a id="pdf-da0881782a35-p076-b003"></a>
<!-- pdf-source: page=76; block=3; confidence=0.86 -->
**Chapter notes and history (start).** In the 1950s Soviet scientists, aware of the undesirability of exhaustive ("perebor") search, asked whether certain problems inherently require it …

<a id="pdf-da0881782a35-p077-b001"></a>
<!-- pdf-source: page=77; block=1; confidence=0.86 -->
**Chapter notes and history (continued).** … ([Tra84]). In the west the first published description is Edmonds [Edm65]. Gödel's 1956 letter essentially asks P vs. NP; von Neumann was very sick, and the letter was only discovered in the 1980s. Cook [Coo71] defined NP-completeness and showed SAT NP-complete in 1971; Karp [Kar72] showed 21 important problems NP-complete; Levin independently defined NP-completeness (focusing on search problems) and showed a variant of SAT NP-complete ([Lev73], 1973, with talks since 1971). Sipser's survey [Sip92] covers the history and translates Gödel's letter. The "TSP book" of Lawler et al. [LLKS85] traces TSP to the 19th century; a letter of Gauss to Schumacher shows him considering the Euclidean Steiner Tree problem (now known NP-hard). Garey and Johnson [GJ79] and the web site [CK00] give many more NP-complete problems; Aaronson [Aar05] surveys attempts via "non-traditional" computing devices. Even if NP ≠ P, 3SAT might be easy on average (Chapter 15; Impagliazzo's survey [Imp95]).

<a id="pdf-da0881782a35-p077-b002"></a>
<!-- pdf-source: page=77; block=2; confidence=0.88 -->
**Exercises 1.** Prove the existence of a non-deterministic universal TM N_U with N_U(x, α) = M_α(x) for a representation scheme of NDTMs: (a) halting within CT log T steps if M_α halts within T steps (C depending only on the machine represented by α); (b) running for at most Ct steps.

<a id="pdf-da0881782a35-p078-b001"></a>
<!-- pdf-source: page=78; block=1; confidence=0.86 -->
**Exercises 1 (hint)–11(a).** §1 hint: an O(|α| t log t) simulation adapts Theorem 1.13; for a more efficient one, first simulate M while non-deterministically guessing the work-tape contents, then verify the guesses tape by tape. §2: Prove Theorem 2 [sic; Theorem 2.9 is meant]. §3: HALT (Theorem 1.17) is NP-hard; is it NP-complete? §4: ≤p is reflexive and transitive but not commutative. §5: closure of NP under union and intersection. §6: {⟨φ, 1ⁿ⟩ : φ has a ZF proof of size at most n} is NP-complete (at a high level; Gödel's question). §7: NP = coNP iff 3SAT and TAUTOLOGY are polynomial-time reducible to one another. §8: a definition of NEXP without NDTMs? §9: a NEXP-complete language, and if it is in EXP then NEXP = EXP. §10: for time-constructible T, L ∈ NTIME(T(n)) has a Karp reduction to 3SAT producing 3CNFs of size O(T(n) log T(n)); can the reduction also run in that time? §11: a reduction f from an NP-language L to an NP-language L′ is *parsimonious* if the number of certificates of x equals the number of certificates of f(x) [the draft prints "the number of certificates of f is equal to the number of certificates of f(x)"]; (a) the reduction of Lemma 2.12 is parsimonious.

<a id="pdf-da0881782a35-p079-b001"></a>
<!-- pdf-source: page=79; block=1; confidence=0.86 -->
**Exercises 11(b)–16.** §11(b): a parsimonious reduction from SAT to 3SAT. §12: Cook reducibility (polynomial-time oracle TM; oracle defined via a forward reference "Section ??") is transitive, and 3SAT is Cook-reducible to TAUTOLOGY. §13 (Berman's Theorem 1978): if a unary language is NP-complete then P = NP (strengthened in Exercise 6 of Chapter 6); hint: use downward self-reducibility (Theorem 2.19). §14: CLIQUE and VERTEX COVER are NP-complete (reduce from INDSET). §15: MAX CUT is NP-complete. §16: Exactly One 3SAT and SUBSET SUM are NP-complete.

<a id="pdf-da0881782a35-p080-b001"></a>
<!-- pdf-source: page=80; block=1; confidence=0.86 -->
**Exercises 16 (hint)–23.** §16 hint: replace literal occurrences by new variables z_{i,C} for Exactly One 3SAT; map literals to numbers Σ_{j∈S_i}(2n)^j with target Σ_{j=1}^m (2n)^j for SUBSET SUM, plus a trick excluding a variable and its negation. §17: HAMPATH (undirected), TSP (Example 2.2) and HAMCYCLE are NP-complete. §18: QUADEQ (satisfiable systems of quadratic equations Σ a_{i,j} u_i u_j = b over 0/1 variables, modulo 2) is NP-complete (reduce from SAT). §19: P ⊆ NP ∩ coNP. §20: Definitions 2.21 and 2.22 define the same class. §21: NP ∩ coNP is closed under symmetric difference L₁ ⊕ L₂. §22: UNARY SUBSET SUM is in P (dynamic programming). §23: if every unary NP-language is in P then EXP = NEXP.
