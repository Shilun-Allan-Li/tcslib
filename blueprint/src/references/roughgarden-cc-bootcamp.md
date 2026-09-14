<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: d54d402b16e24167c171968b47b8205d6277512e5df493c123ab6240671b5f96 -->

<a id="pdf-d54d402b16e2-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.97 -->
# Lecture 4 — Boot Camp on Communication Complexity

<a id="pdf-d54d402b16e2-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.95 -->
**§4.1 Preamble.** Covers basic facts about deterministic and randomized two-party communication protocols in Yao's (1979) general model. Placed after three lectures on one-way protocols (single message, Alice→Bob), which sufficed for several lower-bound applications (streaming space bounds, compressive-sensing row bounds) and are easier to analyze. General-protocol lower bounds mostly reduce to a combinatorial covering problem: showing many "rectangles" of a certain type are needed to cover a matrix. Footnote: other methods exist (e.g. Lee–Shraibman 2009, the rank lower bound), but the algorithmic applications here follow from combinatorial covering arguments; alternatives are deferred to exercises.

<a id="pdf-d54d402b16e2-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.97 -->
## §4.2 Deterministic Protocols

<a id="pdf-d54d402b16e2-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.95 -->
**Definition (§4.2.1, Deterministic protocol).** In the two-party model, Alice holds input $x \in X$ (unknown to Bob) and Bob holds $y \in Y$ (unknown to Alice); commonly $X = Y = \{0,1\}^n$. A deterministic communication protocol specifies, as a function of the messages sent so far, whose turn it is to speak, when communication ends, and the output bit in each end state. Players agree on the protocol in advance and cooperate fully; the sole constraint is that each player's message depends only on that player's own input and the full history of messages sent so far.

**Cost / complexity.** The cost of a protocol is the maximum number of bits it ever sends, over all inputs. The communication complexity of a function is the minimum cost over protocols that correctly compute it. The key feature distinguishing general from one-way protocols is interaction between the players.

<a id="pdf-d54d402b16e2-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.94 -->
**Definition (§4.2.2, Clique vs. Independent Set).** Fix a graph $G = (V,E)$ with $|V| = n$ known to both players. Alice's private input is a clique $C$ of $G$ (a vertex subset with $(u,v) \in E$ for all distinct $u,v \in C$); Bob's private input is an independent set $I$ (a vertex subset with $(u,v) \notin E$ for all distinct $u,v \in I$). Neither need be maximal. Observation: $C$ and $I$ are either disjoint or intersect in a single vertex (Figure 4.1). Goal: decide which case holds — a special case of Disjointness where the sets are a clique and an independent set of a known graph.

**Cost bounds.** Naive protocol: Alice sends the characteristic vector of $C$ (or Bob that of $I$), using $\Theta(n)$ bits; smarter encoding cannot help much since the number of cliques/independent sets is generally exponential in $n$. A reduction from Index shows one-way protocols (even randomized) require $\Omega(n)$ communication (exercise). Interaction does much better.

<a id="pdf-d54d402b16e2-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.93 -->
**Protocol (interactive, begin).**
1. If there exists a vertex $v \in C$ with $\deg(v) < n/2$, Alice sends the name of an arbitrary such vertex to Bob ($\approx \log_2 n$ bits).

<a id="pdf-d54d402b16e2-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.95 -->
**Figure 4.1.** A clique $C$ and an independent set $I$ overlap in zero or one vertices.

<a id="pdf-d54d402b16e2-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.93 -->
**Protocol (continued).**
1. (a) Bob announces whether $v \in I$ (1 bit); if so, terminate with "not disjoint".
   (b) Otherwise recurse on the subgraph $H$ induced by $v$ and its neighbors. [$H$ has at most half the nodes of $G$; it contains all of $C$ and, if $I$ meets $C$, the intersection vertex. $C$ and $I$ intersect in $G$ iff their projections to $H$ intersect in $H$.]
2. Otherwise, Alice sends a "NULL" message to Bob ($\approx \log_2 n$ bits).
3. If there exists $v \in I$ with $\deg(v) \ge n/2$, Bob sends the name of an arbitrary such vertex to Alice ($\approx \log_2 n$ bits).
   (a) Alice announces whether $v \in C$ (1 bit); if so, terminate with "not disjoint".
   (b) Otherwise recurse on the subgraph $H$ induced by $v$ and its non-neighbors. [$H$ has at most half the nodes; contains all of $I$ and, if $C$ meets $I$, the intersection vertex, so the answer in $H$ equals that in $G$.]
4. Otherwise, Bob terminates and declares "disjoint". [Correct because at this point $\deg(v) < n/2$ for all $v \in C$ and $\deg(v) \ge n/2$ for all $v \in I$.]

<a id="pdf-d54d402b16e2-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.95 -->
Each iteration of the protocol uses O(log n) bits and halves the number of graph vertices (or terminates), giving total communication O(log² n). This bound is unachievable without interaction between the players.

<a id="pdf-d54d402b16e2-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.99 -->
## 4.2.3 Trees and Matrices

<a id="pdf-d54d402b16e2-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.92 -->
Clique-Independent Set shows Pigeonhole arguments (adequate for one-way protocols) fail for general protocols, motivating new machinery. Key observation: every deterministic communication protocol is a binary tree.

<a id="pdf-d54d402b16e2-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.95 -->
**Example (Equality, n = 2).** Here f(x,y) = 1 iff x = y. Alice sends her first bit. If Bob's first bit differs, he terminates and announces "not equal." If it matches, Bob echoes the bit; Alice then sends her second bit, after which Bob knows Alice's whole input and outputs the answer.

<a id="pdf-d54d402b16e2-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.94 -->
**Definition (protocol tree / leaf partition).** In the tree (Figure 4.2) each node corresponds to a possible state of the protocol and is labeled with the player whose turn it is to speak; the labels alternate with the levels, with the root belonging to Alice (in general, players need not alternate turns). There are 10 leaves, representing the possible end states of the protocol: two for the case where Alice and Bob have different first bits and the protocol terminates early, and eight for the remaining cases where they have the same first bit. The possible transcripts are in one-to-one correspondence with the root-to-leaf paths, so leaves and transcripts are used interchangeably. We can view the leaves as a partition {Z(ℓ)} of the input space X × Y, with Z(ℓ) the inputs (x, y) such that the protocol terminates in the leaf ℓ. In our example, there are 10 leaves for the 16 possible inputs (x, y), so different inputs can generate the same transcript.

<a id="pdf-d54d402b16e2-p004-b006"></a>
<!-- pdf-source: page=4; block=6; confidence=0.93 -->
**Definition (matrix representation).** A function f : X × Y → {0,1} is represented as a matrix with rows indexed by Alice's inputs X, columns by Bob's inputs Y, and entry (x,y) equal to f(x,y). This matrix is fully known to both players once they agree on a protocol; it is used throughout.

<a id="pdf-d54d402b16e2-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.97 -->
**Figure 4.2.** The binary tree induced by a communication protocol for Equality with n = 2.

<a id="pdf-d54d402b16e2-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.97 -->
**Example (Equality matrix, eq. 4.1).** For example, suppose that X = Y = {0,1}², resulting in 4×4 matrices (rows and columns indexed 00, 01, 10, 11). Equality then corresponds to the identity matrix:

$$\begin{array}{c|cccc} & 00 & 01 & 10 & 11 \\ \hline 00 & 1 & 0 & 0 & 0 \\ 01 & 0 & 1 & 0 & 0 \\ 10 & 0 & 0 & 1 & 0 \\ 11 & 0 & 0 & 0 & 1 \end{array} \tag{4.1}$$

<a id="pdf-d54d402b16e2-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.96 -->
**Example (Greater-Than matrix).** If we define the Greater-Than function as 1 whenever x is at least y (where x and y are interpreted as non-negative integers, written in binary), then we just fill in the lower triangle with 1s:

$$\begin{array}{c|cccc} & 00 & 01 & 10 & 11 \\ \hline 00 & 1 & 0 & 0 & 0 \\ 01 & 1 & 1 & 0 & 0 \\ 10 & 1 & 1 & 1 & 0 \\ 11 & 1 & 1 & 1 & 1 \end{array}$$

<a id="pdf-d54d402b16e2-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.95 -->
**Example (Disjointness matrix).** We also write out the matrix for Disjointness (x, y viewed as subsets; value 1 iff the sets are disjoint) over X = Y = {0,1}², which is somewhat more inscrutable than the Equality and Greater-Than matrices:

$$\begin{array}{c|cccc} & 00 & 01 & 10 & 11 \\ \hline 00 & 1 & 1 & 1 & 1 \\ 01 & 1 & 0 & 1 & 0 \\ 10 & 1 & 1 & 0 & 0 \\ 11 & 1 & 0 & 0 & 0 \end{array}$$

<a id="pdf-d54d402b16e2-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.99 -->
## 4.2.4 Protocols and Rectangles

<a id="pdf-d54d402b16e2-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.90 -->
To find a usable counting argument, run the 2-bit Equality protocol against matrix (4.1) from the viewpoint of an outside observer who knows neither x nor y. At termination the matrix is carved into 10 pieces, one per leaf; the transcript reveals only the leaf.

<a id="pdf-d54d402b16e2-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.90 -->
Before any bit, all 16 inputs are possible. Alice's first bit narrows to 8 (top 8 if 0, bottom 8 if 1). The next bit reveals Bob's first bit, identifying the quadrant. In the northeastern and southwestern quadrants all entries are 0, so f(x,y) is determined (= 0) even though (x,y) is not — these correspond to the two early-stopping leaves. Otherwise Alice's second bit and Bob's final bit split the northwestern and southeastern quadrants down to singleton regions, revealing the entire input.

<a id="pdf-d54d402b16e2-p006-b005"></a>
<!-- pdf-source: page=6; block=5; confidence=0.88 -->
Every protocol induces a partition of X × Y with one set per leaf / distinct transcript. For this protocol each such set has a submatrix (combinatorial rectangle) form (Figure 4.3), and this holds in general — the claim developed next.

<a id="pdf-d54d402b16e2-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.90 -->
**Figure 4.3** The partition of the input space X × Y according to the 10 different transcripts that can be generated by the Equality protocol.

The underlying 4×4 grid (rows/columns 00, 01, 10, 11) is the identity matrix, carved into rectangles by the transcripts:

$$\begin{array}{c|cccc} & 00 & 01 & 10 & 11 \\ \hline 00 & 1 & 0 & 0 & 0 \\ 01 & 0 & 1 & 0 & 0 \\ 10 & 0 & 0 & 1 & 0 \\ 11 & 0 & 0 & 0 & 1 \end{array}$$

<a id="pdf-d54d402b16e2-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.98 -->
**Lemma 4.1 (Rectangles).** For every transcript z of a deterministic protocol P, the set of inputs (x, y) that generate z forms a rectangle A × B with A ⊆ X and B ⊆ Y.

<a id="pdf-d54d402b16e2-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.95 -->
**Definition (rectangle).** A rectangle is a subset of X × Y expressible as a product A × B. Equivalently, S ⊆ X × Y is a rectangle iff it is closed under "mix and match": whenever (x₁, y₁), (x₂, y₂) ∈ S, also (x₁, y₂), (x₂, y₁) ∈ S. Example: {(00,00),(11,00),(00,11),(11,11)} is a rectangle; {(00,00),(11,11)} is not. Such sets are also called combinatorial rectangles, and X, Y need not be viewed as ordered.

<a id="pdf-d54d402b16e2-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.95 -->
**Proof of Lemma 4.1.** By induction on the number of bits exchanged. Base case: with the empty transcript, all inputs X × Y generate it. Inductive step: for a t-bit transcript-so-far z (t ≥ 1), suppose Alice spoke last (Bob's case is analogous). Let z₀ be z with its final bit b ∈ {0,1} removed; by the inductive hypothesis the inputs generating z₀ have the form A × B. Let A_b ⊆ A be those x ∈ A for which Alice sends bit b given z₀ (a player's message depends only on its private input and the history). [Continues on p. 8: the set generating z is A_b × B, completing the step.]

<a id="pdf-d54d402b16e2-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.95 -->
**Proof of Lemma 4.1 (concl.).** The set of inputs generating z is A_b × B, completing the inductive step. ∎ Note: Lemma 4.1 holds for any deterministic protocol, independent of any function f.

<a id="pdf-d54d402b16e2-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.98 -->
**Lemma 4.2.** If a deterministic protocol P computes a function f, then every rectangle induced by P is monochromatic in the matrix M(f) (all its entries share the same value).

<a id="pdf-d54d402b16e2-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.97 -->
**Proof of Lemma 4.2.** Let A × B be a rectangle induced by P, all of whose inputs produce the same transcript. The output of P is constant on A × B; since P computes f, f is constant on A × B. ∎

<a id="pdf-d54d402b16e2-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.98 -->
**Theorem 4.3.** Let f be a function such that every partition of M(f) into monochromatic rectangles requires at least t rectangles. Then the deterministic communication complexity of f is at least log₂ t.

<a id="pdf-d54d402b16e2-p008-b005"></a>
<!-- pdf-source: page=8; block=5; confidence=0.97 -->
**Proof of Theorem 4.3.** A deterministic protocol with communication cost c generates at most 2^c distinct transcripts (its protocol tree has at most 2^c leaves). If it computes f, then by Lemmas 4.1 and 4.2 it partitions M(f) into at most 2^c monochromatic rectangles. By assumption 2^c ≥ t, hence c ≥ log₂ t. ∎

<a id="pdf-d54d402b16e2-p008-b006"></a>
<!-- pdf-source: page=8; block=6; confidence=0.92 -->
**Definition (covering).** A covering of a 0-1 matrix is a collection of subsets of entries whose union includes all elements, with overlaps allowed (unlike a partition, which requires disjointness). See Figure 4.4.

<a id="pdf-d54d402b16e2-p008-b007"></a>
<!-- pdf-source: page=8; block=7; confidence=0.95 -->
**Corollary 4.4.** Let f be a function such that every covering of M(f) by monochromatic rectangles requires at least t rectangles. Then the deterministic communication complexity of f is at least log₂ t. (Lower bounds proved via covers also apply to nondeterministic protocols and to randomized protocols with 1-sided error.)

<a id="pdf-d54d402b16e2-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.90 -->
**Figure 4.4** A covering by four monochromatic rectangles that is not a partition.

The underlying 3×3 grid of values is:

$$\begin{array}{ccc} 0 & 1 & 1 \\ 1 & 1 & 1 \\ 1 & 1 & 0 \end{array}$$

<a id="pdf-d54d402b16e2-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.97 -->
**4.2.5 Lower Bounds for Equality and Disjointness**

<a id="pdf-d54d402b16e2-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.93 -->
For the Equality function, M(f) is the identity matrix. Key observation: a monochromatic rectangle containing a 1 contains exactly one element — it cannot contain a 0, and by closure under mix-and-match a second 1 would force in some 0-entries. Since there are 2ⁿ ones, every covering by monochromatic rectangles (even of the 1's alone) has size 2ⁿ.

<a id="pdf-d54d402b16e2-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.98 -->
**Corollary 4.5.** The deterministic communication complexity of Equality is at least n.

<a id="pdf-d54d402b16e2-p009-b005"></a>
<!-- pdf-source: page=9; block=5; confidence=0.97 -->
**Corollary 4.6.** The same argument gives: the deterministic communication complexity of Greater-Than is at least n.

<a id="pdf-d54d402b16e2-p009-b006"></a>
<!-- pdf-source: page=9; block=6; confidence=0.97 -->
**Definition (fooling set).** A fooling set for f is a subset F ⊆ X × Y such that: (i) f is constant on F; (ii) for each distinct pair (x₁,y₁), (x₂,y₂) ∈ F, at least one of (x₁,y₂), (x₂,y₁) has the opposite f-value.

<a id="pdf-d54d402b16e2-p009-b007"></a>
<!-- pdf-source: page=9; block=7; confidence=0.90 -->
Footnote 4: the 0's can be covered by 2ⁿ additional monochromatic rectangles, one per row (rectangles need not be contiguous), giving a lower bound of n+1. The trivial upper bound is an (n+1)-bit protocol where Alice sends her input and Bob announces the answer. Analogous "+1" improvements apply to the other examples.

<a id="pdf-d54d402b16e2-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.92 -->
**Proof (continued).** Because rectangles are closed under the "mix and match" operation, properties (i) and (ii) imply that every monochromatic rectangle contains at most one element of the fooling set F.

<a id="pdf-d54d402b16e2-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.96 -->
**Corollary 4.7.** If F is a fooling set for f, then the deterministic communication complexity of f is at least log₂|F|.

<a id="pdf-d54d402b16e2-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.90 -->
The lower bounds for Equality and Greater-Than effectively used the fooling set F = {(x, x) : x ∈ {0,1}ⁿ}.

<a id="pdf-d54d402b16e2-p010-b004"></a>
<!-- pdf-source: page=10; block=4; confidence=0.97 -->
**Corollary 4.8.** The deterministic communication complexity of Disjointness is at least n.

<a id="pdf-d54d402b16e2-p010-b005"></a>
<!-- pdf-source: page=10; block=5; confidence=0.90 -->
**Proof.** Take F = {(x, x̄) : x ∈ {0,1}ⁿ}, equivalently {(S, Sᶜ) : S ⊆ {1,2,…,n}}. Each such pair is a "yes" input of Disjointness, and for distinct S ≠ T at least one of S ∩ Tᶜ or T ∩ Sᶜ is nonempty; hence F is a fooling set. Since |F| = 2ⁿ, Corollary 4.7 gives the bound of n. ∎

<a id="pdf-d54d402b16e2-p010-b006"></a>
<!-- pdf-source: page=10; block=6; confidence=0.90 -->
**Figure 4.5.** For distinct sets S and T, either S and Tᶜ, or T and Sᶜ, fail to be disjoint.

<a id="pdf-d54d402b16e2-p010-b007"></a>
<!-- pdf-source: page=10; block=7; confidence=0.98 -->
**4.2.6 Take-Aways**

<a id="pdf-d54d402b16e2-p010-b008"></a>
<!-- pdf-source: page=10; block=8; confidence=0.90 -->
Covering arguments yield the desired lower bounds on the deterministic communication complexity of many functions of interest; these bounds also apply to nondeterministic protocols and to randomized protocols with one-sided error. Obtaining stronger bounds that also cover two-sided-error randomized protocols is more challenging.

<a id="pdf-d54d402b16e2-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.85 -->
Since a good randomized algorithm is usually acceptable (e.g. the F₂-estimation algorithm of Section 1.4), lower bounds against two-sided-error randomized protocols are the relevant next topic.

<a id="pdf-d54d402b16e2-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.97 -->
**4.3 Randomized Protocols** — 4.3.1 Default Parameter Settings

<a id="pdf-d54d402b16e2-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.93 -->
**Default parameter settings** (our discussion of randomized one-way protocols in Section 2.2 remains equally relevant; the settings are the same):
- **Public coins:** by default we work with public-coin protocols, where Alice and Bob have shared randomness (an infinite sequence of perfectly random bits in public view); such protocols are more powerful than private-coin protocols, but not by much (Theorem 4.9). Public-coin randomized protocols are equivalent to distributions over deterministic protocols.
- **Two-sided error:** we allow a protocol to err with constant probability (1/3 by default), whether or not the correct answer is "1" or "0"; this is the most permissive error model.
- **Arbitrary constant error probability:** all constant error probabilities in (0, 1/2) are the same — changing the error changes the randomized communication complexity by only a constant factor (the usual "independent trials" argument). Thus for upper bounds we'll be content to achieve error 49%; for lower bounds, it is enough to rule out low-communication protocols with error 1%.
- **Worst-case communication:** the communication cost of a randomized protocol is the maximum number of bits ever communicated, over all choices of inputs and coin flips; measuring the expected communication (over the coin flips) could reduce the cost of a problem, but only by a constant factor.

<a id="pdf-d54d402b16e2-p011-b004"></a>
<!-- pdf-source: page=11; block=4; confidence=0.96 -->
**4.3.2 Newman's Theorem: Public- vs. Private-Coin Protocols**

<a id="pdf-d54d402b16e2-p011-b005"></a>
<!-- pdf-source: page=11; block=5; confidence=0.96 -->
**Theorem 4.9 (Newman's Theorem, 1991).** If there is a public-coin protocol for a function f with n-bit inputs having two-sided error 1/3 and communication cost c, then there is a private-coin protocol for f with two-sided error 1/3 and communication cost O(c + log n).

<a id="pdf-d54d402b16e2-p011-b006"></a>
<!-- pdf-source: page=11; block=6; confidence=0.90 -->
For problems with public-coin randomized communication complexity Ω(log n) — most problems studied here — public-coin and private-coin variants have the same complexity up to constant factors.

<a id="pdf-d54d402b16e2-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.90 -->
Exception: Equality has a one-way public-coin protocol of constant communication, but Theorem 4.9 only gives an O(log n) private-coin upper bound, and there is a matching Ω(log n) private-coin lower bound. Thus public coins save Θ(log n) bits over private coins for Equality, but no more.

<a id="pdf-d54d402b16e2-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.90 -->
**Proof of Theorem 4.9.** Let P be a public-coin protocol with two-sided error 1/3.

*Thought experiment:* Fix an input (x, y) with x, y ∈ {0,1}ⁿ. Running P for t independent trials consuming random strings r₁,…,r_t yields t answers, each correct with probability ≥ 2/3. Chernoff bounds (δ = Θ(1), µ = Θ(t)) imply at least 60% of the answers are correct with probability at least 1 − exp{−Θ(t)}.

*Union bound:* Over all 2ⁿ · 2ⁿ = 2²ⁿ inputs (x, y), with probability at least 1 − 2²ⁿ · exp{−Θ(t)} a single sequence r₁,…,r_t simultaneously yields ≥ 0.6t correct answers for every input. Taking t = cn for a large enough constant c makes this probability positive, so such strings exist.

*Private-coin protocol:*
(0) Before receiving inputs, Alice and Bob agree on strings r₁,…,r_t with the above property.
(1) Alice picks i ∈ {1,…,t} uniformly at random and sends it to Bob, using ≈ log₂ t = Θ(log n) bits (t = Θ(n)).
(2) They simulate P using rᵢ as the public coins.

This protocol has error 40%, reducible to 1/3 by a constant number of independent repetitions plus majority vote. The total communication cost is O(c + log n). ∎

<a id="pdf-d54d402b16e2-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.95 -->
Theorem 4.9, stated and proved for general protocols, holds with the same proof for the one-way protocols of Lectures 1–3.

<a id="pdf-d54d402b16e2-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.99 -->
**4.3.3 Distributional Complexity**

<a id="pdf-d54d402b16e2-p013-b003"></a>
<!-- pdf-source: page=13; block=3; confidence=0.90 -->
Randomized protocols are harder to reason about: a deterministic protocol is a partition of the input space into rectangles, whereas a randomized protocol is a distribution over such partitions. A deterministic protocol computing $f$ induces only monochromatic rectangles, but a randomized one need not (it may err).

<a id="pdf-d54d402b16e2-p013-b004"></a>
<!-- pdf-source: page=13; block=4; confidence=0.95 -->
**Lemma 4.10 (Yao 1983).** Let $D$ be a distribution over inputs $(x,y)$ and $\epsilon\in(0,\tfrac12)$. If every deterministic protocol $P$ with $\Pr_{(x,y)\sim D}[P\text{ wrong on }(x,y)]\le\epsilon$ has communication cost $\ge k$, then every public-coin randomized protocol $R$ with two-sided error $\le\epsilon$ on every input has communication cost $\ge k$.

<a id="pdf-d54d402b16e2-p013-b005"></a>
<!-- pdf-source: page=13; block=5; confidence=0.90 -->
This is Lemma 2.3, proved in Lecture 2 for one-way protocols; the same proof holds verbatim for general protocols. It is a "complete" technique: for the true randomized complexity there always exists a hard distribution $D$ that can prove it.

<a id="pdf-d54d402b16e2-p013-b006"></a>
<!-- pdf-source: page=13; block=6; confidence=0.95 -->
Proving randomized communication lower bounds reduces to: (1) finding a hard distribution $D$ over inputs; (2) showing every low-communication deterministic protocol has large error w.r.t. inputs drawn from $D$.

<a id="pdf-d54d402b16e2-p013-b007"></a>
<!-- pdf-source: page=13; block=7; confidence=0.97 -->
**4.3.4 Case Study: Disjointness** — *Overview*

<a id="pdf-d54d402b16e2-p013-b008"></a>
<!-- pdf-source: page=13; block=8; confidence=0.90 -->
Lecture 2 showed the one-way randomized communication complexity of Disjointness is linear (Theorem 2.2), via a reduction from Index (a special case where one player holds a singleton set / standard basis vector).

<a id="pdf-d54d402b16e2-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.90 -->
**4.3 Randomized Protocols**

<a id="pdf-d54d402b16e2-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.90 -->
The one-way $\Omega(n)$ bound for Index used Yao's Lemma with $D$ uniform and a counting argument on the volume of small-radius balls in the Hamming cube. But for general protocols Index has complexity $O(\log n)$: Bob sends his index $i$ in $\approx\log_2 n$ bits and Alice computes the function. So a new approach is needed.

<a id="pdf-d54d402b16e2-p014-b003"></a>
<!-- pdf-source: page=14; block=3; confidence=0.97 -->
**Theorem 4.11 (Kalyanasundaram and Schnitger 1992; Razborov 1992).** The randomized communication complexity of Disjointness is $\Omega(n)$.

<a id="pdf-d54d402b16e2-p014-b004"></a>
<!-- pdf-source: page=14; block=4; confidence=0.85 -->
Originally proved by Kalyanasundaram and Schnitger (1992); Razborov's (1992) simplified proof is more influential, and modern proofs use information-complexity arguments (Bar-Yossef et al. 2002a). The result is central because Disjointness is highly effective as a black box for lower bounds on other algorithmic problems, and its proofs showcase reusable techniques.

<a id="pdf-d54d402b16e2-p014-b005"></a>
<!-- pdf-source: page=14; block=5; confidence=0.85 -->
Since general-protocol bounds (unlike one-way ones) apply to multi-pass algorithms, Theorem 4.11 upgrades every $\Omega(m)$ space lower bound for 1-pass streaming to $\Omega(m/p)$ for $p$-pass algorithms via the same reductions — e.g. for computing $F_\infty$ (highest frequency, even with randomization and approximation) and for computing $F_0$ or $F_2$ exactly with randomization. Footnote: a $p$-pass space-$s$ algorithm induces a protocol with $O(ps)$ communication.

<a id="pdf-d54d402b16e2-p014-b006"></a>
<!-- pdf-source: page=14; block=6; confidence=0.90 -->
By Yao's Lemma, proving Theorem 4.11 reduces to exhibiting a hard distribution $D$ over inputs and showing all low-communication deterministic protocols have large error w.r.t. $D$.

<a id="pdf-d54d402b16e2-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.95 -->
*Choosing a Hard Distribution*

<a id="pdf-d54d402b16e2-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.90 -->
Under the uniform distribution, each coordinate has $\Pr[x_i=y_i=1]=1/4$, so $f(x,y)=1$ (not disjoint) with probability $(3/4)^n$. Hence the zero-communication protocol always outputting "not disjoint" has low error. A hard distribution $D$ must produce both yes- and no-instances with constant probability.

<a id="pdf-d54d402b16e2-p015-b003"></a>
<!-- pdf-source: page=15; block=3; confidence=0.88 -->
Motivated by the Birthday Paradox, let $D$ give Alice and Bob each a random subset of $\{1,\dots,n\}$ of size $\approx\sqrt n$; then $f(x,y)=1$ and $f(x,y)=0$ each occur with constant probability. But there is a zero-error deterministic protocol using $O(\sqrt n\log n)$ bits (a player names each of their $\sqrt n$ elements with $\approx\log_2 n$ bits), so no linear lower bound follows. Babai et al. (1986) prove an $\Omega(\sqrt n)$ lower bound holds for this distribution, and that for every product distribution $D$ (where $x$ and $y$ are chosen independently) there is a zero-error deterministic protocol using $O(\sqrt n\log n)$ bits.

<a id="pdf-d54d402b16e2-p015-b004"></a>
<!-- pdf-source: page=15; block=4; confidence=0.92 -->
For an $\Omega(n)$ randomized lower bound, $D$ must satisfy: (1) $f(x,y)=1$ and $f(x,y)=0$ each with constant probability (else a constant protocol works); (2) inputs usually correspond to sets of size $\Omega(n)$ (else a player communicates their set); (3) $x$ and $y$ are correlated (else the Babai et al. 1986 upper bound applies); (4) it is mathematically tractable to lower-bound the error of all sublinear-communication deterministic protocols.

<a id="pdf-d54d402b16e2-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.90 -->
## 4.3 Randomized Protocols

<a id="pdf-d54d402b16e2-p016-b002"></a>
<!-- pdf-source: page=16; block=2; confidence=0.90 -->
**Definition (Razborov 1992 distribution).** A distribution over inputs $(x,y)$ that satisfies the first three desired properties and, less obviously, the fourth. It is defined as:
- With probability $75\%$: $(x,y)$ chosen uniformly subject to (i) $x,y$ each have exactly $n/4$ ones, and (ii) no index $i\in\{1,\dots,n\}$ has $x_i=y_i=1$ (so $f(x,y)=1$).
- With probability $25\%$: $(x,y)$ chosen uniformly subject to (i) $x,y$ each have exactly $n/4$ ones, and (ii) exactly one index $i$ has $x_i=y_i=1$ (so $f(x,y)=0$).

In both cases the constraint on the number of indices with $x_i=y_i=0$ creates correlation between the choices of $x$ and $y$.

<a id="pdf-d54d402b16e2-p016-b003"></a>
<!-- pdf-source: page=16; block=3; confidence=0.90 -->
### Proving Error Lower Bounds via Corruption Bounds

<a id="pdf-d54d402b16e2-p016-b004"></a>
<!-- pdf-source: page=16; block=4; confidence=0.80 -->
The corruption method proves error lower bounds for low-communication deterministic protocols, extending the covering arguments of Section 4.2 to protocols that may err. Weighted by distribution $D$ and allowing error, one argues there is significant mass on the 1-inputs of $f$ and that many nearly monochromatic rectangles are needed to cover them.

<a id="pdf-d54d402b16e2-p016-b005"></a>
<!-- pdf-source: page=16; block=5; confidence=0.85 -->
Setup: a distribution $D$ whose "1-mass" $\Pr_{(x,y)\sim D}[f(x,y)=1]$ is at least a constant (say $.5$). The plan proves two properties.

**(1)** For every deterministic protocol $P$ with error at most a sufficiently small constant $\epsilon$, at least $25\%$ of the 1-mass of $D$ is contained in "almost monochromatic 1-rectangles" of $P$ (defined below). This holds in general by an averaging argument.

<a id="pdf-d54d402b16e2-p016-b006"></a>
<!-- pdf-source: page=16; block=6; confidence=0.85 -->
Footnote: since $f$ has only two outputs, it is almost without loss to fix a single output $z\in\{0,1\}$ and lower bound only the number of monochromatic rectangles needed to cover all $z$-inputs.

<a id="pdf-d54d402b16e2-p017-b001"></a>
<!-- pdf-source: page=17; block=1; confidence=0.85 -->
**(2)** An almost monochromatic 1-rectangle contains at most $2^{-c}$ mass of the distribution $D$, where $c$ is as large as possible (ideally $c = \Omega(n)$). This is the hard step, and the argument will be different for different functions $f$ and different input distributions $D$.

If we can establish (1) and (2), then we have a lower bound of $\Omega(2^{-c})$ on the number of rectangles induced by $P$, which proves that $P$ uses communication $\Omega(c)$.

<a id="pdf-d54d402b16e2-p017-b002"></a>
<!-- pdf-source: page=17; block=2; confidence=0.90 -->
**Definition (AM1R).** A rectangle $R=A\times B$ of the matrix $M(f)$ is an almost monochromatic 1-rectangle with respect to input distribution $D$ if
$$\Pr_{(x,y)\sim D}[(x,y)\in R \text{ and } f(x,y)=0] \;\le\; 8\epsilon\cdot \Pr_{(x,y)\sim D}[(x,y)\in R \text{ and } f(x,y)=1]. \tag{4.2}$$

<a id="pdf-d54d402b16e2-p017-b003"></a>
<!-- pdf-source: page=17; block=3; confidence=0.85 -->
**Proof (of property (1)).** Let $P$ be deterministic with error at most $\epsilon$ w.r.t. $D$. Being deterministic, $P$ partitions $M(f)$ into rectangles with constant output; let $R_1,\dots,R_\ell$ be those where $P$ outputs "1".

At least $50\%$ of the 1-mass of $D$ (hence at least $25\%$ of total mass) lies in $R_1,\dots,R_\ell$: otherwise on at least $25\%$ of $D$'s mass $f(x,y)=1$ while $P$ outputs "0", contradicting error $\epsilon$ (given $\epsilon<.25$).

Also at least $50\%$ of the mass in $R_1,\dots,R_\ell$ lies in AM1Rs: otherwise, by (4.2) and total mass $\ge .25$ in these rectangles, $D$ would place more than $8\epsilon\cdot .125=\epsilon$ mass on 0-inputs of $R_1,\dots,R_\ell$, where $P$ outputs "1", contradicting error $\le\epsilon$. This proves step (1) for any problem and any $D$ with 1-mass $\ge .5$.

<a id="pdf-d54d402b16e2-p017-b004"></a>
<!-- pdf-source: page=17; block=4; confidence=0.85 -->
Step (2) is difficult and problem-specific. Babai et al. (1986), for their Disjointness input distribution, proved step (2) with $c=\Omega(\sqrt{n})$, giving an $\Omega(\sqrt{n})$ lower bound on randomized communication complexity. Razborov (1992), for his distribution, proved step (2) with $c=\Omega(n)$, giving the desired $\Omega(n)$ lower bound for Disjointness. Subsequent proofs (e.g. Bar-Yossef et al. 2002a) are not covered.

<a id="pdf-d54d402b16e2-p017-b005"></a>
<!-- pdf-source: page=17; block=5; confidence=0.85 -->
Footnote: the method is called "corruption" because it shows that if a deterministic protocol has low communication, most of its rectangles containing 1-inputs are "corrupted" by many 0-inputs — they are so large that (4.2) fails — which implies large error.
