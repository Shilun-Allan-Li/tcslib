<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: fa052d8c95c0cb623ac076478337d47a58de2818d97a8061a841b025654819cf -->

<a id="pdf-fa052d8c95c0-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.90 -->
**Chapter 1. Deterministic Protocols.** Introduces communication protocols: a way for $k$ parties, each holding different inputs, to communicate to learn some property of all inputs. The section motivates the topic with example communication problems.

<a id="pdf-fa052d8c95c0-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.95 -->
**Example (Equality).** Alice and Bob hold $n$-bit strings $x,y\in\{0,1\}^n$ and want to decide whether $x=y$.
- Trivial deterministic protocol: Alice sends $x$, Bob replies — $n+1$ bits; no deterministic protocol does better.
- Randomized protocol: hash inputs and compare hashes — $O(1)$ bits.
- Non-deterministic protocol: guess an index $i$ with $x_i\ne y_i$ and send it — $O(\log n)$ bits.

<a id="pdf-fa052d8c95c0-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.90 -->
**Example (Cliques and Independent Sets).** Alice holds $A\subseteq[n]$, Bob holds $B\subseteq[n]$; both know a graph $G$ on vertex set $[n]$, with the promise that $A$ is a clique and $B$ is an independent set. They want to decide whether $A\cap B\ne\varnothing$. No one-way protocol solves this using fewer than $n$ bits, but an interactive protocol uses $O(\log^2 n)$ bits: if $A$ contains a vertex $v$ of degree $<n/2$, Alice announces $v$; then either $v\in B$, or all non-neighbors of $v$ can be discarded from $A$ (halving the graph). Symmetrically, if $B$ contains a vertex $v$ of degree $\ge n/2$, Bob announces it.

<a id="pdf-fa052d8c95c0-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.88 -->
**Example (continued).** In the symmetric case, either $v\in A$, or Alice and Bob discard all neighbors of $v$, again halving the graph. After at most $\log n$ such steps the answer is determined.

<a id="pdf-fa052d8c95c0-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.88 -->
**Example ($k$-Disjointness).** Alice and Bob hold sets $A,B\subseteq[n]$, each of size $k$, and want to know whether they share a common element.
- Sending $A$ costs $k\log n$ bits.
- Randomized protocol using $O(k)$ bits: parties share a random sequence of sets; Alice announces the name of the first set containing $A$; if $A,B$ are disjoint this eliminates half of $B$, and repeating gives $O(k)$ bits.
- Non-deterministic protocol: $O(\log n)$ bits.

<a id="pdf-fa052d8c95c0-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.96 -->
**Example ($k$-party Disjointness).** Input is $k$ sets $A_1,\dots,A_k\subseteq[n]$ with $k$ parties; the $i$-th party knows all sets except $A_i$. They want to know whether all sets share a common element. There is a deterministic protocol using $O(n/2^k)$ bits, essentially optimal. No randomized protocol has communication less than $\sqrt{n}/2^k$, but tightness of this bound is unknown.

<a id="pdf-fa052d8c95c0-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.90 -->
**Example (3-Sum).** Input is three numbers $x,y,z\in[n]$; Alice knows $(x,y)$, Bob knows $(y,z)$, Charlie knows $(x,z)$. They want to decide whether $x+y+z=n$. Alice sending $x$ to Bob gives an $O(\log n)$-bit protocol. There is a deterministic protocol communicating $o(\log n)$ bits, but any deterministic protocol must communicate $\omega(1)$ bits. A randomized protocol communicates $O(1)$ bits.

<a id="pdf-fa052d8c95c0-p002-b005"></a>
<!-- pdf-source: page=2; block=5; confidence=0.90 -->
**Example (Pointer Chasing).** Input is two functions $f,g:[n]\to[n]$, with Alice knowing $f$ and Bob knowing $g$. Define $a_0,a_1,\dots,a_k\in[n]$ by $a_0=1$ and $a_i=f(g(a_{i-1}))$; the goal is to compute $a_k$. A simple $k$-round protocol achieves communication $O(k\log n)$, but any protocol with fewer than $k$ rounds requires $\Omega(n)$ bits.

<a id="pdf-fa052d8c95c0-p002-b006"></a>
<!-- pdf-source: page=2; block=6; confidence=0.96 -->
**Example (Graph Connectivity).** Input is an undirected graph on vertices $[n]$ with $k$ parties; the $j$-th party knows all edges except those touching vertices in $[(j-1)n/k,\; jn/k]$. They want to decide whether vertex $1$ is connected to vertex $n$. The trivial deterministic protocol uses $O(n^2/k)$ bits. There is no randomized protocol using fewer than $n/2^k$ bits.

<a id="pdf-fa052d8c95c0-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.92 -->
**Definition (2-party deterministic protocol).** Inputs come from sets $\mathcal{X},\mathcal{Y}$. A protocol $\pi$ is a rooted binary tree in which every internal vertex $v$ has 2 children and is associated with one of the two parties together with a function $f_v:\mathcal{X}\to\{0,1\}$ (or $f_v:\mathcal{Y}\to\{0,1\}$) mapping that party's input to a child of $v$.

<a id="pdf-fa052d8c95c0-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.92 -->
**Definition (outcome).** For inputs $(x,y)\in\mathcal{X}\times\mathcal{Y}$, the outcome $\pi(x,y)$ is a leaf computed as follows: start with current vertex $v$ = root; the party associated with $v$ announces $f_v(x)$ (or $f_v(y)$); both parties move to the indicated child. Repeat until a leaf is reached; that leaf is the outcome.

<a id="pdf-fa052d8c95c0-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.90 -->
**Definition (computing a function, complexity, rounds).** For a boolean $g:\mathcal{X}\times\mathcal{Y}\to\{0,1\}$, protocol $\pi$ *computes* $g$ if $\pi(x,y)$ determines $g(x,y)$ for every input; leaves may be labeled by the computed value. The communication complexity $\lVert\pi\rVert$ is the depth of the protocol tree (longest root-to-leaf path). A function has communication complexity $c$ if some protocol computes it with $c$ bits but none does with fewer. The number of rounds is the maximum number of alternations between the two parties' messages along any root-to-leaf path. An efficient protocol has minimal communication complexity and minimal number of rounds.

<a id="pdf-fa052d8c95c0-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.92 -->
**Fact 1.1.** For any protocol $\pi$, the number of rounds in $\lVert\pi\rVert$ is always at most $\lVert\pi\rVert-1$.

<a id="pdf-fa052d8c95c0-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.90 -->
**Lemma 1.2.** The number of leaves in the protocol tree for $\pi$ is at most $2^{\lVert\pi\rVert}$.

<a id="pdf-fa052d8c95c0-p003-b006"></a>
<!-- pdf-source: page=3; block=6; confidence=0.85 -->
**Proof.** By induction on the communication $\lVert\pi\rVert$. Base case: communication $0$ gives exactly $2^0=1$ leaf. Inductive step: if the communication is $\lVert\pi\rVert$, then by induction the left and right subtrees of the root each have at most $2^{\lVert\pi\rVert-1}$ leaves, so the total is at most $2\cdot 2^{\lVert\pi\rVert-1}=2^{\lVert\pi\rVert}$. $\square$

<a id="pdf-fa052d8c95c0-p003-b007"></a>
<!-- pdf-source: page=3; block=7; confidence=0.82 -->
**Remark (k-party protocols).** Analogously, for sets $\mathcal{X}_1,\dots,\mathcal{X}_k$ a $k$-party protocol lets $k$ parties communicate about their inputs, the $i$-th from $\mathcal{X}_i$; each vertex $v$ is associated with a party $i$ and a function $f_v:\mathcal{X}_i\to\{0,1\}$. When $\mathcal{X}=\mathcal{Y}=\{0,1\}^n$ and each $f_v$ equals a single bit of the input, the protocol is a *decision tree*. Definitions extend to non-boolean functions (restricted here to boolean for simplicity) and to functions $g:\mathcal{D}\to\mathcal{R}$ on a domain $\mathcal{D}\subseteq\mathcal{X}_1\times\cdots\times\mathcal{X}_k$ — relevant to the Number-on-Forehead model. Rounds example: Alice 2 bits, Bob 3 bits, Alice 1 bit → 2 rounds.

<a id="pdf-fa052d8c95c0-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.95 -->
**Balancing Protocols.** Lemma 1.2 is tight exactly when the protocol tree is a balanced binary tree; motivates that any unbalanced protocol tree can be balanced.

<a id="pdf-fa052d8c95c0-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.95 -->
**Theorem 1.3.** If $\pi$ is a protocol with $\ell$ leaves, then there is a protocol computing the outcome $\pi(x, y)$ with communication at most $2\log_{3/2} \ell$.

<a id="pdf-fa052d8c95c0-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.97 -->
**Lemma 1.4.** In every protocol tree with ℓ leaves, there is a vertex v such that the subtree rooted at v contains r leaves with ℓ/3 ≤ r ≤ 2ℓ/3.

<a id="pdf-fa052d8c95c0-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.95 -->
**Proof.** Let r be the root and define a sequence r = v₁, v₂, … where v₁ is the root and v_{i+1} is the child of v_i having the most leaves beneath it. Let ℓ_i be the number of leaves in the subtree rooted at v_i. By choice of v_i, ℓ_{i+1} ≥ ℓ_i/2 and ℓ_{i+1} < ℓ_i. Since ℓ₁ = ℓ and the sequence decreases until reaching 1, some i satisfies ℓ/3 ≤ ℓ_i ≤ 2ℓ/3. ∎

<a id="pdf-fa052d8c95c0-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.92 -->
Balanced protocol: repeatedly pick a vertex v per Lemma 1.4; each party checks whether its input is consistent with the whole path up to v. If consistent, recurse on the subtree rooted at v; otherwise delete v (replace v's parent by v's sibling) and continue. Each step exchanges two bits and reduces the number of leaves by a factor of at least 2/3, so at most log_{3/2} ℓ steps occur; output the unique remaining leaf.

<a id="pdf-fa052d8c95c0-p004-b006"></a>
<!-- pdf-source: page=4; block=6; confidence=0.96 -->
**Rectangles.** A rectangle is a subset R = A × B ⊆ X × Y with A ⊆ X and B ⊆ Y. (For k-party protocols, a rectangle is the cartesian product of k sets.)

<a id="pdf-fa052d8c95c0-p004-b007"></a>
<!-- pdf-source: page=4; block=7; confidence=0.96 -->
**Lemma 1.5.** R is a rectangle if and only if whenever (x, y), (x′, y′) ∈ R then (x′, y), (x, y′) ∈ R.

<a id="pdf-fa052d8c95c0-p004-b008"></a>
<!-- pdf-source: page=4; block=8; confidence=0.90 -->
**Proof.** (⇒) If R = A × B, then (x, y), (x′, y′) ∈ R gives x, x′ ∈ A and y, y′ ∈ B, so (x, y′), (x′, y) ∈ A × B ⊆ R. (⇐) If R has the stated closure property: if R is empty it is a rectangle; otherwise fix (x, y) ∈ R. [Construction continues on page 5.]

<a id="pdf-fa052d8c95c0-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.90 -->
**Proof (cont.).** Define A = {x′ : (x′, y) ∈ R} and B = {y′ : (x, y′) ∈ R}. By the closure property, R ⊆ A × B, and for every (x′, y′) with x′ ∈ A, y′ ∈ B one has (x′, y′) ∈ R, so A × B ⊆ R. Hence R = A × B. ∎

<a id="pdf-fa052d8c95c0-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.93 -->
For each vertex v, let R_v ⊆ X × Y be the set of inputs (x, y) whose execution passes through v. For the root r, R_r = X × Y is a rectangle. If R_v = A × B is a rectangle with children u, w, and the first party acts at v moving to u when f_v(x) = 0, set A₀ = {x ∈ A : f_v(x) = 0}, A₁ = {x ∈ A : f_v(x) = 1}. Then A₀, A₁ partition A, R_u = A₀ × B, R_w = A₁ × B, so R_u, R_w are rectangles partitioning R_v. Inductively every R_v is a rectangle.

<a id="pdf-fa052d8c95c0-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.96 -->
**Lemma 1.6.** For every vertex v in the protocol tree, R_v is a rectangle. Moreover, the rectangles associated with all leaves form a partition of the inputs.

<a id="pdf-fa052d8c95c0-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.94 -->
**Definition (monochromatic).** A rectangle R is monochromatic under g if g is constant on R, i.e. g(x, y) = g(x′, y′) for all (x, y), (x′, y′) ∈ R. It is 1-monochromatic if g takes value 1 on R (analogously 0-monochromatic).

<a id="pdf-fa052d8c95c0-p005-b005"></a>
<!-- pdf-source: page=5; block=5; confidence=0.92 -->
Argument: if $\pi$ computes $g : \mathcal{X} \times \mathcal{Y} \to \{0,1\}$ and $v$ is a leaf, then any two inputs $(x, y), (x', y') \in R_v$ must satisfy $g(x, y) = g(x', y')$, since $\pi$ gives them the same output; hence each leaf's rectangle is monochromatic under $g$. Combined with Lemmas 1.2 and 1.6:

**Theorem 1.7.** If the communication complexity of $g : \mathcal{X} \times \mathcal{Y} \to \{0,1\}$ is $c$, then $\mathcal{X} \times \mathcal{Y}$ can be partitioned into at most $2^c$ monochromatic rectangles.

<a id="pdf-fa052d8c95c0-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.92 -->
**From Rectangles to Protocols.** Not every partition of the inputs arises from a protocol (cf. Figure 1.5), but a small monochromatic-rectangle cover yields an efficient protocol.

**Theorem 1.8.** If g admits 2^c monochromatic rectangles whose union is X × Y, then there is a protocol computing g with O(c²) bits of communication. (Reference: Yannakakis 1991; Aho et al. 1983. An efficient partition of the 1's also yields an efficient protocol — Exercise 1.2.)

<a id="pdf-fa052d8c95c0-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.93 -->
**Definition.** Two rectangles R = A × B and R′ = A′ × B′ intersect horizontally if A ∩ A′ ≠ ∅, and intersect vertically if B ∩ B′ ≠ ∅. If x ∈ A ∩ A′ and y ∈ B ∩ B′, then (x, y) ∈ R and (x, y) ∈ R′.

**Fact 1.9.** If R, R′ are disjoint rectangles, they cannot intersect both horizontally and vertically.

<a id="pdf-fa052d8c95c0-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.90 -->
Parties hold (x, y) and a collection of monochromatic rectangles ℛ covering all inputs; goal is to find R_{x,y} ∈ ℛ with (x, y) ∈ R_{x,y}. At each step a party announces the name of a rectangle R = A × B ∈ ℛ consistent with its input. If Alice announces R then x ∈ A, so both may discard every rectangle in ℛ that does not vertically intersect R; if Bob announces R, discard every rectangle that does not horizontally intersect R. Any rectangle containing (x, y) is never discarded. The claim (to be shown) is that some announceable R always lets many rectangles be discarded.

<a id="pdf-fa052d8c95c0-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.95 -->
**Definition.** Let ℛ₀ = {R ∈ ℛ : g(R) = 0} be the rectangles of value 0 and ℛ₁ = {R ∈ ℛ : g(R) = 1} those of value 1.

<a id="pdf-fa052d8c95c0-p006-b005"></a>
<!-- pdf-source: page=6; block=5; confidence=0.93 -->
**Definition 1.10.** A rectangle R = (A × B) ∈ ℛ₀ is:
- **horizontally good** if x ∈ A and R horizontally intersects at most half of the rectangles in ℛ₁; and
- **vertically good** if y ∈ B and R vertically intersects at most half of the rectangles in ℛ₁.

<a id="pdf-fa052d8c95c0-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.86 -->
**Figure 1.7 (Protocol from monochromatic rectangle covers).** Input: Alice knows x∈X, Bob knows y∈Y; both know a set R = R₀ ∪ R₁ of monochromatic rectangles whose union contains (x,y). Output: g(x,y). While R₁ ≠ ∅: if ∃ R∈R₀ horizontally good, Alice sends Bob the name of R and both discard every R₁-rectangle that does not horizontally intersect R; else if ∃ R∈R₀ vertically good, Bob sends Alice the name of R and both discard every R₁-rectangle that does not vertically intersect R; else the parties output 1 and halt. If the loop terminates with R₁ empty, the parties output 0. (Attributed to Göös et al., 2015.)

<a id="pdf-fa052d8c95c0-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.82 -->
**Argument.** Alice can compute which rectangles are horizontally good and Bob which are vertically good, with no communication. If g(x,y)=0, some Rₓ,ᵧ∈R₀ contains (x,y). Since R₁-rectangles are disjoint from Rₓ,ᵧ, Fact 1.9 gives that each intersects Rₓ,ᵧ horizontally or vertically but not both. Hence at most half of R₁ intersects it horizontally, or at most half vertically; any such rectangle is consistent with both inputs.

<a id="pdf-fa052d8c95c0-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.95 -->
**Claim 1.11.** Any rectangle of R₀ that contains (x,y) is either horizontally good or vertically good.

<a id="pdf-fa052d8c95c0-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.88 -->
**Complexity analysis.** Each step names a horizontally- or vertically-good rectangle if one exists, discarding half of R₁; if none exists, no R₁-rectangle covers (x,y), so R₀ covers it and g(x,y)=1. A rectangle survives at most c+1 discards and a rectangle name costs c bits, so the communication complexity is O(c²).

<a id="pdf-fa052d8c95c0-p007-b005"></a>
<!-- pdf-source: page=7; block=5; confidence=0.88 -->
**Open Problem 1.12.** There is a function g whose inputs can be partitioned into 2^c monochromatic rectangles, yet no protocol computes g using o(c^{3/2}) bits of communication. What are the best parameters obtainable in Theorem 1.8?

<a id="pdf-fa052d8c95c0-p007-b006"></a>
<!-- pdf-source: page=7; block=6; confidence=0.85 -->
**Some lower bounds.** To show a function lacks an efficient protocol, use Theorem 1.7: proving the inputs cannot be partitioned into 2^c monochromatic rectangles, or lack large monochromatic rectangles, proves no c-bit protocol computes it.

<a id="pdf-fa052d8c95c0-p007-b007"></a>
<!-- pdf-source: page=7; block=7; confidence=0.93 -->
**Equality (definition).** Under the heading "Using bounds on the size of monochromatic rectangles," define EQ: {0,1}^n × {0,1}^n → {0,1} by EQ(x,y) = 1 if x = y and 0 otherwise. (1.1)

<a id="pdf-fa052d8c95c0-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.86 -->
**Equality (continued).** Alice sending her input yields an (n+1)-bit protocol. Bounding by absence of large monochromatic rectangles fails: EQ has a large 0-monochromatic rectangle R = {(x,y) : x₁=0, y₁=1} of density 1/4 (EQ=0 throughout). Instead, one shows EQ has no large 1-monochromatic rectangle.

<a id="pdf-fa052d8c95c0-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.90 -->
**Argument.** If x ≠ x', then (x,x) and (x,x') cannot lie in the same monochromatic rectangle: by Lemma 1.5, (x,x') would then belong to it, and monochromaticity would force EQ(x,x') = EQ(x,x) = 1, contradicting x ≠ x'.

<a id="pdf-fa052d8c95c0-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.96 -->
**Claim 1.13.** Every 1-monochromatic rectangle of EQ has size at most 1.

<a id="pdf-fa052d8c95c0-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.92 -->
**Theorem 1.14.** The deterministic communication complexity of EQ is at least n+1. There are 2^n inputs x with EQ(x,x)=1, and each requires its own size-1 rectangle, so ≥ 2^n rectangles are needed to cover the 1's.

<a id="pdf-fa052d8c95c0-p008-b005"></a>
<!-- pdf-source: page=8; block=5; confidence=0.90 -->
**Disjointness.** Define $\mathrm{Disj}: 2^{[n]} \times 2^{[n]} \to \{0,1\}$ by $\mathrm{Disj}(X,Y)=1$ if $X\cap Y=\emptyset$ and $0$ otherwise. (1.2) Alice sending $X$ gives an $(n+1)$-bit protocol. Disj has large monochromatic rectangles but no large 1-monochromatic rectangle: for a 1-monochromatic rectangle $R = A\times B$, the unions $X' = \bigcup_{X\in A} X$ and $Y' = \bigcup_{Y\in B} Y$ must be disjoint, so $|X'|+|Y'| \le n$; since $|A| \le 2^{|X'|}$ and $|B| \le 2^{|Y'|}$, we have $|R| = |A||B| \le 2^n$.

<a id="pdf-fa052d8c95c0-p008-b006"></a>
<!-- pdf-source: page=8; block=6; confidence=0.95 -->
**Claim 1.15.** Every 1-monochromatic rectangle of Disj has size at most 2^n.

<a id="pdf-fa052d8c95c0-p008-b007"></a>
<!-- pdf-source: page=8; block=7; confidence=0.90 -->
**Counting.** The number of disjoint pairs (X,Y) is exactly 3^n, since each universe element is either in X, in Y, or in neither.

<a id="pdf-fa052d8c95c0-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.88 -->
**Argument (continued).** With 3 choices per element there are 3^n disjoint pairs; since each 1-monochromatic rectangle has size ≤ 2^n, at least 3^n/2^n = 2^{(log 3 − 1)n} monochromatic rectangles are needed to cover the 1's of Disj.

<a id="pdf-fa052d8c95c0-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.93 -->
**Theorem 1.16.** The deterministic communication complexity of Disj is at least (log 3 − 1)n. (A stronger lower bound is proved later.)

<a id="pdf-fa052d8c95c0-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.85 -->
**Richness.** For asymmetric protocols, where Alice's and Bob's communication are bounded separately, the richness concept (Miltersen et al., 1998) is used.

<a id="pdf-fa052d8c95c0-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.78 -->
**Definition 1.17.** A function $g: \mathcal{X}\times\mathcal{Y} \to \{0,1\}$ is said to be $(u,v)$-rich if there is a set $V \subseteq \mathcal{Y}$, $|V| = v$, such that for all $y \in V$ there is a set $U_y \subseteq \mathcal{X}$ with $g(U_y, y) = 1$.

<a id="pdf-fa052d8c95c0-p009-b005"></a>
<!-- pdf-source: page=9; block=5; confidence=0.82 -->
**Lemma 1.18.** If g: X×Y → {0,1} is (u,v)-rich and there is a protocol computing g in which Alice sends at most a bits and Bob sends at most b bits, then g admits a (u/2^a) × (v/2^{a+b}) 1-monochromatic rectangle.

<a id="pdf-fa052d8c95c0-p009-b006"></a>
<!-- pdf-source: page=9; block=6; confidence=0.85 -->
**Proof.** By induction on the protocol length. Base case: if the protocol does not communicate at all, then $g(x,y)=1$ for all $x\in\mathcal{X}, y\in\mathcal{Y}$, and the statement holds. If Bob sends the first bit, then Bob partitions $\mathcal{Y} = \mathcal{Y}_0 \cup \mathcal{Y}_1$; one of these two sets has $v/2$ of the inputs $y$ that make $g$ rich, and by induction it contains a $\frac{u}{2^a} \times \frac{v/2}{2^{a+b-1}}$ 1-monochromatic rectangle, as required. If Alice sends the first bit, then it partitions $\mathcal{X}$ into two sets $\mathcal{X}_0, \mathcal{X}_1$; every input $y$ with $u$ 1's has $u/2$ of them in $\mathcal{X}_0$ or in $\mathcal{X}_1$, so there are $v/2$ choices of $y$ with $u/2$ 1's for $g$ restricted to $\mathcal{X}_0 \times \mathcal{Y}$ or to $\mathcal{X}_1 \times \mathcal{Y}$, and by induction there is a 1-monochromatic rectangle of dimensions $\frac{u/2}{2^{a-1}} \times \frac{v/2}{2^{a-1+b}}$, as required.

<a id="pdf-fa052d8c95c0-p009-b007"></a>
<!-- pdf-source: page=9; block=7; confidence=0.85 -->
**Lopsided Disjointness.** Alice is given X ⊆ [n] with |X| = k < n and Bob a set Y ⊆ [n]; they decide disjointness. The obvious protocol has Alice send X, costing log(n choose k) bits. Question: what is the complexity when Alice must send far fewer than log(n choose k) bits? The lower bound analyzes rectangles of a special shape, restricting attention to a special family of sets. (Chapter 2 shows the complexity is at least log(n choose k).)

<a id="pdf-fa052d8c95c0-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.72 -->
Setup for a disjointness lower bound between Alice and Bob. Let $n = 2kt$. Input $Y$ contains exactly one element of each pair $\{2i-1, 2i\}$; input $X$ contains exactly one element of each block $\{2t(i-1)+1, \dots, 2ti\}$. (Figure 1.8 illustrates $n=12$, $k=3$, $t=2$.) A margin note records that $|A_k| \ge 1/k$ follows from the AM–GM inequality.

<a id="pdf-fa052d8c95c0-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.95 -->
**Claim 1.19.** If $A \times B$ is a 1-monochromatic rectangle, then $|B| \le 2^{\,kt - k|A|^{1/k}}$.

<a id="pdf-fa052d8c95c0-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.60 -->
**Proof.** The union $\bigcup_{X \in A} X$ has at least $k|A|^{1/k}$ elements: if it has $a_i$ elements in block $\{2t(i-1)+1,\dots,2ti\}$, then $\big|\bigcup_{X\in A} X\big| = \sum_{i=1}^{k} a_i \ge k\big(\prod_{i=1}^{k} a_i\big)^{1/k} \ge k|A|^{1/k}$ by AM–GM (since $\prod a_i \ge |A|$). This union intersects every set of $B$, so it determines at least $k|A|^{1/k}$ forced coordinates in each set of $B$; hence the number of admissible $B$-sets is at most $2^{\,kt - k|A|^{1/k}}$. $\square$

<a id="pdf-fa052d8c95c0-p010-b004"></a>
<!-- pdf-source: page=10; block=4; confidence=0.86 -->
**Derivation.** The disjointness matrix here is at least $(t^k, 2^{kt})$-rich, since every choice of $Y$ allows for $t^k$ possible choices of $X$ that are disjoint. By Lemma 1.18, any protocol where Alice sends $a$ bits and Bob sends $b$ bits induces a 1-monochromatic rectangle of dimensions $t^k/2^{a} \times 2^{\,kt-a-b}$, so Claim 1.19 gives $2^{\,kt-a-b} \le 2^{\,kt - kt/2^{a/k}}$, hence $a+b \ge kt/2^{a/k} = n/2^{\,a/k+1}$.

<a id="pdf-fa052d8c95c0-p010-b005"></a>
<!-- pdf-source: page=10; block=5; confidence=0.85 -->
**Theorem 1.20.** If $X, Y \subseteq [n]$ with $|X| = |Y| = k$, and in a protocol computing $\mathrm{Disj}(X,Y)$ Alice sends at most $a$ bits and Bob at most $b$ bits, then $a + b \ge \dfrac{n}{2^{\,a/k+1}}$.

<a id="pdf-fa052d8c95c0-p010-b006"></a>
<!-- pdf-source: page=10; block=6; confidence=0.85 -->
Span problem: Alice holds a vector $x \in \{0,1\}^{n}$, Bob holds an $n/2$-dimensional subspace $V \subseteq \{0,1\}^{n}$, and the goal is to decide whether $x \in V$. As with disjointness, the argument first rules out 1-monochromatic rectangles of a certain size.

<a id="pdf-fa052d8c95c0-p010-b007"></a>
<!-- pdf-source: page=10; block=7; confidence=0.95 -->
**Claim 1.21.** If $A \times B$ is a 1-monochromatic rectangle, then $|B| \le 2^{\,n^2/2 - n\log|A|}$.

<a id="pdf-fa052d8c95c0-p010-b008"></a>
<!-- pdf-source: page=10; block=8; confidence=0.50 -->
**Proof.** The $x$'s in the rectangle span a subspace of dimension at least $\log|A|$. The number of $n/2$-dimensional subspaces containing this span is at most $\binom{2^{n}}{\,\cdot\,}$-type count bounded by $\big(2^{\,n-\log|A|}\big)^{n/2} \le 2^{\,n^2/2 - n\log|A|}$, bounding $|B|$. $\square$

<a id="pdf-fa052d8c95c0-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.90 -->
**Derivation.** The span problem is at least $(2^{n/2},\, 2^{n^2/4}/n!)$-rich: there are at least $2^{n^2/4}/n!$ subspaces, each containing $2^{n/2}$ vectors. Applying Lemma 1.18 and Claim 1.21 to a protocol with $a$ bits from Alice and $b$ from Bob gives $2^{\,n^2/4-a-b}/n! \le 2^{\,n^2/2 - n\log 2^{\,n/2-a}}$, which simplifies through $n^2/4 - a - b - n\log n \le na$ to $b \ge n^2/4 - a(n+1) - n\log n$.

<a id="pdf-fa052d8c95c0-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.85 -->
**Theorem 1.22.** If Alice sends $a$ bits and Bob sends $b$ bits to solve the span problem, then $b \ge \dfrac{n^2}{4} - a(n+1) - n\log n$.

<a id="pdf-fa052d8c95c0-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.90 -->
**Using Fooling Sets.**

<a id="pdf-fa052d8c95c0-p011-b004"></a>
<!-- pdf-source: page=11; block=4; confidence=0.85 -->
**Definition (Greater-than).** $\mathrm{GT} : [n] \times [n] \to \{0,1\}$ with
$$\mathrm{GT}(x,y) = \begin{cases} 1 & \text{if } x > y,\\ 0 & \text{otherwise.} \end{cases} \qquad (1.3)$$
The trivial protocol uses $\lceil \log n \rceil$ bits, shown to be tight. Rectangle-counting fails here because $\mathrm{GT}$ has large 0-monochromatic rectangles (e.g. $\{(x,y): x < n/2,\, y > n/2\}$) and large 1-monochromatic rectangles (e.g. $\{(x,y): x > n/2,\, y < n/2\}$); instead a fooling set $S = \{(x,x)\}$ is used.

<a id="pdf-fa052d8c95c0-p011-b005"></a>
<!-- pdf-source: page=11; block=5; confidence=0.85 -->
**Claim 1.23.** No two points of $S = \{(x,x)\}$ lie in the same monochromatic rectangle. Indeed, if $R$ is monochromatic and $(x,x),(x',x') \in R$ with $x < x'$, then $R$ being a rectangle forces $(x',x) \in R$, contradicting monochromaticity since $\mathrm{GT}(x',x) \neq \mathrm{GT}(x',x')$. Hence at least $n$ monochromatic rectangles are required.

<a id="pdf-fa052d8c95c0-p011-b006"></a>
<!-- pdf-source: page=11; block=6; confidence=0.90 -->
**Theorem 1.24.** The deterministic communication complexity of $\mathrm{GT}$ is at least $\log n$.

<a id="pdf-fa052d8c95c0-p011-b007"></a>
<!-- pdf-source: page=11; block=7; confidence=0.85 -->
A tighter disjointness bound uses the fooling set $S = \{(X, X^{c})\}$, pairing each set with its complement. No monochromatic rectangle contains two pairs $(X,X^{c}),(Y,Y^{c})$ with $X \neq Y$: it would then contain $(X, Y^{c})$, which intersects (since $X \neq Y$), whereas the diagonal pairs are disjoint.

<a id="pdf-fa052d8c95c0-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.85 -->
**Theorem 1.25.** The deterministic communication complexity of disjointness is at least $n + 1$. (The fooling set $S$ has $2^{n}$ pairs, each needing its own rectangle, plus at least one more.)

<a id="pdf-fa052d8c95c0-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.90 -->
**Krapchenko's Method.**

<a id="pdf-fa052d8c95c0-p012-b003"></a>
<!-- pdf-source: page=12; block=3; confidence=0.85 -->
**Definition.** Let $\mathcal{X} = \{x \in \{0,1\}^{n} : \sum_i x_i = 0 \bmod 2\}$ and $\mathcal{Y} = \{y \in \{0,1\}^{n} : \sum_i y_i = 1 \bmod 2\}$. For every $x \in \mathcal{X}$, $y \in \mathcal{Y}$ there is an index $i$ with $x_i \neq y_i$. Alice holds $x$, Bob holds $y$, and they must find such an index $i$.

<a id="pdf-fa052d8c95c0-p012-b004"></a>
<!-- pdf-source: page=12; block=4; confidence=0.85 -->
**Protocol.** Beyond Alice sending her whole string, binary search does better. Since $\sum_{i \le n/2} x_i + \sum_{i > n/2} x_i \neq \sum_{i \le n/2} y_i + \sum_{i > n/2} y_i \pmod 2$, Alice and Bob exchange $\sum_{i \le n/2} x_i \bmod 2$ and $\sum_{i \le n/2} y_i \bmod 2$. If these differ, a differing index lies in the first half; otherwise it lies in the second half. Each step uses 2 bits and halves the input, giving communication complexity $2\log n$.

<a id="pdf-fa052d8c95c0-p012-b005"></a>
<!-- pdf-source: page=12; block=5; confidence=0.80 -->
A trivial $\log n$ lower bound holds (bits to write the answer); the goal is to prove $2\log n$ via a fooling-set variant. Let $S = \{(x,y) \in \mathcal{X} \times \mathcal{Y} : x, y \text{ differ in exactly one coordinate}\}$, so $|S| = n \cdot 2^{n-1}$ (choose $x \in \mathcal{X}$, flip any one of $n$ coordinates). A margin note observes at least $n$ rectangles are needed to cover pairs of type $(0, e_i)$. Rather than bounding elements per rectangle, one shows a rectangle with many elements of $S$ must be large.

<a id="pdf-fa052d8c95c0-p012-b006"></a>
<!-- pdf-source: page=12; block=6; confidence=0.88 -->
**Claim 1.26.** If a monochromatic rectangle $R$ contains $r$ elements of $S$, then $|R| \ge r^2$.

<a id="pdf-fa052d8c95c0-p012-b007"></a>
<!-- pdf-source: page=12; block=7; confidence=0.82 -->
**Proof (begins).** The key observation here is that two elements $(x,y),(x,y') \in S$ cannot be in the same monochromatic rectangle. For if the rectangle was labeled $i$, then $(x,y),(x,y')$ must disagree in the $i$'th coordinate, but... [text cut off].

<a id="pdf-fa052d8c95c0-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.85 -->
**Proof (continued).** Similarly, we cannot have two distinct elements $(x,y),(x',y) \in S$ in the same monochromatic rectangle. Thus, if $R=A\times B$ has $r$ elements of $S$, then $|A|\ge r$ and $|B|\ge r$, proving that $|R|\ge r^2$. Now suppose there are $t$ monochromatic rectangles that cover the set $S$, and the $i$'th rectangle covers $r_i$ elements of $S$. Then $|S| = \sum_{i=1}^t r_i$, but since the rectangles are disjoint, $2^{2n-2}\ge\sum_{i=1}^t r_i^2$. Using these facts and the Cauchy–Schwarz inequality, $2^{2n-2} \ge \sum_{i=1}^t r_i^2 \ge \left(\sum_{i=1}^t r_i/\sqrt t\right)^2 = n^2 2^{2n-2}/t$, proving that $t\ge n^2$. This shows that the binary search protocol is the best one can do.

<a id="pdf-fa052d8c95c0-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.90 -->
## Rectangle Covers

Motivation (compressed): measure function complexity by the number of monochromatic rectangles needed to cover all inputs.

<a id="pdf-fa052d8c95c0-p013-b003"></a>
<!-- pdf-source: page=13; block=3; confidence=0.95 -->
**Definition 1.27.** A boolean function has a **1-cover of size $C$** if there are $C$ monochromatic rectangles whose union is all inputs evaluating to $1$. It has a **0-cover of size $C$** if there are $C$ monochromatic rectangles whose union is all inputs evaluating to $0$.

<a id="pdf-fa052d8c95c0-p013-b004"></a>
<!-- pdf-source: page=13; block=4; confidence=0.90 -->
By **Theorem 1.7**, a protocol with communication $c$ yields a 1-cover and a 0-cover each of size at most $2^c$. Conversely, **Theorem 1.8** shows small covers give small communication.

<a id="pdf-fa052d8c95c0-p013-b005"></a>
<!-- pdf-source: page=13; block=5; confidence=0.90 -->
For the disjointness function (defined in (1.2)), define for $i=1,\dots,n$ the rectangle $R_i=\{(X,Y): i\in X,\ i\in Y\}$. Then $R_1,\dots,R_n$ form a **0-cover of size $n$**, while the communication complexity of disjointness is linear, $n+1$. However (shown in a later chapter) any **1-cover of disjointness requires $2^{\Omega(n)}$ rectangles**.

<a id="pdf-fa052d8c95c0-p013-b006"></a>
<!-- pdf-source: page=13; block=6; confidence=0.85 -->
The **$k$-disjointness** function gives Alice and Bob sets $X,Y\subseteq[n]$ of size $k$; its communication complexity is treated in Chapter 2. (Compressed) Rectangle covers correspond to non-deterministic communication complexity: a 1-cover lets the players nondeterministically guess a covering rectangle for a 1-input, and any non-deterministic protocol corresponds to a 1-cover.

<a id="pdf-fa052d8c95c0-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.90 -->
The communication complexity of $k$-disjointness is at least $\log\binom{n}{k}\approx k\log(n/k)$. As above, there is a 0-cover of $k$-disjointness using $n$ rectangles.

<a id="pdf-fa052d8c95c0-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.90 -->
**Claim 1.28.** $k$-disjointness has a 1-cover of size $2^{2k}\ln\!\big(\binom{n}{k}^2\big)$.

<a id="pdf-fa052d8c95c0-p014-b003"></a>
<!-- pdf-source: page=14; block=3; confidence=0.90 -->
**Proof.** By the probabilistic method: sample a random 0-rectangle by choosing a random set $S\subseteq[n]$ and taking $R=\{(X,Y): X\subseteq S,\ Y\subseteq [n]\setminus S\}$. Sample $t=2^{2k}\ln\binom{n}{k}^2$ such rectangles independently. The probability a fixed disjoint pair $(X,Y)$ lies in one rectangle is $2^{-2k}$, so the probability it is excluded from all $t$ is $(1-2^{-2k})^t \le e^{-2^{-2k}t} < \binom{n}{k}^{-2}$ (using $1-x\le e^{-x}$ for $x\ge0$). Since there are at most $\binom{n}{k}^2$ disjoint pairs, the probability that any disjoint pair is excluded is $<1$, so some choice of $t$ rectangles covers all 1-inputs. $\square$

<a id="pdf-fa052d8c95c0-p014-b004"></a>
<!-- pdf-source: page=14; block=4; confidence=0.90 -->
Setting $k=\log n$ gives a 1-cover with $t=2^{2\log n}\ln\binom{n}{\log n}=O(n^2\log^2 n)$ rectangles, showing **Theorem 1.8 is tight** for rectangle covers.

<a id="pdf-fa052d8c95c0-p014-b005"></a>
<!-- pdf-source: page=14; block=5; confidence=0.90 -->
## Direct-sums in Communication Complexity

Question (compressed): if computing $g$ needs $c$ bits, how much is needed to compute $k$ independent copies?

<a id="pdf-fa052d8c95c0-p014-b006"></a>
<!-- pdf-source: page=14; block=6; confidence=0.92 -->
For $g:\{0,1\}^n\times\{0,1\}^n\to\{0,1\}$, define $g^k:(\{0,1\}^n)^k\times(\{0,1\}^n)^k\to\{0,1\}^k$ by $g^k((x_1,\dots,x_k),(y_1,\dots,y_k)) = (g(x_1,y_1), g(x_2,y_2),\dots,g(x_k,y_k))$.

<a id="pdf-fa052d8c95c0-p014-b007"></a>
<!-- pdf-source: page=14; block=7; confidence=0.95 -->
**Theorem 1.29** (Feder et al., 1995). If $g$ requires $c$ bits of communication, then $g^k$ requires at least $k(\sqrt{c}-\log n-1)$ bits of communication.

<a id="pdf-fa052d8c95c0-p014-b008"></a>
<!-- pdf-source: page=14; block=8; confidence=0.75 -->
Even computing the two bits $\bigwedge_{i=1}^k g(x_i,y_i)$ and $\bigvee_{i=1}^k g(x_i,y_i)$ requires $k(\sqrt{c-\log n}-1)$ bits (Exercise 1.11).

<a id="pdf-fa052d8c95c0-p014-b009"></a>
<!-- pdf-source: page=14; block=9; confidence=0.90 -->
**Lemma 1.30.** If $g^k$ can be computed with $\ell$ bits of communication, then the inputs to $g$ can be covered by $2n^2\cdot 2^{\ell/k}$ monochromatic rectangles.

<a id="pdf-fa052d8c95c0-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.65 -->
**Proof (Theorem 1.29).** Theorem 1.8 and Lemma 1.30 imply $g$ has a protocol with communication $(\ell/k+\log n+1)^2$. Thus $c\le(\ell/k+\log n+1)^2$, which rearranges to $\ell\ge k(\sqrt c-\log n-1)$, as required. $\square$

<a id="pdf-fa052d8c95c0-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.90 -->
**Proof (Lemma 1.30).** Find covering rectangles iteratively. Let $S\subseteq\{0,1\}^n\times\{0,1\}^n$ be the inputs to $g$ not yet covered; initially $S$ is all inputs.

<a id="pdf-fa052d8c95c0-p015-b003"></a>
<!-- pdf-source: page=15; block=3; confidence=0.90 -->
**Claim 1.31.** There is a rectangle that is monochromatic under $g$ and covers at least $2^{-\ell/k}|S|$ of the inputs from $S$.

<a id="pdf-fa052d8c95c0-p015-b004"></a>
<!-- pdf-source: page=15; block=4; confidence=0.88 -->
**Proof.** Since $g^k$ is computed with $\ell$ bits, by Theorem 1.7 the set $S^k$ is covered by $2^\ell$ monochromatic rectangles, so some rectangle $R$ covers at least $2^{-\ell}|S|^k$ of these inputs. For each $i$ define $R_i=\{(x,y)\in\{0,1\}^n\times\{0,1\}^n : \exists (a,b)\in R,\ a_i=x,\ b_i=y\}$, which is a rectangle (as $R$ is) and is monochromatic under $g$ (as $R$ is monochromatic under $g^k$). Since $|R|\le\prod_{i=1}^k|R_i|$, we have $\prod_{i=1}^k|R_i|\ge 2^{-\ell}|S|^k$, so some $i$ satisfies $|R_i|\ge 2^{-\ell/k}|S|$. $\square$

<a id="pdf-fa052d8c95c0-p015-b005"></a>
<!-- pdf-source: page=15; block=5; confidence=0.85 -->
Repeatedly apply Claim 1.31 until all inputs to $g$ are covered. After $2n^2\cdot 2^{\ell/k}$ steps, the number of uncovered inputs is at most
$$2^{2n}(1-2^{-\ell/k})^{2n^2\cdot 2^{\ell/k}} \le 2^{2n}e^{-2^{-\ell/k}\cdot 2n^2\cdot 2^{\ell/k}} = 2^{2n}e^{-2n^2} < 1,$$
using $1-x\le e^{-x}$ for $x\ge0$. Hence the process stops after at most $2n^2\cdot 2^{\ell/k}$ steps. $\square$

<a id="pdf-fa052d8c95c0-p015-b006"></a>
<!-- pdf-source: page=15; block=6; confidence=0.92 -->
**Exercise 1.1.** Define the inner product of $n$-bit strings $x,y$ as $\sum_{i=1}^n x_iy_i \bmod 2$. Using linear algebra, show inner-product has no 0-rectangle larger than $2^n$, and conclude its communication complexity is $\Omega(n)$.

<a id="pdf-fa052d8c95c0-p015-b007"></a>
<!-- pdf-source: page=15; block=7; confidence=0.92 -->
**Exercise 1.2.** Using ideas from Yannakakis's protocol, show that if $g:X\times Y\to\{0,1\}$ has $g^{-1}(1)$ partitionable into $2^c$ rectangles, then $g$ has communication complexity at most $O(c^2)$.

<a id="pdf-fa052d8c95c0-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.80 -->
Running header: "communication complexity", page 30. Exercises on deterministic communication complexity.

<a id="pdf-fa052d8c95c0-p016-b002"></a>
<!-- pdf-source: page=16; block=2; confidence=0.94 -->
**Exercise 1.3.** Suppose Alice and Bob each get a size-$k$ subset of the elements $[n]$, and want to know whether these sets intersect or not. Use the fooling set method to show that at least $\log(\lfloor n/k\rfloor)$ bits are required.

<a id="pdf-fa052d8c95c0-p016-b003"></a>
<!-- pdf-source: page=16; block=3; confidence=0.90 -->
**Exercise 1.4.** Alice gets $x \in \{0,1\}^n$ with more 0's than 1's; Bob gets $y \in \{0,1\}^n$ with more 1's than 0's. They must find a coordinate $i$ with $x_i \neq y_i$. Using Krapchenko's method, show at least $2\log n$ bits of communication are required.

<a id="pdf-fa052d8c95c0-p016-b004"></a>
<!-- pdf-source: page=16; block=4; confidence=0.92 -->
**Exercise 1.5.** Show that almost all functions $f : \{0,1\}^n \times \{0,1\}^n \to \{0,1\}$ require communication $\Omega(n)$, where Alice gets $x \in \{0,1\}^n$, Bob gets $y \in \{0,1\}^n$, and they must evaluate $f(x,y)$.

<a id="pdf-fa052d8c95c0-p016-b005"></a>
<!-- pdf-source: page=16; block=5; confidence=0.88 -->
**Exercise 1.6.** Let $X$ and $Y$ be families of subsets of $[n]$ such that for all $x \in X$, $y \in Y$ the intersection satisfies $|x \cap y| \le 1$. Define the communication problem: Alice receives $x \in X$, Bob receives $y \in Y$, and they evaluate $f : X \times Y \to \{0,1\}$ given by $f(x,y) = |x \cap y|$. Show the deterministic complexity of $f$ is $O(\log^2 n)$.

<a id="pdf-fa052d8c95c0-p016-b006"></a>
<!-- pdf-source: page=16; block=6; confidence=0.92 -->
**Exercise 1.7.** Alice and Bob receive subsets $X, Y \subseteq [n]$ and wish to output the median of $X \cup Y$. Give a deterministic protocol using $O(\log n)$ bits, and show no protocol can do asymptotically better.

<a id="pdf-fa052d8c95c0-p016-b007"></a>
<!-- pdf-source: page=16; block=7; confidence=0.82 -->
**Exercise 1.8.** Consider the partial function $f : \{0,1\}^n \times \{0,1\}^n \to \{0,1\}$ where each party's input is interpreted as two $n/2$-bit strings, and
$$f(x,x',y,y') = \begin{cases} 1 & \text{if } x = y \text{ and } x' \neq y', \\ 0 & \text{if } x \neq y \text{ and } x' = y'. \end{cases}$$
Show there are $2^n$ monochromatic rectangles under $f$. Using fooling sets, show the communication complexity of $f$ is at least $\Omega(n)$. This proves an analogue of Theorem 1.8 fails for partial functions.

<a id="pdf-fa052d8c95c0-p017-b001"></a>
<!-- pdf-source: page=17; block=1; confidence=0.80 -->
Running header: "deterministic protocols", page 31. Continued exercises.

<a id="pdf-fa052d8c95c0-p017-b002"></a>
<!-- pdf-source: page=17; block=2; confidence=0.85 -->
**Exercise 1.9.** For a boolean function $g$, define $g^{\wedge k}$ by $g^{\wedge k}(x_1,\dots,x_k,y_1,\dots,y_k) = \bigwedge_{i=1}^k g(x_i,y_i)$. Show that if $g^{\wedge k}$ has a 1-cover of size $2^{\ell}$, then $g$ has a 1-cover of size $2^{\ell/k}$.

<a id="pdf-fa052d8c95c0-p017-b003"></a>
<!-- pdf-source: page=17; block=3; confidence=0.78 -->
**Exercise 1.10.** (Attributed to Alon and Orlitsky, 1995.) Show that an optimal direct sum theorem fails for deterministic communication complexity of relations. Alice is given a subset $X \subseteq [n]$ of size $t$, Bob gets no input, and they want to output an element of $X$.

1. Show that $\log(n - t + 1)$ bits are required (and sufficient) for any deterministic protocol.
2. Show that if Alice is given $k$ sets $X_1,\dots,X_k$ each of size $t$, and the parties want an element from each set, there is a deterministic protocol communicating only $O(k\log(n/t) + \log(kn))$ bits, significantly less than $k\log(n-t+1)$ when $t = n/2$.

Hint: pick a random subset of $[n]^k$ of size $(n/t)^k \ln\big((n-t)^k\big)$ and argue it intersects $X_1 \times \cdots \times X_k$ with positive probability.

<a id="pdf-fa052d8c95c0-p017-b004"></a>
<!-- pdf-source: page=17; block=4; confidence=0.90 -->
**Exercise 1.11.** Show that if $g : \{0,1\}^n \times \{0,1\}^n \to \{0,1\}$ requires $c$ bits of communication, then computing $\bigwedge_{i=1}^k g(x_i,y_i)$ and $\bigvee_{i=1}^k g(x_i,y_i)$ requires $k(\sqrt{c/2} - \log n - 1)$ bits of communication. Hint: Find a small 1-cover using the protocol for computing $\bigvee_{i=1}^k g(x_i,y_i)$, and a 0-cover using the protocol for computing $\bigwedge_{i=1}^k g(x_i,y_i)$.

<a id="pdf-fa052d8c95c0-p018-b001"></a>
<!-- pdf-source: page=18; block=1; confidence=0.90 -->
Page contains no extractable text.
