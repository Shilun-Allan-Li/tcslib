<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: 043896d6545f3608f18c8cfb639513f910f8728adce9d936f568118df872e315 -->

<a id="pdf-043896d6545f-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.98 -->
## 1.6 Can We Do Better?

<a id="pdf-043896d6545f-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.90 -->
Lists five limitations of the frequency-moment upper bounds (e.g. Theorem 1.1) that motivate lower bounds:

1. Positive results only for $F_0$ and $F_2$ (arguably $F_1$); nothing for $k>2$ or $k=\infty$.
2. The $F_0$, $F_2$ algorithms only *approximate* the moment — can it be computed exactly (even randomized)?
3. They are randomized Monte Carlo algorithms that fail with probability $\delta$ and cannot detect failure — can $F_0$, $F_2$ be computed deterministically?
4. They use $\Omega(\log n)$ space — can dependence on universe size be reduced?
5. They use $\Omega(\varepsilon^{-2})$ space — can the $\varepsilon^{-2}$ dependence be improved (e.g. to $\approx\varepsilon^{-1}$)?

Concludes that none of these compromises can be removed: the rest of the lecture proves matching *unconditional* (independent of P vs. NP) lower bounds.

<a id="pdf-043896d6545f-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.98 -->
## 1.7 One-Way Communication Complexity

<a id="pdf-043896d6545f-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.95 -->
Introduces one-way communication complexity as a restricted form of the general communication model; the restriction makes lower bounds easier to prove, and such lower bounds typically transfer to streaming-algorithm space lower bounds.

<a id="pdf-043896d6545f-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.85 -->
Communication complexity is general enough to capture the hardness in many computational models, yet many important lower bounds are provable and *unconditional* (not dependent on conjectures like $P\neq NP$); the model's cleanness guides development of the right proof techniques.

<a id="pdf-043896d6545f-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.95 -->
**Setup.** Two parties, Alice and Bob. Alice holds $x\in\{0,1\}^a$, Bob holds $y\in\{0,1\}^b$; neither knows the other's input. They cooperate to compute a Boolean function (predicate) $f:\{0,1\}^a\times\{0,1\}^b\to\{0,1\}$ on their joint input.

<a id="pdf-043896d6545f-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.96 -->
**Definition (one-way protocol).** Only the following is allowed:
1. Alice sends Bob a message $z$ that is a function of her input $x$ only.
2. Bob outputs $f(x,y)$ as a function of $z$ and his input $y$ only.

Both deterministic and randomized one-way protocols are considered.

<a id="pdf-043896d6545f-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.95 -->
**Definition.** The one-way communication complexity of $f$ is the minimum worst-case number of bits used by any correct one-way protocol:
$$\min_{P}\ \max_{x,y}\ \{\text{length (in bits) of Alice's message } z \text{ when her input is } x\},$$
where the minimum is over all correct protocols. For randomized protocols, "correct" means deciding $f$ with probability $\ge 2/3$. It is always at most $a$ (Alice can send all of $x$). Example: for the parity function it equals $1$ (Alice sends the parity of $x$).

<a id="pdf-043896d6545f-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.97 -->
## 1.8 Connection to Streaming Algorithms

<a id="pdf-043896d6545f-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.94 -->
Two-step plan for space lower bounds: (1) small-space streaming algorithms imply low-communication one-way protocols; (2) such low-communication protocols don't exist.

**Reduction (Figure 1.2).** Given a streaming algorithm $S$ using space $s$, Alice and Bob treat their inputs as a stream $(x,y)$ with all of $x$ before all of $y$. Alice feeds $x$ into $S$, whose state is then summarized by its $s$ memory bits; she sends those $s$ bits to Bob, who restarts $S$ from that state and feeds in $y$. Thus $S$ computes a function of $(x,y)$ with communication cost exactly $s$ — the induced protocol's communication equals the streaming space.

<a id="pdf-043896d6545f-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.90 -->
## 1.9 The Disjointness Problem

To execute the two-step plan above to prove lower bounds on the space usage of streaming algorithms, we need to come up with a Boolean function that (i) can be reduced to a [text cut off at end of page].

<a id="pdf-043896d6545f-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.95 -->
**Section 1.9.1.** Introduces the Disjointness problem as the canonical hard problem of communication complexity (analogous to SAT for NP-completeness), the source of most reductions in the course.

<a id="pdf-043896d6545f-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.97 -->
**Definition (Disjointness).** Alice and Bob hold $n$-bit vectors $x, y$, viewed as characteristic vectors of subsets of $\{1,2,\dots,n\}$. Define $\mathrm{DISJ}(x,y)=0$ if there exists index $i \in \{1,2,\dots,n\}$ with $x_i = y_i = 1$, and $\mathrm{DISJ}(x,y)=1$ otherwise.

<a id="pdf-043896d6545f-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.97 -->
**Proposition 1.8.** Every deterministic one-way communication protocol computing $\mathrm{DISJ}$ uses at least $n$ bits of communication in the worst case; i.e., the trivial protocol is optimal among deterministic protocols.

<a id="pdf-043896d6545f-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.96 -->
**Proof.** Suppose Alice sends at most $n-1$ bits, so over the $2^n$ inputs $x$ she sends at most $2^{n-1}$ distinct messages. By the Pigeonhole Principle two distinct inputs $x^1, x^2$ yield the same message $z$. Bob must compute $\mathrm{DISJ}(x,y)$ from $z$ and $y$ only. Let $i$ be a coordinate where $x^1, x^2$ differ; if $y$ is the $i$th basis vector (all zeros except $y_i=1$), then Bob's answer is wrong for exactly one of $x=x^1$ or $x=x^2$. Hence the protocol is incorrect. $\square$

<a id="pdf-043896d6545f-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.97 -->
**Theorem 1.9.** Every randomized one-way protocol that for every input $(x,y)$ correctly decides $\mathrm{DISJ}$ with probability at least $2/3$ uses $\Omega(n)$ communication in the worst case.

<a id="pdf-043896d6545f-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.90 -->
The probability is over the protocol's coin flips (input is worst-case, no input randomness). The constant $2/3$ may be replaced by any constant strictly greater than $1/2$. Theorem 1.9 is taken on faith here and used to derive streaming space lower bounds.

<a id="pdf-043896d6545f-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.92 -->
**Section 1.9.2.** Space lower bound for computing $F_\infty$, even with randomization and approximation, assuming Theorem 1.9.

<a id="pdf-043896d6545f-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.95 -->
**Theorem 1.10 (Alon et al. 1999).** Every randomized streaming algorithm that, for every data stream of length $m$, computes $F_\infty$ to within a $(1 \pm 0.2)$ factor with probability at least $2/3$ uses space $\Omega(\min\{m, n\})$. This rules out extending the $F_0, F_1, F_2$ upper bounds to all $F_k$.

<a id="pdf-043896d6545f-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.94 -->
**Proof (setup).** Let $S$ be a space-$s$ streaming algorithm that for every stream, with probability $\geq 2/3$, outputs an estimate in $(1 \pm 0.2) F_\infty$. Build a one-way protocol $P$ for Disjointness on input $(x,y)$: (1) Alice feeds $S$ the indices $i$ with $x_i=1$ (arbitrary order; no communication). (2) Alice sends $S$'s memory state $\sigma$ to Bob using $s$ bits. (3) Bob resumes $S$ from $\sigma$ and feeds it the indices $i$ with $y_i=1$.

<a id="pdf-043896d6545f-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.94 -->
**Proof (conclusion).** (4) Bob declares "disjoint" iff $S$'s final answer is at most $4/3$. In the stream induced by $(x,y)$, the frequency of index $i \in \{1,\dots,n\}$ is $0$ if $x_i=y_i=0$, $1$ if exactly one of $x_i,y_i$ is $1$, and $2$ if both are $1$. Hence $F_\infty = 2$ for a "no" instance and $\leq 1$ for a "yes" instance. With probability $\geq 2/3$, $S$'s estimate is $\leq 1.2$ (yes) or $\geq 2/1.2$ (no), so $P$ decides correctly. Since $P$ uses $s$ bits, Theorem 1.9 gives $s = \Omega(n)$. As stream length $m = n$, this also rules out $o(m)$-space algorithms. $\square$

<a id="pdf-043896d6545f-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.90 -->
**Remark 1.11 (Heavy Hitters).** Theorem 1.10 shows computing the maximum frequency is hard for worst-case streaming inputs. A tractable relaxation is the heavy hitters problem: for parameter $k$, if any element has frequency $> m/k$, find one or all such elements. For constant $k$ there are good solutions (Misra–Gries algorithm; Count-Min Sketch and variants — Charikar et al. 2004; Cormode and Muthukrishnan 2005).

<a id="pdf-043896d6545f-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.90 -->
**Section 1.9.3.** Shows that for exact computation of $F_0$ and $F_2$, merely allowing randomization (without approximation) is not enough to beat linear space.

<a id="pdf-043896d6545f-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.97 -->
**Theorem 1.12 (Alon et al. 1999).** For every non-negative integer $k \neq 1$, every randomized streaming algorithm that, for every data stream, computes $F_\infty$ exactly with probability at least $2/3$ uses space $\Omega(\min\{n, m\})$.

<a id="pdf-043896d6545f-p006-b005"></a>
<!-- pdf-source: page=6; block=5; confidence=0.80 -->
**Proof.** Nearly identical to the reduction for Theorem 1.10. That proof rules out approximation (even randomized) because $F_\infty$ differs by a factor of $2$ between the "yes" and "no" instances of Disjointness.

<a id="pdf-043896d6545f-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.90 -->
For finite k the true value of Fk differs slightly between the two Disjointness cases, which suffices to rule out a randomized algorithm that is exact at least 2/3 of the time. Consequence of Theorem 1.12: even for F0 and F2, approximation is essential to get a sublinear-space algorithm. Randomization is also essential — every deterministic streaming algorithm that always outputs a (1±ε)-estimate of Fk (for any k≠1) uses linear space (Alon et al. 1999); argument left to the exercises.

<a id="pdf-043896d6545f-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.90 -->
**1.10 Looking Backward and Forward.** Assuming randomized one-way protocols require Ω(n) communication for Disjointness (Theorem 1.9), some frequency moments — in particular F∞ — cannot be computed in sublinear space even allowing randomization and approximation. Both randomization and approximation are essential for the sublinear-space F0 and F2 algorithms. Action items: (1) prove Theorem 1.9; (2) revisit the five compromises of Section 1.6 — the first three shown necessary, the last two addressed next lecture.

<a id="pdf-043896d6545f-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.85 -->
Footnote: the preceding claim is not exactly true, but if Bob also knows the number of 1's in Alice's input (communicable in log2 n bits), then exact computation of Fk lets Bob distinguish yes/no inputs of Disjointness for any k≠1.

<a id="pdf-043896d6545f-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.95 -->
**Lecture 2 — Lower Bounds for One-Way Communication: Disjointness, Index, and Gap-Hamming.**

<a id="pdf-043896d6545f-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.95 -->
**2.1 The Story So Far.** Recap of one-way communication complexity: Alice has input x∈{0,1}^a, Bob has input y∈{0,1}^b, and the goal is to compute a Boolean function f:{0,1}^a×{0,1}^b→{0,1} of (x,y). Alice sends a message z to Bob depending only on x; Bob decides f knowing only z and y. The one-way communication complexity of f is the smallest worst-case number of bits communicated by any protocol computing f. Deterministic protocols are sometimes considered, but the focus is mostly on randomized protocols (defined shortly).

<a id="pdf-043896d6545f-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.85 -->
Figure 2.1: a one-way protocol in which Alice's message depends only on her input and Bob decides based on his input and Alice's message. Data stream model: a stream x1,…,xm ∈ U from a universe of n=|U| elements arrives one by one with insufficient space to store all data, computing statistics in one pass. Previously presented a low-space O(ε^{-2}(log n + log m) log(1/δ)) streaming algorithm that, with probability ≥ 1−δ, computes a (1±ε)-approximation of F2 = Σ_{j∈U} fj² (the skew), where fj ∈ {0,1,…,m} is the number of times j appears in the stream.

<a id="pdf-043896d6545f-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.90 -->
An analogous low-space streaming algorithm estimating F0 (number of distinct elements) is left to the homework. Low-space streaming algorithms S induce low-communication one-way protocols P, with P's communication equal to S's space. Reduction form: Alice converts her input x into a data stream, feeds it into the space-s algorithm S, then sends S's memory (s bits) to Bob; Bob resumes S's execution and feeds a representation of his input y into S. On termination S has computed a useful function of (x,y) using only s bits of communication. Hence lower bounds for one-way communication imply space lower bounds for streaming. Theorem 1.9 was used last lecture without proof.

<a id="pdf-043896d6545f-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.95 -->
**Theorem 2.1.** The one-way communication complexity of the Disjointness problem is Ω(n), even for randomized protocols. (Footnote: last lecture this was proved only for deterministic protocols via a simple Pigeonhole Principle argument.)

<a id="pdf-043896d6545f-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.90 -->
Disjointness input: x,y ∈ {0,1}^n viewed as characteristic vectors of two subsets of {1,…,n}; output is "0" if there is an index i with xi=yi=1, and "1" otherwise. Theorem 1.9 yields streaming space lower bounds: any streaming algorithm computing F∞ (max frequency), even approximately with probability 2/3, needs linear Ω(min{n,m}) space — contrasting the logarithmic space for approximating F0 and F2. The same reduction shows exact computation of F0 or F2 requires linear space even with randomization. A separate argument (homework) shows every deterministic streaming algorithm approximating F0 or F2 to a small constant factor requires linear space. Today: prove Theorem 1.9, give lower bounds for other one-way-hard problems, and derive further streaming space lower bounds via reductions.

<a id="pdf-043896d6545f-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.85 -->
**2.2 Randomized Protocols.** There are many flavors of randomized communication protocols, so one must specify precisely which are meant before proving lower bounds. For algorithmic applications one can almost always focus on a particular flavor (continues on next page).

<a id="pdf-043896d6545f-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.90 -->
**Section 2.2 (cont.).** Four default assumptions/rules of thumb are adopted for the randomized protocols studied, chosen to admit as broad (permissive) a class of protocols as possible so as to maximize the strength of the resulting lower bounds and their algorithmic consequences.

<a id="pdf-043896d6545f-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.95 -->
**Assumption (Public coins).** Unless noted, protocols are public-coin: an infinite sequence of uniformly random bits is written on a shared blackboard visible to both Alice and Bob before they start, and using any number of them costs no communication. Private-coin protocols (each player flips its own coins, hidden from the other unless communicated) can be simulated by public-coin protocols with no loss (e.g. Alice uses shared bits 1,3,5,..., Bob uses 2,4,6,...). Public coins are strictly more powerful than private coins but behave essentially the same here; the lower bounds apply to public-coin (hence also private-coin) protocols. Additionally, public-coin randomized protocols are equivalent to distributions over deterministic protocols: fixing the blackboard bits makes the protocol deterministic, and any distribution over deterministic protocols with rational probabilities is realized by using the public coins to sample it.

<a id="pdf-043896d6545f-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.93 -->
**Assumption (Two-sided error).** Protocols may err with some probability on every input (x,y), whether f(x,y)=0 or f(x,y)=1. This is weaker than one-sided error (two flavors: forbidding false positives, or forbidding false negatives). Lower bounds against two-sided-error protocols are at least as strong as those against one-sided-error protocols. The one-way protocols induced by the streaming algorithms of the previous lecture are two-sided-error randomized protocols; some problems instead have natural one-sided-error solutions.

<a id="pdf-043896d6545f-p010-b004"></a>
<!-- pdf-source: page=10; block=4; confidence=0.90 -->
**Assumption (Arbitrary constant error probability).** All constant error probabilities ε ∈ (0, 1/2) yield the same communication complexity up to a constant factor, because success can be boosted by amplification (repeated trials). [Justification continues on the next page.] Footnote: one may also consider zero-error randomized protocols, which always output correctly but use a random amount of communication; these are not discussed.

<a id="pdf-043896d6545f-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.55 -->
**Amplification (cont.).** If protocol P uses k bits and succeeds with probability ≥ 51% on every input, run 10000 independent copies in parallel (public coins supply the 10000 random strings, preserving one-way-ness): Alice sends 10000 messages and Bob outputs the majority vote. In expectation 5100 trials are correct, and Pr[more than 5000 correct] is large (≥ 90%). In general a constant number of trials plus a majority vote boosts success from any constant > 1/2 to any constant < 1, at only a constant-factor increase in communication. Consequently one is sloppy about the exact constant error: for upper bounds it suffices to achieve error 49% (reducible to any small constant), and for lower bounds it suffices to rule out protocols with error 1% (the same bounds hold up to constants even against error 49%).

<a id="pdf-043896d6545f-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.90 -->
**Assumption (Worst-case communication).** The communication cost of a randomized protocol is the worst case over inputs (x,y) and over coin flips; cost ≤ k means Alice always sends at most k bits. Using expected rather than worst-case communication changes the complexity of a problem (for protocols that may err) by only a constant factor. Sketch: if R has two-sided error ≤ 1/3 and uses ≤ k bits on average, then by a Markov-type argument R uses ≤ 10k bits at least 90% of the time. Define R': simulate R for up to 10k steps, and if it has not terminated, abort and output an arbitrary answer. Then R' always sends ≤ 10k bits and has error at most error(R) + 10% (≈ 43%), which is reduced back to 1/3 (or any target) by repeated trials.

<a id="pdf-043896d6545f-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.85 -->
Given these four standing assumptions and rules, Theorem 1.9 is restated in the next section.

<a id="pdf-043896d6545f-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.95 -->
**Section 2.3. Distributional Complexity.**

<a id="pdf-043896d6545f-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.95 -->
**Theorem 2.2.** Every public-coin randomized one-way protocol for Disjointness with two-sided error at most a constant ε ∈ (0, 1/2) uses Ω(min{n, m}) communication in the worst case (over inputs and coin flips).

<a id="pdf-043896d6545f-p012-b003"></a>
<!-- pdf-source: page=12; block=3; confidence=0.90 -->
Randomized protocols are harder to reason about than deterministic ones: the previous lecture's Pigeonhole argument (if Alice always sends ≤ n−1 bits then two distinct inputs x, x' induce the same message z) breaks down, since in a randomized protocol Alice may use a different distribution over (n−1)-bit messages for each of her 2^n inputs. Distributional complexity is the main method for randomized lower bounds: it reduces the task to proving lower bounds for deterministic protocols against a suitably chosen input distribution.

<a id="pdf-043896d6545f-p012-b004"></a>
<!-- pdf-source: page=12; block=4; confidence=0.95 -->
**Lemma 2.3 (Yao 1983).** Let D be a distribution over inputs (x,y) to a communication problem and ε ∈ (0, 1/2). Suppose every deterministic one-way protocol P with Pr_{(x,y)∼D}[P wrong on (x,y)] ≤ ε has communication cost at least k. Then every public-coin randomized one-way protocol R with two-sided error at most ε on every input has communication cost at least k. (In the hypothesis the randomness is in the input with P deterministic; in the conclusion the input is fixed and R flips coins.)

<a id="pdf-043896d6545f-p012-b005"></a>
<!-- pdf-source: page=12; block=5; confidence=0.90 -->
**Proof of Lemma 2.3 (begins).** Let R be a randomized protocol with communication cost < k. Write R as a distribution over deterministic protocols P₁, P₂, …, P_s. Since randomized cost is worst-case over inputs and coin flips, each P_i always uses < k bits. By the hypothesis (contrapositive), each satisfies Pr_{(x,y)∼D}[P_i wrong on (x,y)] > ε. [Proof continues beyond the supplied pages.]

<a id="pdf-043896d6545f-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.92 -->
**Proof (concl.).** Averaging over the $P_i$ gives $\Pr_{(x,y)\sim D;\,R}[R\text{ wrong on }(x,y)] > \epsilon$. Since a maximum is at least the average, some input $(x,y)$ satisfies $\Pr_R[R\text{ wrong on }(x,y)] > \epsilon$, completing the proof. $\square$

<a id="pdf-043896d6545f-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.95 -->
Converse of Lemma 2.3 (Yao, 1983): for any randomized communication complexity there exists a hard input distribution $D$ witnessing it; proved via strong LP duality / von Neumann's Minimax Theorem. Hence the distributional method is complete for lower bounds; here $D$ is the uniform distribution.

<a id="pdf-043896d6545f-p013-b003"></a>
<!-- pdf-source: page=13; block=3; confidence=0.99 -->
## 2.4 The Index Problem

<a id="pdf-043896d6545f-p013-b004"></a>
<!-- pdf-source: page=13; block=4; confidence=0.96 -->
Theorem 2.2 is proved in two steps: (1) a linear lower bound on the randomized communication complexity of the Index problem; (2) an easy reduction of Index to Disjointness.

<a id="pdf-043896d6545f-p013-b005"></a>
<!-- pdf-source: page=13; block=5; confidence=0.97 -->
**Definition (Index).** Alice holds $x \in \{0,1\}^n$; Bob holds $i \in \{1,2,\dots,n\}$ encoded in binary using $\approx \log_2 n$ bits. Goal: compute $x_i$, the $i$th bit of Alice's input.

<a id="pdf-043896d6545f-p013-b006"></a>
<!-- pdf-source: page=13; block=6; confidence=0.94 -->
Intuition: Alice, not knowing which bit Bob wants, must send essentially her whole input; provable easily for deterministic protocols via pigeonhole, and holds (with more work) for randomized protocols.

<a id="pdf-043896d6545f-p013-b007"></a>
<!-- pdf-source: page=13; block=7; confidence=0.98 -->
**Theorem 2.4 (Kremer et al., 1999).** The randomized one-way communication complexity of Index is $\Omega(n)$.

<a id="pdf-043896d6545f-p013-b008"></a>
<!-- pdf-source: page=13; block=8; confidence=0.95 -->
With general (two-way) protocols Index is solvable using only $\approx \log_2 n$ bits (Bob sends $i$ to Alice), so Index captures the extra difficulty specific to one-way protocols.

<a id="pdf-043896d6545f-p013-b009"></a>
<!-- pdf-source: page=13; block=9; confidence=0.95 -->
**Proof of Theorem 2.2.** Reduce Disjointness to Index. Given an Index instance $(x,i)$, Alice forms $x' = x$ and Bob forms $y' = e_i$, the standard basis vector with a $1$ in coordinate $i$ and $0$ elsewhere. (continues p.14)

<a id="pdf-043896d6545f-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.96 -->
**Proof of Theorem 2.2 (concl.).** Then $(x',y')$ is a "yes" instance of Disjointness iff $x_i = 0$. Thus every one-way protocol for Index yields one for Disjointness with the same communication cost and error probability. $\square$

<a id="pdf-043896d6545f-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.95 -->
**Proof of Theorem 2.4.** Apply the distributional complexity method with $D$ the uniform distribution, where $x$ and $i$ are chosen independently and uniformly at random.

<a id="pdf-043896d6545f-p014-b003"></a>
<!-- pdf-source: page=14; block=3; confidence=0.95 -->
**Proof (step).** Let $c$ be a sufficiently small constant ($\le 0.1$) and $n$ large ($\ge 300$). Show every deterministic one-way protocol using $\le cn$ bits has error $\ge \tfrac{1}{8}$ w.r.t. $D$. By Lemma 2.3 this gives every randomized protocol error $\ge \tfrac{1}{8}$ on some input, hence for every error $\epsilon' > 0$ there is $c' > 0$ such that every randomized protocol using $\le c'n$ bits has error $> \epsilon'$.

<a id="pdf-043896d6545f-p014-b004"></a>
<!-- pdf-source: page=14; block=4; confidence=0.95 -->
**Proof (step).** Fix deterministic one-way $P$ using $\le cn$ bits; Alice sends at most $2^{cn}$ distinct messages $z$. For fixed $z$, Bob's outputs over inputs $i = 1,\dots,n$ form the $n$-bit answer vector $a(z)$. There are at most $2^{cn}$ answer vectors.

<a id="pdf-043896d6545f-p014-b005"></a>
<!-- pdf-source: page=14; block=5; confidence=0.96 -->
**Proof (step).** Fix Alice's input $x$ giving message $z$. Since $i$ is uniform and independent of $x$,
$$\Pr_i[P\text{ incorrect}\mid x,z] = \frac{d_H(x, a(z))}{n}, \quad (2.1)$$
where $d_H$ is Hamming distance. Goal: with constant probability over $x$, (2.1) is bounded below by a constant.

<a id="pdf-043896d6545f-p014-b006"></a>
<!-- pdf-source: page=14; block=6; confidence=0.95 -->
**Proof (step).** Let $A = \{a(z(x)) : x \in \{0,1\}^n\}$ be the set of answer vectors used by $P$, with $|A| \le 2^{cn}$. Call $x$ *good* if some $a \in A$ has $d_H(x,a) < n/4$, and *bad* otherwise. (continues p.15)

<a id="pdf-043896d6545f-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.94 -->
**Proof (step).** Geometrically, each answer vector $a$ is the center of a Hamming ball of radius $n/4$ in $\{0,1\}^n$. Because there are only $2^{cn}$ balls (small $c$) with modest radius $n/4$, their union covers less than half the Hamming cube.

<a id="pdf-043896d6545f-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.95 -->
Figure 2.2: Hamming balls of radius $n/4$ centered at the answer vectors used by protocol $P$.

<a id="pdf-043896d6545f-p015-b003"></a>
<!-- pdf-source: page=15; block=3; confidence=0.97 -->
**Claim.** Provided $c$ is sufficiently small and $n$ sufficiently large, there are at least $2^{n-1}$ bad inputs $x$.

<a id="pdf-043896d6545f-p015-b004"></a>
<!-- pdf-source: page=15; block=4; confidence=0.90 -->
Footnote 5: For large $n$, a Hamming ball of radius $r$ around a point contains very few points until $r$ is nearly $n/2$, about half the points when $r \approx n/2$, and almost all the points once $r$ exceeds $n/2$ even modestly.

<a id="pdf-043896d6545f-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.93 -->
**Proof (continued).** The Claim implies the theorem. Decompose $\Pr_{(x,y)\sim D}[D\text{ wrong}] = \Pr[x\text{ good}]\cdot\Pr[D\text{ wrong}\mid x\text{ good}] + \Pr[x\text{ bad}]\cdot\Pr[D\text{ wrong}\mid x\text{ bad}]$, where $\Pr[x\text{ bad}]\ge 1/2$ (by the Claim) and $\Pr[D\text{ wrong}\mid x\text{ good}]\ge 0$. By (2.1) and the definition of a bad input, $\Pr[D\text{ wrong}\mid x\text{ bad}] = \mathbb{E}_x\!\left[\tfrac{d_H(x,a(z(x)))}{n}\mid x\text{ bad}\right] \ge \mathbb{E}_x\!\left[\min_{a\in A}\tfrac{d_H(x,a)}{n}\mid x\text{ bad}\right] \ge \tfrac14$. Hence protocol $P$ errs on $D$ with probability $\ge \tfrac18$, proving the theorem.

<a id="pdf-043896d6545f-p016-b002"></a>
<!-- pdf-source: page=16; block=2; confidence=0.80 -->
**Proof of Claim.** Fix an answer vector $a\in A$. The number of inputs $x$ within Hamming distance $n/4$ of $a$ is $1+\binom{n}{1}+\binom{n}{2}+\cdots+\binom{n}{n/4}$ (2.2). Using $\binom{n}{k}\le\left(\tfrac{en}{k}\right)^k$ (from Stirling's approximation), bound (2.2) by $n(4e)^{n/4} = n\,2^{\frac{n}{4}\log_2(4e)} \le n\,2^{.861n}$. The total number of good inputs (the union of all $|A|$ balls) is at most $|A|\cdot 2^{.861n} \le 2^{(.861+c)n} \le 2^{n-1}$ for $c$ small (say $.1$) and $n$ large (say $\ge 300$). $\blacksquare$

<a id="pdf-043896d6545f-p017-b001"></a>
<!-- pdf-source: page=17; block=1; confidence=0.86 -->
**Section 2.5 (review).** Theorem 2.4 completes the first approach to streaming space lower bounds. The chain: Index proven hard for one-way protocols (Thm 2.4), Index reduced to Disjointness (Thm 2.2), Disjointness reduced to streaming. Consequences: linear space is necessary to compute the highest frequency $F_\infty$, even allowing randomization and approximation; and linear space is necessary to compute $F_0$ or $F_2$ exactly by a randomized streaming algorithm with success probability $2/3$.

<a id="pdf-043896d6545f-p017-b002"></a>
<!-- pdf-source: page=17; block=2; confidence=0.70 -->
**Figure 2.3.** Proof structure of the linear (in $\min\{n,m\}$) space lower bounds: Index $\xrightarrow{\text{Thm 2.2}}$ Disjointness $\xrightarrow{\text{Lecture 1}}$ Streaming. Lower bounds travel from left to right.

<a id="pdf-043896d6545f-p017-b003"></a>
<!-- pdf-source: page=17; block=3; confidence=0.85 -->
**Section 2.5 (next goal).** Known $F_0$/$F_2$ streaming algorithms have space quadratic in $\epsilon^{-1}$ (a $1\%$ approximation costs a $10{,}000\times$ blowup). Goal: prove space quadratic in $\epsilon^{-1}$ is necessary — even with randomization and even for $F_0$ and $F_2$ — to achieve a $(1\pm\epsilon)$-approximation. This is done via reductions (Figure 2.4): introduce the Gap-Hamming problem, reduce Index to Gap-Hamming (Thm 2.5), and show one-way Gap-Hamming protocols with sublinear communication induce streaming algorithms computing a $(1\pm\epsilon)$-approximation of $F_0$ or $F_2$ in $o(\epsilon^{-2})$ space.

<a id="pdf-043896d6545f-p017-b004"></a>
<!-- pdf-source: page=17; block=4; confidence=0.70 -->
**Figure 2.4.** Proof plan for $\Omega(\epsilon^{-2})$ space lower bounds for randomized streaming algorithms approximating $F_0$ or $F_2$ to a $1\pm\epsilon$ factor: Index $\xrightarrow{\text{Thm 2.5}}$ Gap-Hamming $\xrightarrow{\text{Section 2.6.2}}$ Streaming. Lower bounds travel from left to right.

<a id="pdf-043896d6545f-p018-b001"></a>
<!-- pdf-source: page=18; block=1; confidence=0.86 -->
**Section 2.6 (The Gap-Hamming Problem).** Goal: every streaming algorithm computing a $(1\pm\epsilon)$-approximation of $F_0$ or $F_2$ needs $\Omega(\epsilon^{-2})$ space. Not claimed for $\epsilon \ll 1/\sqrt{n}$, since a frequency moment is computable exactly in linear or near-linear space. The extreme case is that a $(1\pm 1/\sqrt{n})$-approximation requires $\Omega(n)$ space; this special case already contains all ideas needed for the general $\Omega(\epsilon^{-2})$ bound.

<a id="pdf-043896d6545f-p018-b002"></a>
<!-- pdf-source: page=18; block=2; confidence=0.85 -->
**Section 2.6.1 (Why Disjointness doesn't work).** In the natural one-way reduction, a streaming algorithm $S$ giving a $(1\pm 1/\sqrt{n})$-approximation of $F_0$ (Alice streams $x$, sends $S$'s memory state to Bob, Bob streams $y$ and resumes $S$) estimates $F_0$ of the combined stream. For a "yes" instance of Disjointness, $F_0 = |x|+|y|$ (with $|\cdot|$ the number of 1's); for a "no" instance, $F_0$ lies between $\max\{|x|,|y|\}$ and $|x|+|y|-1$. In the hard case $|x|=|y|=n/2$ with the sets disjoint or overlapping in one element, $F_0$ is $n$ or $n-1$, but a $(1\pm 1/\sqrt{n})$-approximation gives additive error $\approx\sqrt{n}$ — too coarse to distinguish the cases. So this reduction fails.

<a id="pdf-043896d6545f-p018-b003"></a>
<!-- pdf-source: page=18; block=3; confidence=0.93 -->
**Section 2.6.2 (Reducing Gap-Hamming to $F_0$ estimation).** $F_0$ estimation instead solves estimation of the Hamming distance $d_H(x,y)$ (number of coordinates where $x,y$ differ). For $x,y\in\{0,1\}^n$ over $U=\{1,2,\dots,n\}$, viewing $x,y$ as characteristic vectors of sets $A,B\subseteq U$ (Figure 2.5): $d_H(x,y) = |A\setminus B| + |B\setminus A|$ (size of the symmetric difference), and $F_0 = |A\cup B|$. Hence $|A\setminus B| = F_0 - |B|$ and $|B\setminus A| = F_0 - |A|$. [Text truncated here.]

<a id="pdf-043896d6545f-p019-b001"></a>
<!-- pdf-source: page=19; block=1; confidence=0.90 -->
Since $d_H(x,y) = 2F_0 - |x| - |y|$ and Alice can send $|x|$ using $\log_2 n$ bits, a one-way protocol computing $F_0$ with communication $c$ gives one for $d_H(x,y)$ with communication $c + \log_2 n$. More generally, a $(1 \pm \tfrac{1}{\sqrt n})$-approximation of $F_0$ yields a protocol estimating $d_H(x,y)$ up to additive error $2F_0/\sqrt n \le 2\sqrt n$, with $\log_2 n$ extra communication.

<a id="pdf-043896d6545f-p019-b002"></a>
<!-- pdf-source: page=19; block=2; confidence=0.95 -->
Figure 2.5: the Hamming distance between two bit vectors equals the size of the symmetric difference of the corresponding subsets of 1-coordinates.

<a id="pdf-043896d6545f-p019-b003"></a>
<!-- pdf-source: page=19; block=3; confidence=0.95 -->
**Definition (Gap-Hamming(t)).** For a parameter $t$, a protocol correctly solves Gap-Hamming$(t)$ if it outputs "1" whenever $d_H(x,y) < t - c\sqrt n$ and outputs "0" whenever $d_H(x,y) > t + c\sqrt n$, for a sufficiently small constant $c$. On inputs with $d_H(x,y) = t \pm c\sqrt n$ the output is unconstrained (a promise problem).

<a id="pdf-043896d6545f-p019-b004"></a>
<!-- pdf-source: page=19; block=4; confidence=0.88 -->
The reduction shows Gap-Hamming$(t)$ reduces to the $(1 \pm \tfrac{c}{\sqrt n})$-approximation of $F_0$ for every $t$. Choosing $t=0$ makes it a special case of Equality (whose one-way public-coin randomized complexity is $O(1)$), and $t=n$ is equally unhelpful; $t=n/2$ is more promising, as certifying a "no" instance appears hard.

<a id="pdf-043896d6545f-p020-b001"></a>
<!-- pdf-source: page=20; block=1; confidence=0.90 -->
For $x,y \in \{0,1\}^n$ chosen uniformly at random the expected Hamming distance is $n/2$ with standard deviation $\approx \tfrac{1}{2}\sqrt n$, so deciding Gap-Hamming$(n/2)$ resembles learning an unpredictable fact about two random strings.

<a id="pdf-043896d6545f-p020-b002"></a>
<!-- pdf-source: page=20; block=2; confidence=0.95 -->
**2.7 Lower Bound on the One-Way Communication Complexity of Gap-Hamming.** Formally proves that every protocol solving Gap-Hamming with $t=n/2$ and $c$ sufficiently small requires linear communication.

<a id="pdf-043896d6545f-p020-b003"></a>
<!-- pdf-source: page=20; block=3; confidence=0.97 -->
**Theorem 2.5 (Jayram et al. 2008; Woodruff 2004, 2007).** The randomized one-way communication complexity of Gap-Hamming is $\Omega(n)$.

<a id="pdf-043896d6545f-p020-b004"></a>
<!-- pdf-source: page=20; block=4; confidence=0.92 -->
**Proof.** A randomized reduction from Index. Alice holds an $n$-bit string $x$, Bob holds index $i \in \{1,\dots,n\}$; assume $n$ odd and large. Using public randomness with no communication they generate a Gap-Hamming input $(x_0,y_0)$ one bit at a time. For the first bit: interpret the first $n$ public coins as a random string $r$; Bob sets $b = r_i$. Alice checks whether $d_H(x,r) < n/2$ or $> n/2$ (one holds since $n$ is odd), setting $a=1$ in the former case and $a=0$ otherwise.

<a id="pdf-043896d6545f-p020-b005"></a>
<!-- pdf-source: page=20; block=5; confidence=0.92 -->
**Proof (cont.).** Key claim: $a$ and $b$ are correlated — positively if $x_i=1$, negatively if $x_i=0$. Condition on the $n-1$ bits of $r$ other than $i$. Case 1: $x$ and $r$ agree on strictly fewer or strictly more than $(n-1)/2$ of those bits, so $a$ is already determined; then $\Pr[a=b] = \Pr[a=r_i] = \tfrac12$ since $r_i$ is independent. Case 2: exactly half of the $n-1$ bits agree with $x$, so $a=1$ iff $x_i=r_i$; hence if $x_i=1$ then $a,b$ always agree, and if $x_i=0$ they always disagree. The probability of Case 2 equals $\Pr[(n-1)/2 \text{ heads in } n-1 \text{ flips}] = \binom{n-1}{(n-1)/2}$.

<a id="pdf-043896d6545f-p021-b001"></a>
<!-- pdf-source: page=21; block=1; confidence=0.90 -->
**Proof (cont.).** Stirling's approximation gives $\Pr[\text{Case 2}] \approx \tfrac{c_0}{\sqrt n}$ for a constant $c_0$. Therefore
$$\Pr[a=b] = \Pr[\text{Case 1}]\cdot\tfrac12 + \Pr[\text{Case 2}]\cdot(1\text{ or }0) = \left(1-\tfrac{c_0}{\sqrt n}\right)\tfrac12 + \tfrac{c_0}{\sqrt n}\cdot(1\text{ or }0),$$
which equals $\tfrac12 - \tfrac{c_0}{\sqrt n}$ if $x_i=1$ and $\tfrac12 + \tfrac{c_0}{\sqrt n}$ if $x_i=0$. Thus with shared randomness but no communication the parties generate bits correlated with $x_i$.

<a id="pdf-043896d6545f-p021-b002"></a>
<!-- pdf-source: page=21; block=2; confidence=0.90 -->
**Proof (cont.).** Repeat the experiment $m = qn$ independent times ($q$ a large constant) to form $x_0, y_0$. The expected Hamming distance is at most $\tfrac{m}{2} - c_0\sqrt m$ (if $x_i=1$) or at least $\tfrac{m}{2} + c_0\sqrt m$ (if $x_i=0$). By a Chernoff bound, for suitable small $c$ and large $q$, with probability $\ge 8/9$ one has $d_H(x_0,y_0) < \tfrac{m}{2} - c\sqrt m$ (if $x_i=1$) and $> \tfrac{m}{2} + c\sqrt m$ (if $x_i=0$). Invoking any Gap-Hamming protocol $P$ on $(x_0,y_0)$ then answers the Index instance $(x,i)$, at communication cost of $P$ on length $m = \Theta(n)$. Hence a public-coin randomized Gap-Hamming protocol with two-sided error $1/3$ and sublinear communication would give an Index protocol with error $4/9$; since that is ruled out, so is the former. $\blacksquare$

<a id="pdf-043896d6545f-p021-b003"></a>
<!-- pdf-source: page=21; block=3; confidence=0.88 -->
**Theorem 2.6.** There is a constant $c > 0$ such that no sublinear-space randomized streaming algorithm computes $F_0$ to within a $1 \pm \tfrac{c}{\sqrt n}$ factor with probability at least $2/3$ for every data stream. (Follows by combining Theorem 2.5 with the reduction from Gap-Hamming to estimating $F_\infty$.)

<a id="pdf-043896d6545f-p021-b004"></a>
<!-- pdf-source: page=21; block=4; confidence=0.88 -->
A variation of the same reduction proves the same lower bound for approximating $F_2$. Footnote: the correlated-bit generation is impossible with private coins, but the additive difference between private- and public-coin communication complexity of a problem is $O(\log n)$, so a linear lower bound for one type carries over to the other.

<a id="pdf-043896d6545f-p022-b001"></a>
<!-- pdf-source: page=22; block=1; confidence=0.90 -->
## 2.7 Lower Bound for Gap-Hamming

<a id="pdf-043896d6545f-p022-b002"></a>
<!-- pdf-source: page=22; block=2; confidence=0.95 -->
Goal: a $(1\pm\epsilon)$-approximation of $F_0$ requires space $\Omega(\epsilon^{-2})$ when $\epsilon \ge 1/\sqrt n$. Theorem 2.6 establishes this only for $\epsilon = \Theta(1/\sqrt n)$. Extension to larger $\epsilon$ via padding: fix $n$ and $\epsilon \ge 1/\sqrt n$, reduce from Gap-Hamming on inputs of length $m = \Theta(\epsilon^{-2})$; given $(x,y)$ form $(x',y')$ by appending $n-m$ zeroes to $x$ and $y$. A streaming algorithm using space $s$ that $(1\pm\epsilon)$-estimates $F_0$ on the induced stream yields a randomized protocol solving this special case of Gap-Hamming with communication $s$. Theorem 2.5 gives communication $\Omega(\epsilon^{-2})$ for that problem, so the same bound applies to the streaming space.

<a id="pdf-043896d6545f-p023-b001"></a>
<!-- pdf-source: page=23; block=1; confidence=0.95 -->
# Lecture 3: Lower Bounds for Compressive Sensing

<a id="pdf-043896d6545f-p023-b002"></a>
<!-- pdf-source: page=23; block=2; confidence=0.95 -->
## 3.1 An Appetizer: Randomized Communication Complexity of Equality

<a id="pdf-043896d6545f-p023-b003"></a>
<!-- pdf-source: page=23; block=3; confidence=0.92 -->
Equality: $f(x,y)=1$ iff $x=y$, for inputs of length $n$. Its deterministic one-way communication complexity is $n$ (Pigeonhole Principle). Randomized protocols here are public-coin by default with two-sided error $\epsilon <\tfrac12$. Question: what is its randomized communication complexity?

<a id="pdf-043896d6545f-p023-b004"></a>
<!-- pdf-source: page=23; block=4; confidence=0.97 -->
**Theorem 3.1 (Yao 1979).** The public-coin randomized one-way communication complexity of Equality is $O(1)$.

<a id="pdf-043896d6545f-p023-b005"></a>
<!-- pdf-source: page=23; block=5; confidence=0.85 -->
Randomized communication complexity can be radically smaller than deterministic. Cautionary lesson: clever protocols can defeat expected hardness or complicate lower-bound proofs, and few natural problems remain to reduce from when proving randomized lower bounds. Footnotes: the $n$ lower bound extends to general (not just one-way) deterministic protocols; public-coin model = shared random bits on a blackboard not counted toward cost; Gap-Hamming needs midpoint $t=n/2$, since $t$ near $0$ or $n$ makes it a special case of Equality and thus easy for randomized protocols.

<a id="pdf-043896d6545f-p024-b001"></a>
<!-- pdf-source: page=24; block=1; confidence=0.93 -->
**Proof of Theorem 3.1.** Protocol: (1) Alice and Bob read the first $2n$ public coins as random strings $r_1,r_2\in\{0,1\}^n$ (no communication). (2) Alice sends $\langle x,r_1\rangle \bmod 2$ and $\langle x,r_2\rangle \bmod 2$ (2 bits). (3) Bob outputs $1$ iff $\langle x,r_i\rangle = \langle y,r_i\rangle \bmod 2$ for $i=1,2$.

Error $\le 25\%$, one-sided: if $x=y$ always accepts (no false negatives). If $x\ne y$, by the Principle of Deferred Decisions, for each $i$ the inner products differ mod 2 with probability exactly $50\%$: pick index $j$ with $x_j\ne y_j$, condition on all bits of $r_i$ except the $j$-th; if that bit is $0$ both partial products are unchanged, if $1$ exactly one flips (since exactly one of $x_j,y_j$ is $1$), so exactly one of the two bit values makes the products differ. Two independent experiments both matching for unequal strings has probability $25\%$. $\blacksquare$

<a id="pdf-043896d6545f-p024-b002"></a>
<!-- pdf-source: page=24; block=2; confidence=0.88 -->
The 2-bit protocol has one-sided error $25\%$; parallel repetition drives error to any small constant with constant blow-up in communication. Public coins are essential: the private-coin one-way randomized complexity is $\Theta(\log n)$ — worse than public-coin but far better than deterministic. Newman's theorem (next lecture): private-coin complexity exceeds public-coin complexity by at most $O(\log n)$. The protocol gives each string a 2-bit sketch/fingerprint preserving distinctness — essentially hashing.

<a id="pdf-043896d6545f-p024-b003"></a>
<!-- pdf-source: page=24; block=3; confidence=0.90 -->
**Remark 3.2.** The communication-complexity model is very powerful (e.g., Alice and Bob have unlimited computation) and exists mainly to prove lower bounds; thus an upper-bound result like Theorem 3.1 prompts asking what the [text continues beyond page].
