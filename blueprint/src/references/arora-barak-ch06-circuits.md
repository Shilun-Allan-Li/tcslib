<!-- generated-by: maintainer ingest for EF-H12 (2026-11-19; ruling EF-H12-R4 A / Q-H12-2 A), transcribed from the scoped pypdf raw extraction and checked against page images -->
<!-- source-pdf-sha256: da0881782a35bde6a0779a2eb1a8d480f39fbddf70bbb92824d1dc5550a033b2 -->
<!-- validation-status: awaiting Codex source review -->

# Arora–Barak, Chapter 6: Circuits (authors' web draft)

**Source.** S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, the authors' public
web draft, downloaded on 2026-11-19 from <https://theory.cs.princeton.edu/complexity/book.pdf>
(489 pages; SHA-256 `da0881782a35bde6a0779a2eb1a8d480f39fbddf70bbb92824d1dc5550a033b2`; page
footers "Web draft 2007-01-08 21:59"). This file covers **PDF pages 117–130**, the whole of the
draft's Chapter 6 (Chapter 7 begins on PDF page 131). The PDF is not committed.

**Numbering.** This is the draft, **not** the Cambridge University Press 2009 edition that the
tag [AB09] names. Every chapter, section, definition, theorem, lemma, remark, example, exercise
and page number below is the **draft's and may differ from the CUP 2009 edition**; in this chapter
it differs substantially. In particular, the circuit-satisfiability material that TCSlib cites as
[AB09, §6.1.2, Definition 6.9, Lemmas 6.10 and 6.11, p. 111] is, in this draft, **Section 6.7,
Definition 6.30, Lemmas 6.31 and 6.32, printed p. 112** (anchors `p128-b001` to `p128-b006`),
while the draft's own Definition 6.9, Example 6.10 and Theorem 6.11 are about advice
(§6.1.1). Anchors use the physical PDF page; the draft's printed page is the PDF page minus 16
(PDF p. 128 is printed "p6.12 (112)"). The full mapping is recorded in
`briefs/efficiency-gaps/wave1/EF-H12/ingest-report.md`.

**Form.** As in the chapter 7 and 13 ingests, definitions and statements are transcribed close to
the draft's wording (mathematics in Unicode, overbars written as an overline); proofs, examples
and discussion are condensed; exercises are summarised by number. Bold block labels are the
ingester's, and notes marked *Transcription note* are not part of the source.

<a id="pdf-da0881782a35-p117-b001"></a>
<!-- pdf-source: page=117; block=1; confidence=0.93 -->
# Chapter 6: Circuits

_Epigraph (Karp and Lipton, 1982): one might imagine that P ≠ NP, but SAT is tractable in the sense that for every ℓ there is a very short program that runs in time ℓ² and correctly treats all instances of size ℓ._

<a id="pdf-da0881782a35-p117-b002"></a>
<!-- pdf-source: page=117; block=2; confidence=0.90 -->
Introduction. A Boolean circuit generalises Boolean formulae and roughly formalises the "silicon chip". Motivations: it is a natural model of *nonuniform* computation (a different "algorithm" for each input size, versus the uniform TM model); and complexity classes such as P and NP could in principle be separated by circuit lower bounds (Chapter 13 describes partial successes, Chapter 22 where the effort is stuck). The chapter defines P/poly (languages computable by polynomial-sized Boolean circuits), relates it to NP, studies subclasses including NC (efficient parallel computation), and characterises the polynomial hierarchy by exponential-sized constant-depth circuits.

<a id="pdf-da0881782a35-p117-b003"></a>
<!-- pdf-source: page=117; block=3; confidence=0.92 -->
## 6.1 Boolean circuits

A Boolean circuit is a diagram showing how to derive an output from an input by combining the basic Boolean operations OR (∨), AND (∧) and NOT (¬); Figure 6.1 shows a circuit computing XOR.

<a id="pdf-da0881782a35-p118-b001"></a>
<!-- pdf-source: page=118; block=1; confidence=0.80 -->
**Figure 6.1.** A circuit C computing the XOR function (i.e., C(x₁, x₂) = 1 iff x₁ ≠ x₂). *Transcription note:* the drawing is not transcribed; the text layer renders it as font-code debris ("/X56 …").

<a id="pdf-da0881782a35-p118-b002"></a>
<!-- pdf-source: page=118; block=2; confidence=0.97 -->
**Definition 6.1 (Boolean circuits).** For every n, m ∈ ℕ a Boolean circuit C with n inputs and m outputs is a directed acyclic graph. It contains n nodes with no incoming edges, called the *input nodes*, and m nodes with no outgoing edges, called the *output nodes*. All other nodes are called *gates* and are labeled with one of ∨, ∧ or ¬ (in other words, the logical operations OR, AND, and NOT). The ∨ and ∧ nodes have *fanin* (i.e., number of incoming edges) of 2 and the ¬ nodes have fanin 1. The *size* of C, denoted by |C|, is the number of nodes in it. The circuit is called a *Boolean formula* if each node has at most one outgoing edge.

<a id="pdf-da0881782a35-p118-b003"></a>
<!-- pdf-source: page=118; block=3; confidence=0.93 -->
**The function a circuit computes.** Number the n input and m output nodes canonically, so an n-bit input assigns a value in {0,1} to each input node. Since the graph is acyclic, assign each node an integral depth (breadth-first search or topological sorting) such that each node has incoming edges only from nodes of higher depth. Process the nodes in decreasing order of depth: for each node, apply its label's operation (∨, ∧ or ¬) to the values of the nodes at the other ends of its incoming edges. This gives each node a unique value; the values at the m output nodes are the circuit's m-bit output. For u ∈ {0,1}ⁿ, C(u) denotes the output of C on input u.

<a id="pdf-da0881782a35-p118-b004"></a>
<!-- pdf-source: page=118; block=4; confidence=0.90 -->
OR, AND and NOT form a *universal basis*: every function from {0,1}ⁿ to {0,1}^m is implemented by a Boolean circuit, in fact a Boolean formula (Claim 2.14). A silicon chip is an implementation of a Boolean circuit in VLSI technology (footnote 2: chip circuits are not acyclic — cycles implement memory — but a computation on a chip of size C finishing in time T can be done by a Boolean circuit of size O(C·T)). A circuit only solves inputs of a certain size, which may not be a big restriction in a finite world …

<a id="pdf-da0881782a35-p119-b001"></a>
<!-- pdf-source: page=119; block=1; confidence=0.88 -->
… e.g. a small circuit for 3SAT instances of up to 100,000 variables could be found by a Manhattan-project-like effort, built as a chip, and would jeopardise every encryption scheme not using a huge key (the scenario of the Karp–Lipton quote). Circuit complexity is studied asymptotically.

<a id="pdf-da0881782a35-p119-b002"></a>
<!-- pdf-source: page=119; block=2; confidence=0.97 -->
**Definition 6.2 (Circuit families and language recognition).** Let T : ℕ → ℕ be a function. A T(n)-sized circuit family is a sequence {C_n}_{n∈ℕ} of Boolean circuits, where C_n has n inputs and a single output, such that |C_n| ≤ T(n) for every n. We say that a language L is in **SIZE**(T(n)) if there exists a T(n)-size circuit family {C_n}_{n∈ℕ} such that for every x ∈ {0,1}ⁿ, x ∈ L ⇔ C(x) = 1.

<a id="pdf-da0881782a35-p119-b003"></a>
<!-- pdf-source: page=119; block=3; confidence=0.90 -->
As noted in Claim 2.14, every language is decidable by a circuit family of size O(n2ⁿ): the circuit for length n can hardwire 2ⁿ bits saying which inputs are in the language and look the answer up.

<a id="pdf-da0881782a35-p119-b004"></a>
<!-- pdf-source: page=119; block=4; confidence=0.97 -->
**Definition 6.3.** **P/poly** is the class of languages that are decidable by polynomial-sized circuit families, in other words, ⋃_c **SIZE**(n^c).

<a id="pdf-da0881782a35-p119-b005"></a>
<!-- pdf-source: page=119; block=5; confidence=0.90 -->
Objections to the practicality of P/poly (size n¹⁰⁰) are like those for P (Section 1.5.1); moreover, the hope is to show languages such as SAT are not in P/poly, and allowing large circuits only strengthens such a result. P/poly contains P — a corollary of Theorem 6.7 below. No reasonable upper bound on P/poly exists: it contains undecidable languages.

<a id="pdf-da0881782a35-p119-b006"></a>
<!-- pdf-source: page=119; block=6; confidence=0.93 -->
**Example 6.4.** A language L is *unary* if it is a subset of {1ⁿ : n ∈ ℕ}. Every unary language has linear-size circuits (the circuit for size n hardwires a single bit saying whether 1ⁿ is in the language). Hence the undecidable unary language {1ⁿ : M_n outputs 1 on input 1ⁿ} (1), where M_n is the machine represented by (the binary expansion of) n, has linear-size circuits.

<a id="pdf-da0881782a35-p120-b001"></a>
<!-- pdf-source: page=120; block=1; confidence=0.90 -->
This suggests restricting to circuits that can actually be built by a fairly efficient TM, formalised with logspace computations. Recall that f : {0,1}* → {0,1}* is *implicitly logspace computable* if the mapping x, i ↦ f(x)_i can be computed in logarithmic space (Definition 4.14).

<a id="pdf-da0881782a35-p120-b002"></a>
<!-- pdf-source: page=120; block=2; confidence=0.97 -->
**Definition 6.5 (logspace-uniform circuit families).** A circuit family {C_n} is *logspace uniform* if there is an implicitly logspace computable function mapping 1ⁿ to the description of the circuit C_n.

<a id="pdf-da0881782a35-p120-b003"></a>
<!-- pdf-source: page=120; block=3; confidence=0.93 -->
**Representation.** A circuit of size N is represented by its N × N adjacency matrix and an array of size N giving the labels (gate type and input/output) of each node. So {C_n} is logspace uniform iff the following are computable in O(log n) space: SIZE(n), the size m of C_n (in binary); TYPE(n, i), for i ∈ [m], the label and type of the i-th node of C_n — one of {∨, ∧, ¬, NONE} and in addition ⟨OUTPUT, j⟩ or ⟨INPUT, j⟩ if i is the j-th input or output node; EDGE(n, i, j), which returns 1 if there is a directed edge in C_n between the i-th and the j-th node. Inputs and outputs of these functions take O(log |C_n|) bits; requiring O(log n) space means log |C_n| = O(log n), i.e. C_n has size at most polynomial in n.

<a id="pdf-da0881782a35-p120-b004"></a>
<!-- pdf-source: page=120; block=4; confidence=0.93 -->
**Remark 6.6.** Exercise 7 asks you to prove that the class of languages decided by such circuits does not change if we use the adjacency list (as opposed to matrix) representation. We will use the matrix representation from now on.

<a id="pdf-da0881782a35-p120-b005"></a>
<!-- pdf-source: page=120; block=5; confidence=0.97 -->
**Theorem 6.7.** A language has logspace-uniform circuits of polynomial size iff it is in P.

<a id="pdf-da0881782a35-p120-b006"></a>
<!-- pdf-source: page=120; block=6; confidence=0.97 -->
**Remark 6.8.** Note that this implies that P ⊆ P/poly.

<a id="pdf-da0881782a35-p120-b007"></a>
<!-- pdf-source: page=120; block=7; confidence=0.92 -->
**Proof sketch (Theorem 6.7), first part.** The "only if" part is trivial. The "if" part follows the proof of the Cook-Levin Theorem (Theorem 2.10). Every time-O(T(n)) TM M can be simulated by an oblivious TM M̃ (head movement independent of its input) in time O(T(n)²) (or even O(T(n) log T(n))). One can even ensure that M̃'s head movement does not depend on its work-tape contents, so by simulating M̃ while ignoring its read/write instructions one can compute, in O(log T(n)) space, for every i the positions of its heads at step i …

<a id="pdf-da0881782a35-p121-b001"></a>
<!-- pdf-source: page=121; block=1; confidence=0.92 -->
**Proof sketch (Theorem 6.7), continued.** … (footnote 3: the movement pattern is typically simple enough, e.g. T(n) left-to-right-and-back sweeps, that this takes O(log T(n)) space and polylog T(n) time). If L ∈ P it is decided by such an oblivious M̃; build a logspace-uniform family {C_n} with C_n(x) = M̃(x) for every x ∈ {0,1}ⁿ. The transcript of M̃ on x is the sequence z₁,…,z_T of snapshots (state and symbols read by all heads), each a constant-size string; z_i is computed from z_{i−1} and z_{i₁},…,z_{i_k}, where i_j is the last step at which the j-th head was in its step-i position — a constant number of constant-length strings, hence by a constant-sized circuit; and, given i and i′ < i, one can easily check whether z_i depends on z_{i′}. Composing these constant-sized circuits gives a circuit computing z_T from x; a constant-sized circuit then outputs 1 iff z_T is an accepting snapshot. So C(x) = M̃(x) for every x ∈ {0,1}ⁿ. Since C is composed of constant-sized circuits and which small circuit is applied to which nodes is determinable in logarithmic space, every bit of C's representation is computable in logarithmic space (in fact SIZE, TYPE and EDGE are computable in logarithmic space and polylogarithmic time). ∎

<a id="pdf-da0881782a35-p121-b002"></a>
<!-- pdf-source: page=121; block=2; confidence=0.97 -->
### 6.1.1 Turing machines that take advice

P/poly can be defined using Turing machines that "take advice".

**Definition 6.9.** Let T, a : ℕ → ℕ be functions. The class of languages decidable by time-T(n) TM's with a(n) advice, denoted **DTIME**(T(n))/a(n), contains every L such that there exists a sequence {α_n}_{n∈ℕ} of strings with α_n ∈ {0,1}^{a(n)} and a TM M satisfying M(x, α_n) = 1 ⇔ x ∈ L for every x ∈ {0,1}ⁿ, where on input (x, α_n) the machine M runs for at most O(T(n)) steps.

<a id="pdf-da0881782a35-p121-b003"></a>
<!-- pdf-source: page=121; block=3; confidence=0.95 -->
**Example 6.10.** Every unary language can be decided by a polynomial time Turing machine with 1 bit of advice: the advice string for inputs of length n is the single bit indicating whether or not 1ⁿ is in the language. In particular this is true of the language of Example 6.4.

<a id="pdf-da0881782a35-p122-b001"></a>
<!-- pdf-source: page=122; block=1; confidence=0.93 -->
**Theorem 6.11.** P/poly = ⋃_{c,d} DTIME(n^c)/n^d. **Proof.** If L ∈ P/poly, give the polynomial-sized description of its circuit family as advice; on inputs of size n the machine simulates the circuit. Conversely, if L is decided by a polynomial-time TM M with advice {α_n} of size a(n), a polynomial, the construction of Theorem 6.7 gives for every n a polynomial-sized circuit D_n with D_n(x, α) = M(x, α) for all x ∈ {0,1}ⁿ, α ∈ {0,1}^{a(n)}; let C_n be D_n with α_n "hardwired" as its second input, mapping x to D_n(x, α_n). ∎

<a id="pdf-da0881782a35-p122-b002"></a>
<!-- pdf-source: page=122; block=2; confidence=0.93 -->
**Remark 6.12.** By "hardwiring" an input into a circuit we mean taking a circuit C with two inputs x ∈ {0,1}ⁿ, y ∈ {0,1}^m and transforming it into the circuit C_y that for every x returns C(x, y). It is easy to do so while ensuring that the size of C_y is not greater than the size of C. This simple idea is often used in complexity theory.

<a id="pdf-da0881782a35-p122-b003"></a>
<!-- pdf-source: page=122; block=3; confidence=0.93 -->
## 6.2 Karp-Lipton Theorem

Karp and Lipton asked whether SAT is in P/poly and showed the answer is "NO" if the polynomial hierarchy does not collapse.

**Theorem 6.13 (Karp-Lipton, with improvements by Sipser).** If NP ⊆ P/poly then PH = Σ₂^p.

<a id="pdf-da0881782a35-p122-b004"></a>
<!-- pdf-source: page=122; block=4; confidence=0.90 -->
**Proof (Theorem 6.13), first part.** It suffices to show Π₂^p ⊆ Σ₂^p, in particular that Σ₂^p contains the Π₂^p-complete language Π₂SAT of true formulae ∀u ∈ {0,1}ⁿ ∃v ∈ {0,1}ⁿ φ(u, v) = 1 (2), φ unquantified. If NP ⊆ P/poly, a p(n)-sized family {C_n} decides, for every φ and u, whether some v has φ(u, v) = 1; by the search-to-decision reduction of Theorem 2.19 there is a q(n)-sized family {C′_n} that outputs such a v when one exists. C′_n is describable in 10q(n)² bits, so if (2) is true then ∃w ∈ {0,1}^{10q(n)²} ∀u ∈ {0,1}ⁿ: w describes a circuit C′ s.t. φ(u, C′(φ, u)) = 1 (3) …

<a id="pdf-da0881782a35-p123-b001"></a>
<!-- pdf-source: page=123; block=1; confidence=0.92 -->
**Proof (Theorem 6.13), end.** … and if (2) is false then (3) is false as well (regardless of whether P = NP), so (3) is equivalent to (2). Since evaluating a circuit is polynomial-time, the truth of (3) can be decided in Σ₂^p. ∎

<a id="pdf-da0881782a35-p123-b002"></a>
<!-- pdf-source: page=123; block=2; confidence=0.96 -->
**Theorem 6.14 (Karp-Lipton, attributed to A. Meyer).** If EXP ⊆ P/poly then EXP = Σ₂^p. (Proof left as Exercise 3.)

<a id="pdf-da0881782a35-p123-b003"></a>
<!-- pdf-source: page=123; block=3; confidence=0.90 -->
With the time hierarchy theorem (Theorem 3.1), the previous theorem implies that if P = NP then EXP ⊄ P/poly: upper bounds (here NP ⊆ P) can potentially be used to prove circuit lower bounds.

<a id="pdf-da0881782a35-p123-b004"></a>
<!-- pdf-source: page=123; block=4; confidence=0.88 -->
## 6.3 Circuit lowerbounds

Since P ⊆ P/poly, NP ⊄ P/poly would give P ≠ NP, and Karp–Lipton gives hope that NP ⊄ P/poly. Circuits seem to let one "peer into the guts" of computation and perhaps avoid the limits of relativizing methods (Chapter 3). But after two decades the best circuit size lower bound for an NP language is only 5n (Exercise 1 gives a better one for a language in PH); restricted circuit models fare better (Chapter 13). It is easy to show that for large n almost every Boolean function requires large circuits.

<a id="pdf-da0881782a35-p123-b005"></a>
<!-- pdf-source: page=123; block=5; confidence=0.93 -->
**Theorem 6.15.** For n ≥ 100, almost all boolean functions on n variables require circuits of size at least 2ⁿ/(10n). **Proof.** Counting: there are at most s^{3s} circuits of size s (count labeled directed graphs with in-degree at most 2), which bounds the number of functions with circuits of size s. For s = 2ⁿ/(10n) this is at most 2^{2ⁿ/10}, minuscule compared with the 2^{2ⁿ} Boolean functions on n variables. ∎

<a id="pdf-da0881782a35-p123-b006"></a>
<!-- pdf-source: page=123; block=6; confidence=0.92 -->
**Remark 6.16.** Equivalently, with high probability a random function from {0,1}ⁿ to {0,1} has no circuit of size 2ⁿ/10n. Showing that an object with certain properties exists by arguing that a random object has them with high probability is the *probabilistic method*, used repeatedly in the book. The counting argument does not yield an explicit function (say an NP language) requiring large circuits.

<a id="pdf-da0881782a35-p124-b001"></a>
<!-- pdf-source: page=124; block=1; confidence=0.94 -->
## 6.4 Non-uniform hierarchy theorem

**Theorem 6.17.** For every functions T, T′ : ℕ → ℕ with 2ⁿ/(100n) > T′(n) > T(n) > n and T(n) log T(n) = o(T′(n)), **SIZE**(T(n)) ⊊ **SIZE**(T′(n)).

**Proof idea (shown for SIZE(n) ⊊ SIZE(n²)).** Diagonalization (Chapter 3) does not seem to work; the counting argument does. For every ℓ some f : {0,1}^ℓ → {0,1} is not computable by 2^ℓ/(10ℓ)-sized circuits, while every such function is computable by a 2^ℓ·10ℓ-sized circuit. With ℓ = 1.1 log n and g : {0,1}ⁿ → {0,1} applying f to the first ℓ bits of its input: g ∈ SIZE(2^ℓ 10ℓ) = SIZE(11 n^{1.1} log n) ⊆ SIZE(n²) and g ∉ SIZE(2^ℓ/(10ℓ)) = SIZE(n^{1.1}/(11 log n)) ⊇ SIZE(n). ∎

<a id="pdf-da0881782a35-p124-b002"></a>
<!-- pdf-source: page=124; block=2; confidence=0.88 -->
## 6.5 Finer gradations among circuit classes

Subclasses of P/poly matter because lower bounds for them may give insight into separating NP from P/poly, and because they model interesting computation, most notably *massively parallel computers*: off-the-shelf processors linked by an *interconnection network* (e.g. the *hypercube*) allowing interprocessor communication in O(log n) steps, computing in lock-step with small per-step work on O(log n) bits. Details are omitted (Leighton [Lei92] is the standard reference) since Theorem 6.24 does not depend on them; the aim is a loose characterization.

<a id="pdf-da0881782a35-p125-b001"></a>
<!-- pdf-source: page=125; block=1; confidence=0.95 -->
### 6.5.1 Parallel computation and NC

**Definition 6.18.** A computational task is said to have *efficient parallel algorithms* if inputs of size n can be solved using a parallel computer with n^{O(1)} processors and in time log^{O(1)} n.

<a id="pdf-da0881782a35-p125-b002"></a>
<!-- pdf-source: page=125; block=2; confidence=0.90 -->
**Example 6.19.** Adding two n-bit numbers: the gradeschool algorithm propagates a carry bit and uses n steps; *carry lookahead* assigns a processor per bit position and propagates carries by communication, using O(n) processors and O(log n) time. Integer multiplication and (non-intuitively) division also have efficient parallel algorithms.

<a id="pdf-da0881782a35-p125-b003"></a>
<!-- pdf-source: page=125; block=3; confidence=0.90 -->
**Example 6.20.** Many matrix computations (product, rank, determinant, inverse) are efficiently parallel (exercises); so are some graph algorithms (shortest paths, minimum spanning tree). Minimum matching, maximum flows and linear programming are not known (and conjectured not) to have good parallel implementations; see P-completeness below.

<a id="pdf-da0881782a35-p125-b004"></a>
<!-- pdf-source: page=125; block=4; confidence=0.96 -->
The *depth* of a circuit is the length of the longest directed path from an input node to the output node.

**Definition 6.21 (Nick's class or NC).** A language is in NC^i if there are constants c, d > 0 such that it can be decided by a logspace-uniform family of circuits {C_n} where C_n has size O(n^c) and depth O(log^d n). The class NC is ⋃_{i≥1} NC^i. *Transcription note:* as printed, the depth exponent is d, not i.

<a id="pdf-da0881782a35-p125-b005"></a>
<!-- pdf-source: page=125; block=5; confidence=0.96 -->
**Definition 6.22 (AC).** The class AC^i is defined similarly to NC^i except gates are allowed to have unbounded fanin. The class AC is ⋃_{i≥0} AC^i.

<a id="pdf-da0881782a35-p126-b001"></a>
<!-- pdf-source: page=126; block=1; confidence=0.92 -->
Since unbounded (but poly(n)) fanin can be simulated by a tree of ORs/ANDs of depth O(log n), NC^i ⊆ AC^i ⊆ NC^{i+1}, and the inclusion is strict for i = 0 (Chapter 13). NC⁰ is extremely limited (the output depends on a constant number of input bits); AC⁰ is not.

<a id="pdf-da0881782a35-p126-b002"></a>
<!-- pdf-source: page=126; block=2; confidence=0.92 -->
**Example 6.23.** PARITY = {x : x has an odd number of 1s} is in NC¹: a binary tree whose subtrees compute the parity of the two halves of x, combined at the root; unwrapping the recursion gives depth O(log n).

<a id="pdf-da0881782a35-p126-b003"></a>
<!-- pdf-source: page=126; block=3; confidence=0.93 -->
**Theorem 6.24.** A language has efficient parallel algorithms iff it is in NC. **Proof.** If L ∈ NC via circuits C_n of size N = O(n^c) and depth D = O(log^d n), configure a parallel computer with N nodes, one processor per circuit node (done once); each processor sends its node's output to the nodes that need it. With message delivery in O(log N) time the total time is O(log^{d+1} N). Conversely, a circuit of N·D nodes in D layers, node i of layer t performing processor i's computation at time t, with wires in place of the network. ∎

<a id="pdf-da0881782a35-p126-b004"></a>
<!-- pdf-source: page=126; block=4; confidence=0.93 -->
### 6.5.2 P-completeness

Whether P = NC is a major open question, believed NO (even PH vs. NC¹ is not separated); P-completeness studies which problems are likely in NC.

**Definition 6.25.** A language is P-complete if it is in P and every language in P is logspace-reducible to it (as per Definition 4.14).

<a id="pdf-da0881782a35-p126-b005"></a>
<!-- pdf-source: page=126; block=5; confidence=0.95 -->
**Theorem 6.26** (left as Exercise 12). If language L is P-complete then 1. L ∈ NC iff P = NC; …

<a id="pdf-da0881782a35-p127-b001"></a>
<!-- pdf-source: page=127; block=1; confidence=0.95 -->
**Theorem 6.26 (continued).** … 2. L ∈ L iff P = L (where L is the set of languages decidable in logarithmic space, Definition 4.5).

<a id="pdf-da0881782a35-p127-b002"></a>
<!-- pdf-source: page=127; block=2; confidence=0.95 -->
**Theorem 6.27.** Let CIRCUIT-EVAL denote the language consisting of all pairs ⟨C, x⟩ such that C is an n-inputs single-output circuit and x ∈ {0,1}ⁿ satisfies C(x) = 1. Then CIRCUIT-EVAL is P-complete. **Proof.** The language is clearly in P. A logspace-reduction from any other language in P to it is implicit in the proof of Theorem 6.7. ∎

<a id="pdf-da0881782a35-p127-b003"></a>
<!-- pdf-source: page=127; block=3; confidence=0.92 -->
## 6.6 Circuits of exponential size

Every language has circuits of size O(n2ⁿ), but finding them may be hard or undecidable; under a uniformity condition some languages' circuit complexity could exceed n2ⁿ. Alternative definitions of familiar classes follow, analogous to Theorem 6.7 for P.

**Definition 6.28 (DC-Uniform).** Let {C_n}_{n≥1} be a circuit family. It is a *Direct Connect uniform* (DC uniform) family if, given ⟨n, i⟩, we can compute in polynomial time the i-th bit of (the representation of) the circuit C_n. Concretely, with the adjacency matrix representation, {C_n} is DC uniform iff the functions SIZE, TYPE and EDGE defined in Remark ?? are computable in polynomial time. (The circuits may have exponential size but a succinct representation.) *Transcription note:* "Remark ??" is an unresolved reference in the draft; SIZE, TYPE and EDGE are defined after Definition 6.5 (`p120-b003`).

<a id="pdf-da0881782a35-p127-b004"></a>
<!-- pdf-source: page=127; block=4; confidence=0.94 -->
**Theorem 6.29** (left as Exercise 13). L ∈ PH iff L can be computed by a DC uniform circuit family {C_n} that uses AND, OR, NOT gates; has size 2^{n^{O(1)}} and constant depth (i.e., depth O(1)); has gates with unbounded (exponential) fanin; and has NOT gates only at the input level. Dropping the constant-depth restriction gives exactly EXP (Exercise 14).

<a id="pdf-da0881782a35-p128-b001"></a>
<!-- pdf-source: page=128; block=1; confidence=0.97 -->
## 6.7 Circuit Satisfiability and an alternative proof of the Cook-Levin Theorem

Boolean circuits can be used to define the following NP-complete language:

**Definition 6.30.** The *circuit satisfiability* language CKT-SAT consists of all (strings representing) circuits with a single output that have a satisfying assignment. That is, a string representing an n-input circuit C is in CKT-SAT iff there exists u ∈ {0,1}ⁿ such that C(u) = 1.

<a id="pdf-da0881782a35-p128-b002"></a>
<!-- pdf-source: page=128; block=2; confidence=0.97 -->
CKT-SAT is clearly in NP because the satisfying assignment can serve as the certificate. It is also clearly NP-hard as every CNF formula is in particular a Boolean circuit. However, CKT-SAT can also be used to give an alternative proof (or, more accurately, a different presentation of the same proof) for the Cook-Levin Theorem by combining the following two lemmas:

<a id="pdf-da0881782a35-p128-b003"></a>
<!-- pdf-source: page=128; block=3; confidence=0.97 -->
**Lemma 6.31.** CKT-SAT is NP-hard.

<a id="pdf-da0881782a35-p128-b004"></a>
<!-- pdf-source: page=128; block=4; confidence=0.97 -->
**Proof (Lemma 6.31).** Let L be an NP-language and let p be a polynomial and M a polynomial-time TM such that x ∈ L iff M(x, u) = 1 for some u ∈ {0,1}^{p(|x|)}. We reduce L to CKT-SAT by mapping (in polynomial-time) x to a circuit C_x with p(|x|) inputs and a single output such that C_x(u) = M(x, u) for every u ∈ {0,1}^{p(|x|)}. Clearly, x ∈ L ⇔ C_x ∈ CKT-SAT and so this suffices to show that L ≤_P CKT-SAT.

Yet, it is not hard to come up with such a circuit. Indeed, the proof of Theorem 6.7 yields a way to map M, x into the circuit C_x in logarithmic space (which in particular implies polynomial time). ∎

<a id="pdf-da0881782a35-p128-b005"></a>
<!-- pdf-source: page=128; block=5; confidence=0.97 -->
**Lemma 6.32.** CKT-SAT ≤p 3SAT

<a id="pdf-da0881782a35-p128-b006"></a>
<!-- pdf-source: page=128; block=6; confidence=0.96 -->
**Proof (Lemma 6.32).** As mentioned above this follows from the Cook-Levin theorem but we give here a direct reduction. If C is a circuit, we map it into a 3CNF formula φ as follows:

For every node v_i of C we will have a corresponding variable z_i in φ. If the node v_i is an AND of the nodes v_j and v_k then we add to φ clauses that are equivalent to the condition "z_i = (z_j ∧ z_k)". That is, we add the clauses

(z̄_i ∨ z̄_j ∨ z_k) ∧ (z̄_i ∨ z_j ∨ z̄_k) ∧ (z̄_i ∨ z_j ∨ z_k) ∧ (z_i ∨ z̄_j ∨ z̄_k).

Similarly, if v_i is an OR of v_j and v_k then we add clauses equivalent to "z_i = (z_j ∨ z_k)", and if v_i is the NOT of v_j then we add the clauses (z_i ∨ z_j) ∧ (z̄_i ∨ z̄_j).

Finally, if v_i is the output node of C then we add the clause z_i to φ. It is not hard to see that the formula φ will be satisfiable if and only if the circuit C is. ∎

*Transcription note:* the four AND clauses are copied as printed (checked against the page image); they exclude exactly the four assignments inconsistent with z_i = z_j ∧ z_k ((z_i; z_j, z_k) = (1; 1,0), (1; 0,1), (1; 0,0), (0; 1,1)). The draft does not list the OR clauses explicitly.

<a id="pdf-da0881782a35-p129-b001"></a>
<!-- pdf-source: page=129; block=1; confidence=0.90 -->
**What have we learned?** Boolean circuits are an alternative computational model to TMs. P/poly (languages decidable by polynomial-sized circuits) is a strict superset of P but does not contain NP unless the hierarchy collapses. Almost every function from {0,1}ⁿ to {0,1} requires exponential-sized circuits; finding even one such function in NP would show P ≠ NP. NC (uniformly constructible circuits of polylogarithmic depth and polynomial size) corresponds to efficiently parallelisable tasks.

<a id="pdf-da0881782a35-p129-b002"></a>
<!-- pdf-source: page=129; block=2; confidence=0.88 -->
**Chapter notes and history.** The Karp-Lipton theorem is from [KL82]; Karp and Lipton also gave a more general definition of advice, C/a(n) for every class C, not used here since it does not capture the intuitive notion of advice for classes such as NP ∩ coNP and BPP. NC algorithms and parallel computation are discussed in Leighton [?].

<a id="pdf-da0881782a35-p129-b003"></a>
<!-- pdf-source: page=129; block=3; confidence=0.86 -->
**Exercises 1–6.** §1 [Kannan, Kan82]: for every k > 0, PH contains languages of circuit complexity Ω(n^k) (hint: the existence proof of hard functions). §2: the same with Σ₂^p in place of PH. §3 ([KL82], attributed to A. Meyer): if EXP ⊆ P/poly then EXP = Σ₂^p. §4: if P = NP then EXP has a language requiring circuits of size 2ⁿ/n. §5: every sparse language (|L ∩ {0,1}ⁿ| ≤ p(n)) is in P/poly. §6 ("X's Theorem 19??", unresolved in the draft): if a sparse language is NP-complete then P = NP (strengthens Exercise 13 of Chapter 2).

<a id="pdf-da0881782a35-p130-b001"></a>
<!-- pdf-source: page=130; block=1; confidence=0.86 -->
**Exercises 6 (hint)–15.** §6 hint: a recursive exponential-time search for a satisfying assignment above a given v, pruned using the reduction from SAT to L. §7: a logspace implicitly computable map from the adjacency-matrix to the adjacency-list representation of an n-vertex graph. §8 (Open): if every NP language has linear-size circuits, can one show more than PH = Σ₂^p? §9: NC circuits for (a) the product of two n × n matrices, (b) Aⁿ by repeated squaring; (c) hence PATH (and every NL language) is in NC. §10: polynomial-size formulae (circuits with outdegree 1) compute exactly nonuniform NC¹ (hint: balanced tree separators). §11: "Show that NC¹ = L" [sic as printed; the known inclusion is NC¹ ⊆ L]; conclude PSPACE ≠ NC¹. §12: prove Theorem 6.26. §13: prove Theorem 6.29. §14: EXP is exactly the languages with DC uniform circuits of size 2^{n^c}. §15: if linear programming has a fast parallel algorithm then P = NC (hint: express CIRCUIT-EVAL as a linear program, using x ∨ y = 1 iff x + y ≥ 1, with care for real-valued variables).
