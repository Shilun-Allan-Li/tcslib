<!-- generated-by: maintainer transcription of the passages used (DW-7), read from page images -->
<!-- source-pdf-sha256: 06fd3eeccecf8e3e42c0e33f50356588ea9377b2f7d2642b4d3e0370f4ca7831 -->
<!-- validation-status: scoped transcription for DW-7; awaiting Codex source review -->

# Bounded-Width Polynomial-Size Branching Programs Recognize Exactly Those Languages in NC¹

David A. Mix Barrington. *Journal of Computer and System Sciences* 38(1):150–164, February 1989
(received 22 August 1986, revised 7 April 1987; preliminary version STOC 1986). Uploaded copy: a
15-page reprint scan with no text layer (tag `Bar89`).

**Scope.** Only the passages that the phase-6 plan uses are transcribed (DW-7; GSW ruling Q13 and
addendum): the abstract, §1 (instructions, width-$w$ branching programs, yields, recognition,
permutation branching programs), and §3 (five-cycle recognition, Theorem 1 with Lemmas 1–3, the
example, the proof of Theorem 1, Theorem 2 with its proof, and the Corollary). §2 and §4–§6 are
not transcribed. The PDF is not committed. Anchors use the physical PDF page; the printed page is
$149+p$ (`p001` is printed page 150). The PDF has no text layer, so the scoped raw file
`barrington-1989-bounded-width-bp.raw.md` is a plain-text reading of the page images (rendered
at 110–170 dpi), not a machine extraction. Mathematics is set in LaTeX; the wording is the
paper's. Notes marked *Transcription note* are not part of the source.

<a id="pdf-06fd3eeccecf-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.90 -->

**Abstract (p. 150).** We show that any language recognized by an $NC^1$ circuit (fan-in 2, depth
$O(\log n)$) can be recognized by a width-5 polynomial-size branching program. As any bounded-width
polynomial-size branching program can be simulated by an $NC^1$ circuit, we have that the class of
languages recognized by such programs is exactly nonuniform $NC^1$. Further, following Ruzzo
(*J. Comput. System Sci.* 22 (1981), 365–383) and Cook (*Inform. and Control* 64 (1985) 2–22), if
the branching programs are restricted to be ATIME($\log n$)-uniform, they recognize the same
languages as do ATIME($\log n$)-uniform $NC^1$ circuits, that is, those languages in
ATIME($\log n$). We also extend the method of proof to investigate the complexity of the word
problem for a fixed permutation group and show that polynomial size *circuits* of width 4 also
recognize exactly nonuniform $NC^1$.

<a id="pdf-06fd3eeccecf-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.90 -->

## 1. Definitions

**Section 1, instructions, branching programs and yields (pp. 150–151).** Let
$[w]=\{1,\dots,w\}$. An *instruction* is a triple $\langle j,f,g\rangle$ in which $j$ is the index
of an input variable $x_j$ and $f$ and $g$ are maps from $[w]$ to $[w]$. The meaning of an
instruction $\langle j,f,g\rangle$ is "evaluate to $f$ if $x_j=1$, otherwise evaluate to $g$." A
width-$w$ branching program of length $l$ (a $w$-BP) is a sequence of instructions
$\langle j_i,f_i,g_i\rangle$ for $1\le i\le l$. Given a 0–1 assignment $\mathbf x$ to the input
variables $x_1,\dots,x_n$, a branching program $B$ *yields* the function $B(\mathbf x)$ which is
the composition of the functions produced by each of the instructions. For example, let $w=2$, let
$e$ be the identity function on $w$, and let $(1\,2)$ be the transposition of $w$'s two elements.
Then the program consisting of instructions

$$
\langle 7,(1\,2),e\rangle\langle 4,e,(1\,2)\rangle\langle 8,(1\,2),e\rangle
$$

yields $(1\,2)$ if the exclusive OR of $x_7$, $\bar x_4$, and $x_8$ is one and yields $e$
otherwise.

To recognize a language $L\subseteq\{0,1\}^*$ we need a family of width-$w$ branching programs
$\langle B_n\rangle$, where $B_n$ for each positive integer $n$ takes $n$ Boolean inputs. Length and
size can then be viewed as functions of $n$. We say that $\langle B_n\rangle$ *recognizes* $L$ if
for each $n$ there is a set $F_n$ of functions from $[w]$, such that for all
$\mathbf x\in\{0,1\}^n$, $\mathbf x\in L$ iff $B(\mathbf x)\in F_n$.

$B$ is a *permutation branching program* ($w$-PBP) if each $f_i$ and $g_i$ is a permutation of
$[w]$. In general we will use Greek letters for permutations.

*Transcription note.* The first paragraph is on p. 150 and the rest on p. 151; the block keeps the
definition together. In an instruction the map used when $x_j=1$ comes **first**; BV14's tuples
$(\mathsf{var}(t),\sigma_{t,0},\sigma_{t,1})$ list the map for $x=0$ first.

<a id="pdf-06fd3eeccecf-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.90 -->

**Section 1, the traditional model and the main result (p. 151).** The traditional notion (e.g.,
in [10]) of a width-$w$ branching program is of a rectangular $w$ by $l$ array of nodes. Each node
in row $i$ is assigned an input variable and two out-edges leading to nodes in row $i+1$. Our model
can be viewed this way but further requires that each node in a column be assigned the same
variable. This requirement may be enforced at a cost of increasing the length polynomially and
doubling the width. The traditional notion also defines the recognition of a set by a branching
program in a different way, by fixing a start node (a source) and partitioning the sink nodes into
accepting and rejecting. This difference may be dealt with in a similar manner. Thus both models
define the same class BWBP of languages recognized by bounded-width polynomial-size branching
programs. Our main result is that BWBP is equal to (nonuniform) $NC^1$.

In general we will speak of nonuniform circuits and branching programs, so that an $NC^1$ circuit
will be simply a Boolean circuit with fan-in 2 and depth $O(\log n)$ (and hence polynomial size).
Uniformity considerations will be postponed until Section 6, where we will make the appropriate
definitions.

<a id="pdf-06fd3eeccecf-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.90 -->

## 3. The Main Result

**Section 3, five-cycle recognition (p. 152).** We say that a 5-PBP $B$ *five-cycle recognizes* a
set $A\subseteq[2]^n$ if there exists a five-cycle $\sigma$ (called the *output*) in the permutation
group $S_5$ such that $B(\mathbf x)=\sigma$ if $\mathbf x\in A$ and $B(\mathbf x)=e$ if
$\mathbf x\notin A$ ($e$ is the identity permutation). For example, using the usual cycle notation
for elements of $S_5$, the one-instruction program $\langle 1,(12345),e\rangle$ five-cycle
recognizes the set $A=\{\mathbf x:x_1=1\}$ with output $(12345)$.

<a id="pdf-06fd3eeccecf-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.90 -->

**Theorem 1.** Let $A$ be recognized by a depth $d$ fan-in 2 Boolean circuit (we will assume that
the circuit consists of AND and OR gates with a bottom level of inputs and negated inputs). Then
$A$ is five-cycle recognized by a 5-PBP $B$ of length at most $4^d$.

<a id="pdf-06fd3eeccecf-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.90 -->

**Lemma 1.** If $B$ five-cycle recognizes $A$ with output $\sigma$ and $\tau$ is any five-cycle,
then there exists a 5-PBP $B'$, of the same length as $B$, which five-cycle recognizes $A$ with
output $\tau$.

*Proof.* Since $\sigma$ and $\tau$ are both five-cycles there exists some permutation $\theta$ with
$\tau=\theta\sigma\theta^{-1}$. To get $B'$, simply change each instruction of $B$, replacing each
$\sigma_i$ and $\tau_i$ by $\theta\sigma_i\theta^{-1}$ and $\theta\tau_i\theta^{-1}$. $\blacksquare$

*Transcription note.* In this proof $\sigma_i,\tau_i$ name the two permutations of the $i$th
instruction (the $f_i,g_i$ of §1).

<a id="pdf-06fd3eeccecf-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.90 -->

**Lemma 2.** If $A$ can be five-cycle recognized in length $l$, so can its complement.

*Proof.* Let $B$ five-cycle recognize $A$ with output $\sigma$. Call the last instruction of $B$
$\langle i,\mu,\nu\rangle$. Let $B'$ be identical to $B$ except for last instruction
$\langle i,\mu\sigma^{-1},\nu\sigma^{-1}\rangle$. Then $B'(\mathbf x)=e$ if $\mathbf x\in A$ and
$B'(\mathbf x)=\sigma^{-1}$ if $\mathbf x\notin A$. Thus $B'$ five-cycle recognizes the complement
of $A$. $\blacksquare$

<a id="pdf-06fd3eeccecf-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.90 -->

**Lemma 3.** There are two five-cycles $\sigma_1$ and $\sigma_2$ in $S_5$ whose commutator is a
five-cycle. (The commutator of $a$ and $b$ is $aba^{-1}b^{-1}$.)

*Proof* (p. 153). $(12345)(13542)(54321)(24531)=(13254)$. $\blacksquare$

*Transcription note (composition order; checked by computation, not part of the source).* The
displayed identity holds when a product is read left to right, the leftmost permutation acting
first: then $(54321)=(12345)^{-1}$, $(24531)=(13542)^{-1}$, and
$(12345)(13542)(12345)^{-1}(13542)^{-1}=(13254)$. Read right to left (the convention of Mathlib's
`Equiv.Perm` multiplication, which applies the right factor first) the same four factors give
$(14352)$, also a five-cycle. The same left-to-right reading makes Lemma 2's
$B'(\mathbf x)=B(\mathbf x)\sigma^{-1}$ and the yield of a program "the composition of the
functions produced by each of the instructions" in program order. A formalization must fix the
order once; the commutator is a five-cycle in either reading.

<a id="pdf-06fd3eeccecf-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.90 -->

**Example (p. 153).** Consider the 5-PBP

$$
\langle 1,(12345),e\rangle\ \langle 2,(13542),e\rangle\ \langle 1,(54321),e\rangle\ \langle 2,(24531),e\rangle
$$

which yields $(13254)$ as calculated above if $x_1=x_2=1$. If either $x_1$ or $x_2$ is zero, the
yield is $e$ because of cancellation. So this 5-PBP five-cycle recognizes the set
$\{\mathbf x:x_1=x_2=1\}$. We now generalize this construction to prove our theorem.

<a id="pdf-06fd3eeccecf-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.90 -->

**Proof of Theorem 1 (p. 153).** Let $C$ be a depth $d$, fan-in 2 circuit of AND and OR gates, with
a bottom level of inputs and negated inputs. We will show by induction on $d$ that the set
recognized by $C$ can be five-cycle recognized by a 5-PBP. If $d=0$, $C$ has no gates and the set
$A$ can easily be recognized by a one-instruction 5-PBP. Assume without loss of generality that the
output gate of $C$ is an AND gate. If it is an OR gate, appeal to Lemma 2. Then the set $A$
recognized by $C$ is an intersection $A_1\cap A_2$, where $A_1$ and $A_2$ are recognized by circuits
of depth $d-1$ and thus are five-cycle recognized by $B_1$ and $B_2$ of length at most $4^{d-1}$.
Let $B_1$ and $B_2$ have the particular outputs $\sigma_1$ and $\sigma_2$ as defined in Lemma 3, and
$B'_1$ and $B'_2$ have outputs $\sigma_1^{-1}$ and $\sigma_2^{-1}$ (this last is possible by
Lemma 1). Let $B$ be the concatenation $B_1B_2B'_1B'_2$. $B$ yields $e$ unless the input is in both
$A_1$ and $A_2$, but yields the commutator of the two outputs if the input is in $A$. This
commutator is a five-cycle, and so $B$ five-cycle recognizes $A$. $B$ has length at most $4^d$.
Given a circuit and a desired output, this proof gives a deterministic method of constructing the
5-PBP. $\blacksquare$

*Transcription note.* Two steps are left implicit in the source and must be explicit in a
formalization: (i) for an OR gate, "appeal to Lemma 2" means De Morgan — complement the two
sub-programs (Lemma 2), take the AND construction, and complement the result — which keeps the
length bound because Lemma 2 does not change length; (ii) a one-input gate or a constant needs its
own (trivial) case if the circuit model allows them.

<a id="pdf-06fd3eeccecf-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.90 -->

**Theorem 2 (p. 153).** The following result is a nonuniform version of the well-known result that
regular languages can be recognized by $NC^1$ circuits. The proof in the uniform case essentially
appears in [30] and is given explicitly in [22].

*Theorem 2.* If $A\subseteq[2]^n$ is recognized by a $w$-BP $B$ of length $l$, $A$ is recognized by
a fan-in 2 circuit of depth $O(\log l)$, where the constant depends on $w$.

*Proof.* Recall our notion of recognition—we say that $B$ accepts $\mathbf x$ if $B(\mathbf x)$ is
in some arbitrary subset of the functions from $[w]$ to $[w]$. We can represent such a function $f$
by $w^2$ Boolean variables telling whether $f(i)=j$ for each $i$ and $j$. The composition of two
such functions so represented may be computed by a fixed circuit whose size depends only on $w$.
Our circuit for $A$ will have a constant-depth section to find the function yielded by a each
instruction of $B$, a binary tree of composition circuits, and a constant-depth section at the top
to determine acceptance given the function yielded by $B$. $\blacksquare$

<a id="pdf-06fd3eeccecf-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.90 -->

**Corollary (p. 153).** The classes of languages BWBP and nonuniform $NC^1$ are identical. They
equal the class of languages recognized by polynomial-length 5-PBPs.
