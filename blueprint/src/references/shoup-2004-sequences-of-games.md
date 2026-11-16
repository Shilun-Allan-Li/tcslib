<!-- generated-by: maintainer transcription of the passages used (DW-8) -->
<!-- source-pdf-sha256: fde1f65e83ec85297f58840bf87de15fb68e91ada8aefaf77db3b153cf826820 -->
<!-- validation-status: scoped transcription for DW-8; awaiting Codex source review -->

# Sequences of Games: A Tool for Taming Complexity in Security Proofs

Victor Shoup. Cryptology ePrint Archive, Report 2004/332 (tag `Sho04`). Uploaded copy: the
revision dated **January 18, 2006**, 33 PDF pages; the title page records "First public
version: Nov. 30, 2004".

**Scope.** Only the passages that the relational simulation lemma uses are transcribed
(DW-8; pairing ruling Q11): §1 (Introduction) and §1.1 (The Basic Idea), which set up the
sequence-of-games framework and give the three transition types — transitions based on
indistinguishability, transitions based on failure events (with Lemma 1, the Difference
Lemma, and its generalization) and **bridging steps**. One worked bridging step is
transcribed as context, from §4.2 (Game 2 of the universal-hash input-extension proof,
p. 13), because it is the kind of state-reformulation step the cited lemma abstracts. The
PDF is not committed. Physical and printed pages coincide. The scoped raw extraction is
`shoup-2004-sequences-of-games.raw.md`. Mathematics is set in LaTeX; the wording is the
paper's. Notes marked *Transcription note* are not part of the source.

<a id="pdf-fde1f65e83ec-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.95 -->

**Title and abstract (p. 1).** Sequences of Games: A Tool for Taming Complexity in
Security Proofs. Victor Shoup. January 18, 2006.

> **Abstract.** This paper is brief tutorial on a technique for structuring security proofs
> as sequences games.

*Transcription note.* The abstract is transcribed as printed, including "is brief tutorial"
and "sequences games"; neither is a transcription slip.

<a id="pdf-fde1f65e83ec-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.95 -->

**Section 1, Introduction (p. 1).** Security proofs in cryptography may sometimes be
organized as sequences of games. In certain circumstances, this can be a useful tool in
taming the complexity of security proofs that might otherwise become so messy, complicated,
and subtle as to be nearly impossible to verify. This technique appears in the literature in
various styles, and with various degrees of rigor and formality. This paper is meant to
serve as a brief tutorial on one particular "style" of employing this technique, which seems
to achieve a reasonable level of mathematical rigor and clarity, while not getting bogged
down with too much formalism or overly restrictive rules. We do not make any particular
claims of originality — it is simply hoped that others might profit from some of the ideas
discussed here in reasoning about security.

At the outset, it should be noted that this technique is certainly not applicable to all
security proofs. Moreover, even when this technique is applicable, it is only a tool for
organizing a proof — the actual ideas for a cryptographic construction and security analysis
must come from elsewhere.

<a id="pdf-fde1f65e83ec-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.95 -->

**Section 1.1, The Basic Idea (p. 1).** Security for cryptograptic primitives is typically
defined as an attack game played between an adversary and some benign entity, which we call
the challenger. Both adversary and challenger are probabilstic processes that communicate
with each other, and so we can model the game as a probability space. Typically, the
definition of security is tied to some particular event $S$. Security means that for every
"efficient" adversary, the probability that event $S$ occurs is "very close to" some
specified "target probabilty": typically, either $0$, $1/2$, or the probability of some
event $T$ in some other game in which the same adversary is interacting with a different
challenger.

*Transcription note.* "cryptograptic", "probabilstic" and "probabilty" are transcribed as
printed.

<a id="pdf-fde1f65e83ec-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.95 -->

**Section 1.1, the sequence-of-games framework (p. 2).** Now, to prove security using the
sequence-of-games approach, one prodceeds as follows. One constructs a sequence of games,
Game 0, Game 1, …, Game $n$, where Game 0 is the original attack game with respect to a
given adversary and cryptographic primitive. Let $S_0$ be the event $S$, and for
$i=1,\dots,n$, the construction defines an event $S_i$ in Game $i$, usually in a way
naturally related to the definition of $S$. The proof shows that $\Pr[S_i]$ is negligibly
close to $\Pr[S_{i+1}]$ for $i=0,\dots,n-1$, and that $\Pr[S_n]$ is equal (or negligibly
close) to the "target probability." From this, and the fact that $n$ is a constant, it
follows that $\Pr[S]$ is negligibly close to the "target probability," and security is
proved.

That is the general framework of such a proof. However, in constructing such proofs, it is
desirable that the changes between succesive games are very small, so that analyzing the
change is as simple as possible. From experience, it seems that **transitions between
successive games can be restricted to one of three types**:

*Transcription note.* "prodceeds" and "succesive" are transcribed as printed.

<a id="pdf-fde1f65e83ec-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.95 -->

**Transition type 1: transitions based on indistinguishability (p. 2).** In such a
transition, a small change is made that, if detected by the adversary, would imply an
efficient method of distinguishing between two distributions that are indistinguishable
(either statistically or computationally). For example, suppose $P_1$ and $P_2$ are assumed
to be computationally indistinguishable distributions. To prove that
$|\Pr[S_i]-\Pr[S_{i+1}]|$ is negligible, one argues that there exists a distinguishing
algorithm $D$ that "interpolates" between Game $i$ and Game $i+1$, so that when given an
element drawn from distribution $P_1$ as input, $D$ outputs $1$ with probability $\Pr[S_i]$,
and when given an element drawn from distribution $P_2$ as input, $D$ outputs $1$ with
probabilty $\Pr[S_{i+1}]$. The indistinguishability assumption then implies that
$|\Pr[S_i]-\Pr[S_{i+1}]|$ is negligible. Usually, the construction of $D$ is obvious,
provided the changes made in the transition are minimal. Typically, one designs the two
games so that they could easily be rewritten as a single "hybrid" game that takes an
auxilliary input — if the auxiallary input is drawn from $P_1$, you get Game $i$, and if
drawn from $P_2$, you get Game $i+1$. The distinguisher then simply runs this single hybrid
game with its input, and outputs $1$ if the appropriate event occurs.

*Transcription note.* "probabilty", "auxilliary" and "auxiallary" are transcribed as
printed.

<a id="pdf-fde1f65e83ec-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.95 -->

**Transition type 2: transitions based on failure events (pp. 2–3).** In such a transition,
one argues that Games $i$ and $i+1$ proceed identically unless a certain "failure event" $F$
occurs. To make this type of argument as cleanly as possible, it is best if the two games
are defined on the same underlying probability space — the only differences between the two
games are the rules for computing certain random variables. When done this way, saying that
the two games proceed identically unless $F$ occurs is equivalent to saying that

$$
S_i\wedge\neg F\iff S_{i+1}\wedge\neg F,
$$

that is, the events $S_i\wedge\neg F$ and $S_{i+1}\wedge\neg F$ are the same. If this is
true, then we can use the following fact, which is completely trivial, yet is so often used
in these types of proofs that it deserves a name:

<a id="pdf-fde1f65e83ec-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.95 -->

**Lemma 1 (Difference Lemma) (p. 3).** Let $A$, $B$, $F$ be events defined in some
probability distribution, and suppose that $A\wedge\neg F\iff B\wedge\neg F$. Then
$|\Pr[A]-\Pr[B]|\le\Pr[F]$.

*Proof.* This is a simple calculation. We have

$$
\begin{aligned}
|\Pr[A]-\Pr[B]|
&=\left|\Pr[A\wedge F]+\Pr[A\wedge\neg F]-\Pr[B\wedge F]-\Pr[B\wedge\neg F]\right|\\
&=\left|\Pr[A\wedge F]-\Pr[B\wedge F]\right|\\
&\le\Pr[F].
\end{aligned}
$$

The second equality follows from the assumption that $A\wedge\neg F\iff B\wedge\neg F$, and
so in particular, $\Pr[A\wedge\neg F]=\Pr[B\wedge\neg F]$. The final inequality follows from
the fact that both $\Pr[A\wedge F]$ and $\Pr[B\wedge F]$ are numbers between $0$ and
$\Pr[F]$. $\square$

So to prove that $\Pr[S_i]$ is negligibly close to $\Pr[S_{i+1}]$, it suffices to prove that
$\Pr[F]$ is negligible. Sometimes, this is done using a security assumption (i.e., when $F$
occurs, the adversary has found a collision in a hash function, or forged a MAC), while at
other times, it can be done using a purely information-theoretic argument.

Usually, the event $F$ is defined and analyzed in terms of the random variables of one of
the two adjacent games. The choice is arbitrary, but typically, one of the games will be
more suitable than the other in terms of allowing a clear proof.

In some particularly challenging circumstances, it may be difficult to analyze the event $F$
in either game. In fact, the analysis of $F$ may require its own sequence of games sprouting
off in a different direction, or the sequence of games for $F$ may coincide with the
sequence of games for $S$, so that $\Pr[F]$ finally gets pinned down in Game $j$ for
$j>i+1$. This technique is sometimes crucial in side-stepping potential circularities.

<a id="pdf-fde1f65e83ec-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.95 -->

**Transition type 3: bridging steps (p. 3).** The third type of transition introduces a
**bridging step**, which is typically a way of restating how certain quantities can be
computed in a completely equivalent way. The change is purely conceptual, and
$\Pr[S_i]=\Pr[S_{i+1}]$. The reason for doing this is to prepare the ground for a transition
of one of the above two types. While in principle, such a bridging step may seem
unnecessary, without it, the proof would be much harder to follow.

<a id="pdf-fde1f65e83ec-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.95 -->

**Section 1.1, one probability space, and the generalized Difference Lemma (p. 3).** As
mentioned above, in a transition based on a failure event, it is best if the two successive
games are understood to be defined on the same underlying probability space. This is an
important point, which we repeat here for emphasis — it seems that proofs are easiest to
understand if one does not need to compare "corresponding" events across distinct and (by
design) quite different probability spaces. Actually, it is good practice to simply have all
the games in the sequence defined on the same underlying probability space. However, the
Difference Lemma generalizes in the obvious way as follows: if $A$, $B$, $F_1$ and $F_2$ are
events such that $\Pr[A\wedge\neg F_1]=\Pr[B\wedge\neg F_2]$ and $\Pr[F_1]=\Pr[F_2]$, then
$|\Pr[A]-\Pr[B]|\le\Pr[F_1]$. With this generalized version, one may (if one wishes) analyze
transitions based on failure events when the underlying probability spaces are not the same.

<a id="pdf-fde1f65e83ec-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.90 -->

**Section 4.2, a worked bridging step (Game 2, p. 13).** [Context: §4.2, "Extending the
Input Length with a Universal Hash Function" (p. 12), stretches a pseudo-random family
$F=\{F_s\}_{s\in S}$ by a universal hash family $H=\{H_k\}_{k\in K}$. Game 1 gives the
adversary oracle access to a truly random function $f$.]

**Game 2.** [This transition is a bridging step.] We now make a purely conceptual change to
Game 1. Intuitively, one can think of a black box containing the random function $f$ as a
box with a little "gnome" inside: the gnome keeps a table of previous input/output pairs,
and if a query is made that matches one of the previous inputs, the corresponding output is
returned, and otherwise, an output value is chosen at random, and a new input/output pair is
added to the table (see Figure 1). Based on this, we get the following equivalent
formulation of Game 1:

$$
\begin{aligned}
&k\stackrel{\scriptscriptstyle ?}{\leftarrow}K,\quad Y_1,\dots,Y_q\stackrel{\scriptscriptstyle ?}{\leftarrow}\{0,1\}^{\ell_2}\\
&r\stackrel{\scriptscriptstyle ?}{\leftarrow}R\\
&\textbf{for } i\leftarrow 1\dots q \textbf{ do}\\
&\qquad w_i\leftarrow A(r,y_1,\dots,y_{i-1})\in\{0,1\}^{\ell}\\
&\qquad x_i\leftarrow H_k(w_i)\in\{0,1\}^{\ell_1}\\
&\qquad \textbf{if } x_i=x_j \textbf{ for some } j<i \textbf{ then } y_i\leftarrow y_j
  \textbf{ else } y_i\leftarrow Y_i\\
&b\leftarrow A(r,y_1,\dots,y_q)\in\{0,1\}\\
&\textbf{output } b
\end{aligned}
$$

Let $S_2$ be the event that $b=1$ in Game 2. Since the change in going from Game 1 to
Game 2 was purely conceptual, we clearly have

$$
\Pr[S_2]=\Pr[S_1].\tag{5}
$$

*Transcription note, partly illegible glyph.* The paper writes random assignment as a left
arrow with a small mark set above it. The `-layout` extraction renders that mark as the two
characters `c|`, and on the page image (read at 600 dpi) it is a cent-like sign (a "c" with
a vertical stroke); it is **not** legibly an "R", and the mark could not be identified with
confidence. It is written below as $\stackrel{\scriptscriptstyle ?}{\leftarrow}$, with `?`
standing for that unidentified mark. From the paper's own use of the same arrow in §4.1
(p. 11) — $\Pr[s\stackrel{\scriptscriptstyle ?}{\leftarrow}S:A^{F_s}()=1]$ — and from the
prose above ("an output value is chosen at random"), the arrow denotes a uniform random
choice from the set on its right. Figure 1 ("A gnome implementation of a random function",
p. 13) is a diagram and is not transcribed.
