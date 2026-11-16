<!-- generated-by: scoped Poppler extraction of the passages used (DW-8) -->
<!-- source-pdf-sha256: fde1f65e83ec85297f58840bf87de15fb68e91ada8aefaf77db3b153cf826820 -->
<!-- extractor: pdftotext version 24.02.0; -layout; scoped to the line ranges listed below -->
<!-- scope (physical page: lines of the -layout text): p1: 1-44; p2: 45-91; p3: 92-139; p11: 541-544; p12: 545-552; p13: 620-641 -->
<!-- note: physical page = printed page -->

<!-- pdf-page: 1 -->
                           Sequences of Games:
              A Tool for Taming Complexity in Security Proofs∗
                                               Victor Shoup†

                                            January 18, 2006



                                                  Abstract
             This paper is brief tutorial on a technique for structuring security proofs as sequences
          games.


1        Introduction
Security proofs in cryptography may sometimes be organized as sequences of games. In
certain circumstances, this can be a useful tool in taming the complexity of security proofs
that might otherwise become so messy, complicated, and subtle as to be nearly impossible to
verify. This technique appears in the literature in various styles, and with various degrees of
rigor and formality. This paper is meant to serve as a brief tutorial on one particular “style”
of employing this technique, which seems to achieve a reasonable level of mathematical rigor
and clarity, while not getting bogged down with too much formalism or overly restrictive
rules. We do not make any particular claims of originality — it is simply hoped that others
might profit from some of the ideas discussed here in reasoning about security.
    At the outset, it should be noted that this technique is certainly not applicable to
all security proofs. Moreover, even when this technique is applicable, it is only a tool for
organizing a proof — the actual ideas for a cryptographic construction and security analysis
must come from elsewhere.

1.1        The Basic Idea
Security for cryptograptic primitives is typically defined as an attack game played between
an adversary and some benign entity, which we call the challenger. Both adversary and
challenger are probabilstic processes that communicate with each other, and so we can
model the game as a probability space. Typically, the definition of security is tied to some
particular event S. Security means that for every “efficient” adversary, the probability that
event S occurs is “very close to” some specified “target probabilty”: typically, either 0,
1/2, or the probability of some event T in some other game in which the same adversary is
interacting with a different challenger.
    ∗
        First public version: Nov. 30, 2004
    †
        Computer Science Dept. NYU. shoup@cs.nyu.edu


                                                      1

<!-- pdf-page: 2 -->
     In the formal definitions, there is a security parameter: an integer tending to infinity, and
in the previous paragraph, “efficient” means time bounded by a polynomial in the security
parameter, and “very close to” means the difference is smaller than the inverse of any
polynomial in the security parameter, for sufficiently large values of the security parameter.
The term of art is negligibly close to, and a quantity that is negliglibly close to zero is just
called negligible. For simplicity, we shall for the most part avoid any further discussion of
the security parameter, and it shall be assumed that all algorithms, adversaries, etc., take
this value as an implicit input.
     Now, to prove security using the sequence-of-games approach, one prodceeds as follows.
One constructs a sequence of games, Game 0, Game 1, . . . , Game n, where Game 0 is the
original attack game with respect to a given adversary and cryptographic primitive. Let S0
be the event S, and for i = 1, . . . , n, the construction defines an event Si in Game i, usually
in a way naturally related to the definition of S. The proof shows that Pr[Si ] is negligibly
close to Pr[Si+1 ] for i = 0, . . . , n − 1, and that Pr[Sn ] is equal (or negligibly close) to the
“target probability.” From this, and the fact that n is a constant, it follows that Pr[S] is
negligibly close to the “target probability,” and security is proved.
     That is the general framework of such a proof. However, in constructing such proofs,
it is desirable that the changes between succesive games are very small, so that analyzing
the change is as simple as possible. From experience, it seems that transitions between
successive games can be restricted to one of three types:
Transitions based on indistinguishability. In such a transition, a small change is made
that, if detected by the adversary, would imply an efficient method of distinguishing be-
tween two distributions that are indistinguishable (either statistically or computationally).
For example, suppose P1 and P2 are assumed to be computationally indistinguishable dis-
tributions. To prove that | Pr[Si ] − Pr[Si+1 ]| is negligible, one argues that there exists a
distinguishing algorithm D that “interpolates” between Game i and Game i+1, so that when
given an element drawn from distribution P1 as input, D outputs 1 with probability Pr[Si ],
and when given an element drawn from distribution P2 as input, D outputs 1 with prob-
abilty Pr[Si+1 ]. The indistinguishability assumption then implies that | Pr[Si ] − Pr[Si+1 ]|
is negligible. Usually, the construction of D is obvious, provided the changes made in the
transition are minimal. Typically, one designs the two games so that they could easily
be rewritten as a single “hybrid” game that takes an auxilliary input — if the auxiallary
input is drawn from P1 , you get Game i, and if drawn from P2 , you get Game i + 1. The
distinguisher then simply runs this single hybrid game with its input, and outputs 1 if the
appropriate event occurs.
Transitions based on failure events. In such a transition, one argues that Games i
and i + 1 proceed identically unless a certain “failure event” F occurs. To make this type
of argument as cleanly as possible, it is best if the two games are defined on the same
underlying probability space — the only differences between the two games are the rules
for computing certain random variables. When done this way, saying that the two games
proceed identically unless F occurs is equivalent to saying that

                                   Si ∧ ¬F ⇐⇒ Si+1 ∧ ¬F,

that is, the events Si ∧ ¬F and Si+1 ∧ ¬F are the same. If this is true, then we can use the

                                                2

<!-- pdf-page: 3 -->
following fact, which is completely trivial, yet is so often used in these types of proofs that
it deserves a name:

Lemma 1 (Difference Lemma). Let A, B, F be events defined in some probability dis-
tribution, and suppose that A ∧ ¬F ⇐⇒ B ∧ ¬F . Then | Pr[A] − Pr[B]| ≤ Pr[F ].

Proof. This is a simple calculation. We have

          | Pr[A] − Pr[B]| = | Pr[A ∧ F ] + Pr[A ∧ ¬F ] − Pr[B ∧ F ] − Pr[B ∧ ¬F ]|
                            = | Pr[A ∧ F ] − Pr[B ∧ F ]|
                            ≤ Pr[F ].

The second equality follows from the assumption that A ∧ ¬F ⇐⇒ B ∧ ¬F , and so in
particular, Pr[A ∧ ¬F ] = Pr[B ∧ ¬F ]. The final inequality follows from the fact that both
Pr[A ∧ F ] and Pr[B ∧ F ] are numbers between 0 and Pr[F ]. 2
     So to prove that Pr[Si ] is negligibly close to Pr[Si+1 ], it suffices to prove that Pr[F ] is
negligible. Sometimes, this is done using a security assumption (i.e., when F occurs, the
adversary has found a collision in a hash function, or forged a MAC), while at other times,
it can be done using a purely information-theoretic argument.
     Usually, the event F is defined and analyzed in terms of the random variables of one
of the two adjacent games. The choice is arbitrary, but typically, one of the games will be
more suitable than the other in terms of allowing a clear proof.
     In some particularly challenging circumstances, it may be difficult to analyze the event
F in either game. In fact, the analysis of F may require its own sequence of games sprouting
off in a different direction, or the sequence of games for F may coincide with the sequence of
games for S, so that Pr[F ] finally gets pinned down in Game j for j > i + 1. This technique
is sometimes crucial in side-stepping potential circularities.
Bridging steps. The third type of transition introduces a bridging step, which is typically
a way of restating how certain quantities can be computed in a completely equivalent way.
The change is purely conceptual, and Pr[Si ] = Pr[Si+1 ]. The reason for doing this is to
prepare the ground for a transition of one of the above two types. While in principle, such a
bridging step may seem unnecessary, without it, the proof would be much harder to follow.

    As mentioned above, in a transition based on a failure event, it is best if the two
successive games are understood to be defined on the same underlying probability space.
This is an important point, which we repeat here for emphasis — it seems that proofs
are easiest to understand if one does not need to compare “corresponding” events across
distinct and (by design) quite different probability spaces. Actually, it is good practice
to simply have all the games in the sequence defined on the same underlying probability
space. However, the Difference Lemma generalizes in the obvious way as follows: if A,
B, F1 and F2 are events such that Pr[A ∧ ¬F1 ] = Pr[B ∧ ¬F2 ] and Pr[F1 ] = Pr[F2 ], then
| Pr[A] − Pr[B]| ≤ Pr[F1 ]. With this generalized version, one may (if one wishes) analyze
transitions based on failure events when the underlying probability spaces are not the same.




                                                3

<!-- pdf-page: 11 -->
                                                          Γ`1 ,`2 : Af ()] = 1|.
We say that F is pseudo-random if any efficient adversary’s PRF-advantage is negligible.

                                                  11

<!-- pdf-page: 12 -->
4.2   Extending the Input Length with a Universal Hash Function
We now present one construction that allows one to stretch the input length of a pseudo-
random family of functions. Let ` be a positive integer with ` > `1 . Let H := {Hk }k∈K be
a family of keyed hash functions, where each Hk maps {0, 1}` to {0, 1}`1 . Let us assume
that H is an uh -universal family of hash functions, where uh is negligible. This means that
for all w, w0 ∈ {0, 1}` with w 6= w0 , we have
                                     c|
                                Pr[k ←  K : Hk (w) = Hk (w0 )] ≤ uh .

<!-- pdf-page: 13 -->
Game 2. [This transition is a bridging step.] We now make a purely conceptual change to
Game 1. Intuitively, one can think of a black box containing the random function f as a
box with a little “gnome” inside: the gnome keeps a table of previous input/output pairs,
and if a query is made that matches one of the previous inputs, the corresponding output
is returned, and otherwise, an output value is chosen at random, and a new input/output
pair is added to the table (see Figure 1). Based on this, we get the following equivalent
formulation of Game 1:
      c|                    c|
     k←  K, Y1 , . . . , Yq ←  {0, 1}`2
        c|
     r←    R
     for i ← 1 . . . q do
           wi ← A(r, y1 , . . . , yi−1 ) ∈ {0, 1}`
           xi ← Hk (wi ) ∈ {0, 1}`1
           if xi = xj for some j < i then yi ← yj else yi ← Yi
     b ← A(r, y1 , . . . , yq ) ∈ {0, 1}
     output b
  Let S2 be the event that b = 1 in Game 2. Since the change in going from Game 1 to
Game 2 was purely conceptual, we clearly have
                                           Pr[S2 ] = Pr[S1 ].                          (5)

                                                     13
