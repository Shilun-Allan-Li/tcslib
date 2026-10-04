<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: 9c61a2f1ecc11f96a5403f7423ad07671dc78eb0fde46b49551c8717c18639cc -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
Games and Economic Behavior, 29:79-103, 1999.

Adaptive game playing using multiplicative weights

Yoav Freund

Robert E. Schapire

AT&T Labs
Shannon Laboratory
180 Park Avenue
Florham Park, NJ 07932›0971
yoav, schapire (cid:1) @research.att.com

http://www.research.att.com/ (cid:2)

yoav, schapire (cid:1)

April 30, 1999

Abstract

We present a simple algorithm for playing a repeated game. We show that a player using this
algorithm suffers average loss that is guaranteed to come close to the minimum loss achievable by any
(cid:2)xed strategy. Our bounds are non›asymptotic and hold for any opponent. The algorithm, which uses
the multiplicative›weight methods of Littlestone and Warmuth, is analyzed using the Kullback›Liebler
divergence. This analysis yields a new, simple proof of the minmax theorem, as well as a provable method
of approximately solving a game. A variant of our game›playing algorithm is proved to be optimal in a
very strong sense.

1 Introduction

We study the problem of learning to play a repeated game. Let (cid:3)
be a matrix. On each of a series of
rounds, one player chooses a row (cid:4) and the other chooses a column (cid:5)
is the
. The selected entry (cid:3)(cid:7)(cid:6)(cid:8)(cid:4)(cid:10)(cid:9)(cid:11)(cid:5)(cid:13)(cid:12)
loss suffered by the row player. We study play of the game from the row player’s perspective, and therefore
leave the column player’s loss or utility unspeci(cid:2)ed.

(if
A simple goal for the row player is to suffer loss which is no worse than the value of the game (cid:3)
viewed as a zero›sum game). Such a goal may be appropriate when it is expected that the opposing column
player’s goal is to maximize the loss of the row player (so that the game is in fact zero›sum). In this case,
the row player can do no better than to play using a minmax mixed strategy which can be computed using
linear programming, provided that the entire matrix (cid:3)
is known ahead of time, and provided that the matrix
is not too large. This approach has a number of potential drawbacks. For instance,

(cid:3) may be unknown;

(cid:3) may be so large that computing a minmax strategy using linear programming is infeasible; or

the column player may not be truly adversarial and may behave in a manner that admits loss signi(cid:2)›
cantly smaller than the game value.

Overcoming these dif(cid:2)culties in the one›shot game is hopeless. In repeated play, however, one can hope

to learn to play well against the particular opponent that is being faced.

Algorithms of this type were (cid:2)rst proposed by Hannan [20] and Blackwell [3], and later algorithms
were proposed by Foster and Vohra [14, 15, 13]. These algorithms have the property that the loss of the

1

(cid:0)
(cid:0)
(cid:14)
(cid:14)
(cid:14)


<!-- pdf-page: 2 -->
row player in repeated play is guaranteed to come close to the minimum loss achievable with respect to the
sequence of plays taken by the column player.

In this paper, we present a simple algorithm for solving this problem, and give a simple analysis of the
algorithm. The bounds we obtain are not asymptotic and hold for any (cid:2)nite number of rounds. The algorithm
and its analysis are based directly on the (cid:147)on›line prediction(cid:148) methods of Littlestone and Warmuth [25].

The paper is organized as follows.

In Section 2 we de(cid:2)ne the mathematical setup and notation.

The analysis of this algorithm yields a new (as far as we know) and simple proof of von Neumann’s
minmax theorem, as well as a provable method of approximately solving a game. We also give more re(cid:2)ned
variants of the algorithm for this purpose, and we show that one of these is optimal in a very strong sense.
In
Section 3 we introduce the basic multiplicative weights algorithm whose average performance is guaranteed
to be almost as good as that of the best (cid:2)xed mixed strategy. In Section 4 we outline the relationship between
our work and some of the extensive existing work on the use of multiplicative weights algorithms for on›line
prediction. In Section 5 we show how the algorithm can be used to give a simple proof of Von›Neumann’s
min›max theorem. In Section 6 we give a version of the algorithm whose distributions are guaranteed to
converge to an optimal mixed strategy. We note the possible application of this algorithm to solving linear
programming problems and reference other work that have used multiplicative weights to this end. Finally,
in Section 7 we show that the convergence rate of the second version of the algorithm is asymptotically
optimal.

2 Playing repeated games

rows and (cid:1)

We consider non›collaborative two›person games in normal form. The game is de(cid:2)ned by a matrix (cid:3) with
columns. There are two players called the row player and column player. To play the game,
. The selected

the row player chooses a row (cid:4) , and, simultaneously, the column player chooses a column (cid:5)
entry (cid:3)(cid:7)(cid:6)(cid:8)(cid:4)

(cid:12) is the loss suffered by the row player. The column player’s loss or utility is unspeci(cid:2)ed.

For the sake of simplicity, throughout this paper, we assume that all the entries of the matrix (cid:3)

are in
the range
0 (cid:9) 1(cid:3) . Simple scaling can be used to get similar results for general bounded ranges. Also, we
restrict ourselves to the case where the number of choices available to each player is (cid:2)nite. However, most
of the results translate with very mild additional assumptions to cases in which the number of choices is
in(cid:2)nite. For a discussion of in(cid:2)nite matrix games see, for instance, Chapter 2 in Ferguson [11].

Following standard terminology, we refer to the choice of a speci(cid:2)c row or column as a pure strategy
and to a distribution over rows or columns as a mixed strategy. We use (cid:4)
to denote a mixed strategy of the
to denote the probability
row player, and (cid:5)
to denote the expected loss (of the row
that (cid:4)
player) when the two mixed strategies are used. In addition, we write (cid:3)(cid:7)(cid:6)(cid:6)(cid:4)
to denote the
expected loss when one side uses a pure strategy and the other a mixed strategy. Although these quantities
denote expected losses, we will usually refer to them simply as losses.

to denote a mixed strategy of the column player. We use (cid:4)

associates with the row (cid:4) , and we write (cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

(cid:12) and (cid:3)(cid:7)(cid:6)(cid:8)(cid:4)(cid:10)(cid:9)(cid:12)(cid:5)

T

(cid:12)(cid:9)(cid:8)(cid:10)(cid:4)

(cid:3)(cid:11)(cid:5)

(cid:6)(cid:8)(cid:4)(cid:11)(cid:12)

(cid:9)(cid:7)(cid:5)

If we assume that the loss of the row player is the gain of the column player, we can think about the game
to denote optimal mixed strategies for

as a zero›sum game. Under such an interpretation we use (cid:4)(cid:14)(cid:13) and (cid:5)(cid:15)(cid:13)

(cid:9)(cid:12)(cid:5)

(cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

to denote the value of the game.

, and (cid:16)(cid:17)(cid:8)
The main subject of this paper is an algorithm for adaptively selecting mixed strategies. The algorithm is
used to choose a mixed strategy for one of the players in the context of repeated play. We usually associate
the algorithm with the row player. To emphasize the roles of the two players in our context, we sometimes
refer to the row and column players as the learner and the environment, respectively. An instance of repeated
play is a sequence of rounds of interactions between the learner and the environment. The game matrix (cid:3)
used in the interactions is (cid:2)xed but is unknown to the learner. The learner only knows the number of choices
1 (cid:9)(cid:21)(cid:20)(cid:22)(cid:20)(cid:21)(cid:20)
that it has, i.e., the number of rows. On round (cid:18)(cid:19)(cid:8)

:

(cid:9)(cid:24)(cid:23)

2

(cid:0)
(cid:9)
(cid:5)
(cid:2)
(cid:9)
(cid:5)
(cid:12)
(cid:3)
(cid:13)
(cid:13)
(cid:12)


<!-- pdf-page: 3 -->
(cid:1)(cid:0)

1. the learner chooses mixed strategy (cid:4)

;

(cid:2)(cid:0)

(cid:1)(cid:0)

2. the environment chooses mixed strategy (cid:5)

(which may be chosen with knowledge of (cid:4)

(cid:2)(cid:0)

)

3. the learner is permitted to observe the loss (cid:3)(cid:7)(cid:6)(cid:8)(cid:4)
suffered had it played using pure strategy (cid:4) ;

(cid:3)(cid:0)

(cid:1)(cid:0)

(cid:9)(cid:7)(cid:5)

for each row (cid:4) ; this is the loss it would have

4. the learner suffers loss (cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

(cid:9)(cid:12)(cid:5)

(cid:12) .

(cid:4)(cid:6)(cid:5)

(cid:0)(cid:8)(cid:7)

(cid:9)(cid:0)

(cid:10)(cid:0)

The basic goal of the learner is to minimize its total loss

If the environment is
maximally adversarial then a related goal is to approximate the optimal mixed row strategy (cid:4)
(cid:13) . However,
in more benign environments, the goal may be to suffer the minimum loss possible, which may be much
better than the value of the game.

1 (cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

(cid:11)(cid:12) .

(cid:11)(cid:9)(cid:7)(cid:5)

Finally, in what follows, we (cid:2)nd it useful to measure the distance between two distributions (cid:4)

1 and (cid:4)

2

using the Kullback-Leibler divergence, also called the relative entropy, which is de(cid:2)ned to be

RE

(cid:6)(cid:4)

1

2

(cid:12) ln

1 (cid:6)(cid:8)(cid:4)

1

(cid:19)(cid:18)

1 (cid:6)(cid:8)(cid:4)

2 (cid:6)(cid:8)(cid:4)

As is well known, the relative entropy is a measure of discrepancy between distributions in that it is non›
0 (cid:9) 1(cid:3) , we use the shorthand
negative and is equal to zero if and only if (cid:4)
RE
2, i.e.,

to denote the relative entropy between Bernoulli distributions with parameters

2. For real numbers

1 and

1 (cid:8)(cid:10)(cid:4)

1 (cid:9)

1

2

2

(cid:27)(cid:26)(cid:20)

(cid:21)(cid:20)

(cid:11)(cid:23)(cid:20)

(cid:24)(cid:20)

(cid:27)(cid:28)(cid:20)

RE

1

2

1 ln

(cid:18)(cid:26)(cid:25)

1

2

(cid:6) 1

1 (cid:12) ln

(cid:27)(cid:26)(cid:20)

1
1

1

2

3 The basic algorithm

We now describe our basic algorithm for repeated play, which we call MW for (cid:147)multiplicative weights.(cid:148)
This algorithm is a direct generalization of Littlestone and Warmuth’s (cid:147)weighted majority algorithm(cid:148) [25],
which was discovered independently by Fudenberg and Levine [17].

(cid:16)%$

&(’(cid:23))

The learning algorithm MW starts with some initial mixed strategy (cid:4)
of the game. After each round (cid:18) , the learner computes a new mixed strategy (cid:4)
rule:

(cid:31)(cid:30)! #"

(cid:0)(cid:8)(cid:29)

(cid:10)(cid:0)(cid:8)(cid:29)

1 which it uses for the (cid:2)rst round
1 by a simple multiplicative

where

is a normalization factor:

1 (cid:6)

(cid:4)(cid:11)(cid:12)(cid:19)(cid:8)(cid:10)(cid:4)

(cid:6)(cid:8)(cid:4)(cid:11)(cid:12)

(cid:16)%$

 (cid:6)"

(cid:6)(cid:8)(cid:4)

1

and

0 (cid:9) 1 (cid:12)

is a parameter of the algorithm.

The main theorem concerning this algorithm is the following:

Theorem 1 For any matrix M with (cid:0)
Q1 (cid:9)(cid:21)(cid:20)(cid:21)(cid:20)(cid:22)(cid:20)
MW satisﬁes:

(cid:9) Q

,+

played by the environment, the sequence of mixed strategies P1 (cid:9)(cid:21)(cid:20)(cid:21)(cid:20)(cid:22)(cid:20)

rows and entries in (cid:2)

0 (cid:9) 1 (cid:3) , and for any sequence of mixed strategies
produced by algorithm

(cid:9) P

where

(cid:0)(cid:8)(cid:7)

(cid:0)(cid:8)(cid:7)

-/.10

(cid:25)(cid:24)2

M (cid:6) P

(cid:9) Q

(cid:8)(cid:12)

1

min
P

1

M (cid:6) P (cid:9) Q

RE

P

.50

ln (cid:6) 1
1

1

1

3

(cid:13)43

P1

(cid:12)
(cid:11)
(cid:12)
(cid:4)
(cid:13)
(cid:20)
(cid:8)
(cid:14)
(cid:15)
(cid:16)
(cid:7)
(cid:4)
(cid:17)
(cid:4)
(cid:12)
(cid:4)
(cid:12)
(cid:20)
(cid:20)
(cid:22)
(cid:2)
(cid:11)
(cid:20)
(cid:12)
(cid:20)
(cid:13)
(cid:20)
(cid:20)
(cid:12)
(cid:20)
(cid:13)
(cid:20)
(cid:8)
(cid:17)
(cid:20)
(cid:20)
(cid:17)
(cid:18)
(cid:20)
(cid:4)
(cid:0)
*
(cid:0)
*
(cid:0)
*
(cid:0)
(cid:8)
(cid:14)
(cid:15)
(cid:16)
(cid:7)
(cid:4)
(cid:0)
(cid:12)
(cid:30)
&
’
)
(cid:9)
(cid:30)
(cid:22)
(cid:2)
(cid:5)
(cid:5)
(cid:5)
(cid:15)
(cid:0)
(cid:0)
(cid:5)
(cid:15)
(cid:0)
(cid:12)
0
(cid:11)
(cid:12)
(cid:8)
6
(cid:30)
(cid:12)
(cid:27)
(cid:30)
2
0
(cid:8)
(cid:27)
(cid:30)
(cid:20)


<!-- pdf-page: 4 -->
Our proof uses a kind of (cid:147)amortized analysis(cid:148) in which relative entropy is used as a (cid:147)potential(cid:148) function.
This method of analysis for on›line learning algorithms is due to Kivinen and Warmuth [23]. The heart of
the proof is in the following lemma, which bounds the change in potential before and after a single round.

Lemma 2 For any iteration (cid:18) where MW is used with parameter

, and for any mixed strategy (cid:152)P,

RE (cid:0) (cid:152)P

(cid:0)%(cid:29)

P

1 (cid:1)

RE (cid:0) (cid:152)P

P

1(cid:30)

ln

M (cid:6) (cid:152)P (cid:9) Q

(cid:8)(cid:12)

ln

1

(cid:6) 1

(cid:12) M (cid:6) P

(cid:9) Q

(cid:8)(cid:12)

Proof: The proof of the lemma can be summarized by the following sequence of inequalities:

(cid:9)(cid:0)%(cid:29)

(cid:9)(cid:0)

RE (cid:0) (cid:152)(cid:4)

1 (cid:1)

RE (cid:0) (cid:152)(cid:4)
(cid:152)(cid:4)

(cid:6)(cid:8)(cid:4)

(cid:0)(cid:8)(cid:29)

(cid:9)(cid:0)

1 (cid:6)(cid:8)(cid:4)

(cid:0)(cid:8)(cid:29)

(cid:4)(cid:11)(cid:12)

(cid:16)%$

1 (cid:6)(cid:8)(cid:4)

(cid:152)(cid:4)

(cid:6)(cid:8)(cid:4)

(cid:12) ln

(cid:9)(cid:0)

(cid:152)(cid:4)

(cid:6)(cid:8)(cid:4)(cid:11)(cid:12)

(cid:6)(cid:8)(cid:4)

1

(cid:152)(cid:4)

(cid:6)(cid:8)(cid:4)(cid:11)(cid:12) ln

(cid:152)(cid:4)

(cid:6)(cid:8)(cid:4)(cid:11)(cid:12) ln (cid:4)

1

1

1

(cid:152)(cid:4)

(cid:6)(cid:8)(cid:4)(cid:11)(cid:12) ln

 (cid:6)"

1(cid:30)

1(cid:30)

1(cid:30)

ln

ln

ln

(cid:3)(cid:0)

(cid:4)(cid:11)(cid:12)

(cid:3)(cid:7)(cid:6)(cid:8)(cid:4)(cid:10)(cid:9)(cid:12)(cid:5)

ln

(cid:152)(cid:4)

1

(cid:3)(cid:7)(cid:6) (cid:152)(cid:4)

(cid:9)(cid:7)(cid:5)

ln

(cid:6)(cid:8)(cid:4)(cid:11)(cid:12)

1

(cid:6) 1

(cid:12)(cid:10)(cid:3)(cid:7)(cid:6)(cid:8)(cid:4)

(cid:9)(cid:7)(cid:5)

(cid:3)(cid:0)

1

(cid:9)(cid:0)

(cid:10)(cid:0)

(cid:3)(cid:7)(cid:6) (cid:152)(cid:4)

(cid:9)(cid:12)(cid:5)

ln

1

(cid:6) 1

(cid:3)(cid:7)(cid:6)

(cid:11)(cid:9)(cid:7)(cid:5)

(cid:11)(cid:12)

(cid:13)43

(1)

(2)

(3)

(4)

(5)

Line (1) follows from the de(cid:2)nition of relative entropy. Line (3) follows from the update rule of MWand
line (4) follows by simple algebra. Finally, line (5) follows from the de(cid:2)nition of
combined with the fact
that, by convexity,
for
Proof of Theorem 1: Let (cid:152)(cid:4)
Lemma 2 by using the fact that ln (cid:6) 1

(cid:6) 1
be any mixed row strategy. We (cid:2)rst simplify the last term in the inequality of

for any (cid:4)(cid:11)(cid:10) 1 which implies that

0 and (cid:4)

0 (cid:9) 1(cid:3) .

1

(cid:8)(cid:4)

(cid:7)(cid:6)

(cid:9)(cid:4)

,+

(cid:3)(cid:2)

(cid:12)(cid:5)(cid:4)

(cid:9)(cid:0)(cid:8)(cid:29)

(cid:9)(cid:0)

(cid:10)(cid:0)

(cid:3)(cid:0)

RE (cid:0) (cid:152)(cid:4)

1 (cid:1)

RE (cid:0) (cid:152)(cid:4)

1(cid:30)

ln

(cid:3)(cid:7)(cid:6) (cid:152)(cid:4)

(cid:9)(cid:7)(cid:5)

(cid:8)(cid:12)

(cid:6) 1

(cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

(cid:11)(cid:9)(cid:12)(cid:5)

(cid:11)(cid:12)

Summing this inequality over (cid:18)(cid:19)(cid:8)

1 (cid:9)(cid:21)(cid:20)(cid:22)(cid:20)(cid:21)(cid:20)

(cid:23) we get

RE (cid:0) (cid:152)(cid:4)

1 (cid:1)

RE (cid:0) (cid:152)(cid:4)

1 (cid:1)

(cid:3)(cid:0)

(cid:3)(cid:0)

1(cid:30)

(cid:0)%(cid:7)

ln

(cid:3)(cid:7)(cid:6) (cid:152)(cid:4)

(cid:9)(cid:12)(cid:5)

(cid:8)(cid:12)

(cid:6) 1

1

(cid:0)(cid:8)(cid:7)

1

(cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

(cid:11)(cid:9)(cid:12)(cid:5)

(cid:11)(cid:12)(cid:12)(cid:20)

Noting that RE (cid:0) (cid:152)(cid:4)
1 (cid:1)
the statement of the theorem.

.

0, rearranging the inequality and noting that (cid:152)(cid:4) was chosen arbitrarily gives

1. In general, the closer (cid:4)

In order to use MW, we need to choose the initial distribution (cid:4)

. We start with
, the better the bound on the total
the choice of (cid:4)
loss MW. However, even if we have no prior knowledge about the good mixed strategies, we can achieve
reasonable performance by using the uniform distribution over the rows as the initial strategy. This gives us
a performance bound that holds uniformly for all games with (cid:0)

1 is to a good mixed strategy (cid:152)(cid:4)

1 and the parameter

rows:

4

(cid:30)
(cid:12)
(cid:27)
(cid:12)
(cid:0)
(cid:1)
+
(cid:17)
(cid:18)
(cid:0)
(cid:25)
(cid:11)
(cid:27)
(cid:27)
(cid:30)
(cid:0)
(cid:0)
(cid:13)
(cid:20)
(cid:12)
(cid:4)
(cid:27)
(cid:12)
(cid:4)
(cid:1)
(cid:8)
(cid:14)
(cid:15)
(cid:16)
(cid:7)
(cid:12)
(cid:4)
(cid:12)
(cid:27)
(cid:14)
(cid:15)
(cid:16)
(cid:7)
(cid:4)
(cid:12)
(cid:8)
(cid:14)
(cid:15)
(cid:16)
(cid:7)
(cid:6)
(cid:4)
(cid:12)
(cid:8)
(cid:14)
(cid:15)
(cid:16)
(cid:7)
*
(cid:0)
(cid:30)
&
’
)
(cid:8)
(cid:17)
(cid:18)
(cid:14)
(cid:15)
(cid:16)
(cid:7)
(cid:6)
(cid:12)
(cid:25)
*
(cid:0)
+
(cid:17)
(cid:18)
(cid:0)
(cid:12)
(cid:25)
-
(cid:14)
(cid:15)
(cid:16)
(cid:7)
(cid:4)
(cid:0)
(cid:11)
(cid:27)
(cid:27)
(cid:30)
(cid:0)
(cid:12)
(cid:8)
(cid:17)
(cid:18)
(cid:12)
(cid:25)
(cid:11)
(cid:27)
(cid:27)
(cid:30)
(cid:12)
(cid:4)
(cid:13)
(cid:20)
*
(cid:0)
(cid:30)
+
(cid:27)
(cid:27)
(cid:30)
(cid:30)
(cid:22)
(cid:2)
(cid:27)
(cid:12)
(cid:27)
(cid:12)
(cid:4)
(cid:27)
(cid:12)
(cid:4)
(cid:1)
+
(cid:17)
(cid:18)
(cid:27)
(cid:27)
(cid:30)
(cid:12)
(cid:0)
(cid:9)
(cid:12)
(cid:4)
(cid:5)
(cid:29)
(cid:27)
(cid:12)
(cid:4)
+
(cid:17)
(cid:18)
(cid:5)
(cid:15)
(cid:27)
(cid:27)
(cid:30)
(cid:12)
(cid:5)
(cid:15)
(cid:0)
(cid:12)
(cid:4)
(cid:5)
(cid:29)
(cid:6)
(cid:30)


<!-- pdf-page: 5 -->
Corollary 3 If MW is used with P1 set to the uniform distribution then its total loss is bounded by

,+

.50

(cid:0)(cid:8)(cid:7)

(cid:0)(cid:8)(cid:7)

M (cid:6) P

(cid:9) Q

1

min
P

1

M (cid:6) P (cid:9) Q

ln (cid:0)

.10

where

and

are as deﬁned in Theorem 1.

Proof: If (cid:4)

1 (cid:6)

(cid:4)(cid:11)(cid:12)(cid:19)(cid:8)

1

for all (cid:4) then RE

1

ln (cid:0)

for all (cid:4)

.

Next we discuss the choice of the parameter
increases to in(cid:2)nity. On the other hand, if we (cid:2)x

. As

approaches 1,

and let the number of rounds (cid:23)
. Thus, by choosing

approaches 1 from above while
increase, the second
as a function of (cid:23)

ln (cid:0) becomes negligible (since it is (cid:2)xed) relative to (cid:23)

term
which approaches 1 for (cid:23)(cid:1)(cid:0)(cid:3)(cid:2)
than the loss of the best strategy. This is formalized in the following corollary:

, the learner can ensure that its average per›trial loss will not be much worse

Corollary 4 Under the conditions of Theorem 1 and with

set to

the average per-trial loss suffered by the learner is

1

2 ln

1

where

,+

1

(cid:0)(cid:8)(cid:7)

1

M (cid:6) P

(cid:9) Q

1

(cid:0)%(cid:7)

min
P

1

M (cid:6) P (cid:9) Q

2 ln (cid:0)

ln (cid:0)

(cid:8)(cid:6)(cid:5)

(cid:8)(cid:8)(cid:7)(cid:8)(cid:9)

(cid:10)(cid:11)(cid:5)

ln (cid:0)

(cid:23)(cid:13)(cid:12)

ln

(cid:6) 1

2

(cid:6) 2

(cid:12) for

(cid:6) 0 (cid:9) 1(cid:3) . Applying this approximation and the

Proof: It can be shown that
given choice of
Since D

yields the result.
0 as (cid:23)(cid:6)(cid:0)(cid:15)(cid:2)

, we see that the amount by which the average per›trial loss of the learner

exceeds that of the best mixed strategy can be made arbitrarily small for large (cid:23)

.

Note that in the analysis we made no assumption about the strategy used by the environment. Theorem 1
guarantees that its cumulative loss is not much larger than that of any (cid:2)xed mixed strategy. As shown
below, this implies that the loss cannot be much larger than the game value. However, if the environment is
non›adversarial, there might be a better row strategy, in which case the algorithm is guaranteed to be almost
as good as this better strategy.

Corollary 5 Under the conditions of Corollary 4,

(+

1

(cid:0)(cid:8)(cid:7)

1

M (cid:6) P

(cid:9) Q

where (cid:16)

is the value of the game M.

(+

Proof: Let (cid:4)
Corollary 4,

(cid:13) be a minmax strategy for (cid:3)

so that for all column strategies (cid:5)

, (cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

(cid:9)(cid:12)(cid:5)

. Then, by

1

(cid:0)(cid:8)(cid:7)

1

(cid:9)(cid:0)

(cid:3)(cid:0)

,+

(cid:3)(cid:0)

1

(cid:0)(cid:8)(cid:7)

(cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

(cid:9)(cid:12)(cid:5)

(cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

(cid:9)(cid:12)(cid:5)

(cid:8)(cid:12)

1

5

(cid:5)
(cid:15)
(cid:0)
(cid:0)
(cid:12)
(cid:5)
(cid:15)
(cid:0)
(cid:12)
(cid:25)
2
0
2
0
6
(cid:0)
(cid:11)
(cid:4)
(cid:12)
(cid:4)
(cid:13)
+
(cid:30)
(cid:30)
.
0
2
0
(cid:30)
2
0
(cid:30)
(cid:30)
(cid:25)
(cid:4)
(cid:14)
(cid:5)
(cid:9)
(cid:23)
(cid:5)
(cid:15)
(cid:0)
(cid:0)
(cid:12)
(cid:23)
(cid:5)
(cid:15)
(cid:0)
(cid:12)
(cid:25)
D
(cid:5)
$
(cid:14)
D
(cid:5)
$
(cid:14)
(cid:23)
(cid:25)
(cid:23)
(cid:14)
(cid:20)
(cid:27)
(cid:30)
+
(cid:27)
(cid:30)
(cid:12)
6
(cid:30)
(cid:30)
(cid:22)
(cid:30)
(cid:5)
$
(cid:14)
(cid:0)
(cid:23)
(cid:5)
(cid:15)
(cid:0)
(cid:0)
(cid:12)
(cid:16)
(cid:25)
D
(cid:5)
$
(cid:14)
(cid:13)
(cid:12)
(cid:16)
(cid:23)
(cid:5)
(cid:15)
(cid:12)
(cid:23)
(cid:5)
(cid:15)
(cid:13)
(cid:25)
D
(cid:5)
$
(cid:14)
+
(cid:16)
(cid:25)
D
(cid:5)
$
(cid:14)
(cid:20)


<!-- pdf-page: 6 -->
3.1 Convergence with probability one

Suppose that the mixed strategies that are generated by MW are used to select one of the rows at each
iteration. From Theorem 1 and Corollary 4 we know that the expected per›iteration loss of MW approaches
. However, we might want a stronger assurance
the optimal achievable value for any (cid:2)xed strategy as (cid:23)(cid:8)(cid:0)(cid:3)(cid:2)
of the performance of MW; for example, we would like to know that the actual per›iteration loss is, with
high probability, close to the expected value. As the following lemma shows, the per›trial loss of any
(cid:12) away from the expected value.
algorithm for the repeated game is, with high probability, at most (cid:7)
The only required game property is that the game matrix elements are all in

0 (cid:9) 1(cid:3) .

(cid:6) 1

(cid:1)(cid:0)

Lemma 6 Let the players of a matrix game use any pair of methods for choosing their mixed strategies
denote the mixed strategies used by the players
on iteration (cid:18) based on past game events. Let P
and Q
on iteration (cid:18) and let M (cid:6)(cid:8)(cid:4)
that is chosen at random
(cid:12) denote the actual game outcome on iteration (cid:18)
according to P

. Then, for every (cid:2)(cid:4)(cid:3) 0,

and Q

(cid:9)(cid:11)(cid:5)

- 1

(cid:0)%(cid:7)

Pr

M (cid:6)(cid:8)(cid:4)

1

M (cid:6) P

(cid:9) Q

(cid:3)(cid:6)(cid:2)

2 exp

2

1
2 (cid:23)(cid:7)(cid:2)

where probability is taken with respect to the random choice of rows (cid:4) 1 (cid:9)(cid:22)(cid:20)(cid:21)(cid:20)(cid:21)(cid:20)(cid:10)(cid:9)

and columns (cid:5) 1 (cid:9)(cid:21)(cid:20)(cid:22)(cid:20)(cid:21)(cid:20)

.

Proof: The proof follows directly from a theorem proved by Hoeffding [22] about the convergence of a
sum of bounded›step martingales which is commonly called (cid:147)Azuma’s lemma.(cid:148) The sequence of random
variables (cid:8)
are bounded
(cid:3) 0
in

1. Thus we can directly apply Azuma’s Lemma and get that, for any

(cid:11)(cid:12) is a martingale difference sequence. As the entries of (cid:3)

0 (cid:9) 1(cid:3) we have that (cid:9)

(cid:3)(cid:7)(cid:6)(cid:8)(cid:4)

(cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

(cid:10)(cid:0)

(cid:11)(cid:9)(cid:7)(cid:5)

(cid:9)(cid:0)

(cid:10)(cid:9)

(cid:9)(cid:11)(cid:5)

(cid:0)(cid:8)(cid:7)

Pr

1

2 exp

2

2 (cid:23)(cid:13)(cid:12)

Substituting

(cid:8)(cid:14)(cid:2)

(cid:23) we get the statement of the lemma.

If we want to have an algorithm whose performance will converge to the optimal performance we need
the value of
to approach 1 as the length of the sequence increases. One way of doing this, which we
describe here, is to have the row player divide the time sequence into (cid:147)epochs.(cid:148) In each epoch, the row
player restarts the algorithm MW (resetting all the row distribution to the uniform distribution) and uses a
which is tuned according to the length of the epoch. We show that such a procedure can
different value of
guarantee, almost surely, that the long term per›iteration loss is at most the expected loss of any (cid:2)xed mixed
strategy.

We denote the length of the (cid:15) th epoch by (cid:23)(cid:17)(cid:16) and the value of
of epochs that gives convergence with probability one is the following:

used for that epoch by

(cid:16) . One choice

2

(cid:23)(cid:18)(cid:16)

(cid:8)(cid:14)(cid:15)

1

1

2 ln
(cid:16) 2

(cid:6) 6 (cid:12)

The convergence properties of this strategy are given in the following theorem:

Theorem 7 Suppose the repeated game is continued for an unbounded number of rounds. Let P
according to the method of epochs with the parameters described in Equation (6), and let (cid:4)
random according to P
Then, for every (cid:2)(cid:13)(cid:3)
following inequality holds for all but a ﬁnite number of values of (cid:23)

be chosen
be chosen at
as an arbitrary stochastic function of past plays.
0, with probability one with respect to the randomization used by both players, the

. Let the environment choose (cid:5)

:

,+

1

(cid:0)(cid:8)(cid:7)

M (cid:6)(cid:8)(cid:4)

(cid:9)(cid:11)(cid:5)

1

1

(cid:0)(cid:8)(cid:7)

min
P

1

M (cid:6) P (cid:9)(cid:11)(cid:5)

(cid:2)(cid:7)(cid:20)

6

6
(cid:23)
(cid:2)
(cid:0)
(cid:0)
(cid:0)
(cid:0)
(cid:0)
(cid:0)
(cid:23)
(cid:5)
(cid:5)
(cid:5)
(cid:5)
(cid:5)
(cid:5)
(cid:15)
(cid:11)
(cid:0)
(cid:9)
(cid:5)
(cid:0)
(cid:12)
(cid:27)
(cid:0)
(cid:0)
(cid:12)
(cid:13)
(cid:5)
(cid:5)
(cid:5)
(cid:5)
(cid:5)
3
+
(cid:17)
(cid:27)
(cid:18)
(cid:9)
(cid:4)
(cid:5)
(cid:9)
(cid:5)
(cid:5)
(cid:0)
(cid:8)
(cid:0)
(cid:0)
(cid:12)
(cid:27)
(cid:2)
(cid:8)
(cid:0)
+
.
-
(cid:5)
(cid:5)
(cid:5)
(cid:5)
(cid:5)
(cid:5)
(cid:15)
(cid:8)
(cid:0)
(cid:5)
(cid:5)
(cid:5)
(cid:5)
(cid:5)
(cid:3)
.
3
+
(cid:11)
(cid:27)
.
(cid:20)
.
(cid:30)
(cid:30)
(cid:30)
(cid:30)
(cid:9)
(cid:30)
(cid:16)
(cid:8)
(cid:25)
(cid:4)
(cid:14)
(cid:20)
(cid:0)
(cid:0)
(cid:0)
(cid:0)
(cid:23)
(cid:5)
(cid:15)
(cid:0)
(cid:0)
(cid:12)
(cid:23)
(cid:5)
(cid:15)
(cid:0)
(cid:12)
(cid:25)


<!-- pdf-page: 7 -->
Proof: For each epoch (cid:15) we select the accuracy parameter (cid:2)
iterations that constitute the (cid:15) ’th epoch by
that epoch is within (cid:2)

from its expected value, i.e., if

,+

. We denote the sequence of
(cid:16) . We call the (cid:15) th epoch (cid:147)good(cid:148) if the average per trial loss for

ln (cid:15)

2 (cid:0)

(cid:3)(cid:7)(cid:6)

(cid:9)(cid:11)(cid:5)

(cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

(cid:3)(cid:2)(cid:5)(cid:4)(cid:7)(cid:6)

(cid:8)(cid:2)(cid:9)(cid:4)(cid:10)(cid:6)

(cid:6) 7 (cid:12)

From Lemma 6 (where we de(cid:2)ne (cid:11)
the probability that the (cid:15) th epoch is bad is bounded by

to be the mixed strategy which gives probability one to (cid:5)

), we get that

2 exp

2

1
2 (cid:23)(cid:18)(cid:16)

2
2 (cid:20)

is (cid:2)nite. Thus, by the Borel›Cantelli lemma, we know that
The sum of this bound over all (cid:15)
with probability one all but a (cid:2)nite number of epochs are good. Thus for the sake of computing the average
loss for (cid:23)(cid:8)(cid:0)(cid:3)(cid:2) we can ignore the in(cid:3)uence of the bad epochs.

from 1 to (cid:2)

We now use Corollary 4 to bound the expected total loss. We apply this corollary in the case that (cid:5)
. We have from the corollary:

again de(cid:2)ned to be the mixed strategy which gives probability one to (cid:5)

(cid:9)(cid:0)

,+

5(cid:0)

(cid:19)(cid:0)

(cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

(cid:9)(cid:11)(cid:5)

min(cid:12)

(cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

2 (cid:23)(cid:18)(cid:16)

ln (cid:0)

ln (cid:0)

(cid:3)(cid:2)(cid:5)(cid:4)

(cid:3)(cid:2)(cid:5)(cid:4)

is

(cid:6) 8 (cid:12)

Combining Equations (7) and (8) we (cid:2)nd that if the (cid:15) th epoch is good then, for any distribution (cid:152)(cid:4) over

the actions of the algorithm

(cid:3)(cid:7)(cid:6)(cid:8)(cid:4)

(cid:11)(cid:9)(cid:11)(cid:5)

(cid:3)(cid:2)(cid:5)(cid:4)(cid:7)(cid:6)

(cid:3)(cid:2)(cid:5)(cid:4)(cid:7)(cid:6)

(cid:3)(cid:2)(cid:5)(cid:4)(cid:7)(cid:6)

(cid:3)(cid:7)(cid:6) (cid:152)(cid:4)

(cid:9)(cid:11)(cid:5)

(cid:3)(cid:7)(cid:6) (cid:152)(cid:4)

(cid:9)(cid:11)(cid:5)

2 (cid:23)(cid:18)(cid:16)

ln (cid:0)

ln (cid:0)

(cid:23)(cid:18)(cid:16)

(cid:0) 2 ln (cid:0)

ln (cid:0)

2 (cid:15)

ln (cid:15)

epochs (ignoring the (cid:2)nite number of bad iterations whose in(cid:3)uence is

Thus the total loss over the (cid:2)rst (cid:1)
negligible) is bounded by

(cid:19)(cid:0)

(cid:3)(cid:7)(cid:6)(cid:8)(cid:4)

(cid:8)(cid:2)(cid:9)(cid:4)

(cid:4)(cid:7)(cid:18)

(cid:3)(cid:2)(cid:5)(cid:4)

(cid:4)(cid:7)(cid:18)

1 (cid:14)(cid:16)(cid:15)(cid:17)(cid:15)(cid:17)(cid:15)

1 (cid:14)(cid:16)(cid:15)(cid:17)(cid:15)(cid:17)(cid:15)

(cid:3)(cid:2)(cid:5)(cid:4)

1 (cid:14)(cid:16)(cid:15)(cid:17)(cid:15)(cid:17)(cid:15)

(cid:3)(cid:7)(cid:6) (cid:152)(cid:4)

(cid:9)(cid:11)(cid:5)

(cid:8)(cid:12)

(cid:3)(cid:7)(cid:6) (cid:152)(cid:4)

(cid:9)(cid:11)(cid:5)

1

2

(cid:0) 2 ln (cid:0)

ln (cid:0)

2 (cid:15)

ln (cid:15)

(cid:22)(cid:21)

ln (cid:1)

(cid:0) 2 ln (cid:0)

ln (cid:0)

2 (cid:21)

As the total number of rounds in the (cid:2)rst (cid:1)
sides by the number of rounds, the error term decreases to zero.

epochs is

1 (cid:15)

2

3

(cid:6)(cid:6)(cid:1)

(cid:12) we (cid:2)nd that, after dividing both

4 Relation to on-line learning

One interesting use of game theory is in the context of predictive decision making (see, for instance,
Blackwell and Girshick [4] or Ferguson [11]). On›Line decision making can be viewed as a repeated game
between a decision maker and nature. The entry (cid:3)(cid:7)(cid:6)
(cid:12) represents the loss of (or negative utility for) the
prediction algorithm if it chooses action (cid:4) at time (cid:18) . The goal of the algorithm is to adaptively generate
distributions over actions so that its expected cumulative loss will not be much worse than the cumulative
loss it would have incurred had it been able to choose a single ﬁxed distribution with prior knowledge of the
whole sequence of columns.

7

(cid:16)
(cid:8)
6
(cid:15)
(cid:1)
(cid:16)
(cid:15)
(cid:0)
(cid:4)
(cid:0)
(cid:0)
(cid:12)
(cid:15)
(cid:0)
(cid:0)
(cid:9)
(cid:5)
(cid:0)
(cid:12)
(cid:25)
(cid:23)
(cid:16)
(cid:2)
(cid:16)
(cid:20)
(cid:0)
(cid:0)
(cid:17)
(cid:27)
(cid:2)
(cid:16)
(cid:18)
(cid:8)
(cid:15)
(cid:0)
(cid:15)
(cid:0)
(cid:6)
(cid:0)
(cid:12)
(cid:15)
(cid:0)
(cid:6)
(cid:9)
(cid:5)
(cid:12)
(cid:25)
(cid:13)
(cid:25)
(cid:20)
(cid:15)
(cid:0)
(cid:0)
(cid:0)
(cid:12)
+
(cid:15)
(cid:0)
(cid:0)
(cid:12)
(cid:25)
(cid:13)
(cid:25)
(cid:25)
(cid:2)
(cid:16)
+
(cid:15)
(cid:0)
(cid:0)
(cid:12)
(cid:25)
(cid:15)
(cid:25)
(cid:25)
(cid:0)
(cid:20)
(cid:15)
(cid:0)
(cid:14)
(cid:0)
(cid:9)
(cid:5)
(cid:12)
+
(cid:15)
(cid:0)
(cid:14)
(cid:0)
(cid:25)
(cid:19)
(cid:15)
(cid:16)
(cid:7)
(cid:20)
(cid:15)
(cid:25)
(cid:25)
(cid:0)
+
(cid:15)
(cid:0)
(cid:14)
(cid:4)
(cid:18)
(cid:0)
(cid:12)
(cid:25)
(cid:1)
(cid:0)
(cid:20)
(cid:25)
(cid:25)
(cid:20)
(cid:4)
(cid:19)
(cid:16)
(cid:7)
(cid:8)
(cid:7)
(cid:4)
(cid:9)
(cid:18)


<!-- pdf-page: 8 -->
This is a non›standard framework for analyzing on›line decision algorithms in that one makes no
statistical assumptions regarding the relationship between actions and their losses. The only assumption
is that there exists some (cid:2)xed mixed strategy (distribution over actions) whose expected performance is
nontrivial. This approach was previously described in one of our earlier papers [16]; the current paper
expands and re(cid:2)nes the results given there.

The algorithm MW was originally suggested by Littlestone and Warmuth [25] and (in a somewhat more
sophisticated form) by Vovk [30] in the context of on›line prediction. The algorithm was also discovered
independently by Fudenberg and Levine [17]. Research on the use of the multiplicative weights algorithm
for on›line prediction is extensive and on›going, and it is out of the scope of this paper to give a complete
review of it. However, we try to sketch some of the main connections between the work described in this
paper and this expanding line of research.

The on›line prediction framework is a re(cid:2)nement of the decision theoretic framework described above.
Here the prediction algorithm generates distributions over predictions, nature chooses an outcome and the
loss incurred by the prediction algorithm is a known loss function which maps action/outcome pairs to real
values. This framework restricts the choices that can be made by nature because once the predictions have
been (cid:2)xed, the only loss columns that are possible are those that correspond to possible outcomes. This is
the reason that for various loss functions one can prove better bounds than in the less structured context of
on›line decision making. The approach is closely related to work by Dawid [9], Foster [12] and Vovk [30].
One loss function that has received particular attention is the log loss function. Here the prediction is
assumed to be a distribution (cid:0)
,
and the loss is
(cid:12) . This loss has several important interpretations which connect it to likelihood
analysis and to coding theory. Note that as the probability of an element can be arbitrarily small, the loss can
be arbitrarily high. On›Line algorithms for making predictions in this case have been extensively studied in
information theory under the name universal compression of individual sequences [32, 28]. In particular, a
well›known result is that the multiplicative weights algorithm, with
is a near›optimal algorithm
in this context.
It is also interesting to note that this version of the multiplicative weights algorithm is
equivalent to the Bayes prediction rule, where the generated distributions over the rows are equal to the
Bayesian posterior distributions. On the other hand, this equivalence holds only for the log›loss; for other
loss functions there is no simple relationship between the multiplicative weights algorithm and the Bayesian
algorithm.

, the outcome is an element from the domain (cid:4)

over some domain (cid:1)

set to 1

log (cid:0)

(cid:3)(cid:2)

Cover and Ordentlich [7, 6] and later Helmbold et al. [21] extended the log›loss analysis to the design
of algorithms for (cid:147)universal portfolios.(cid:148) There is an extensive literature on on›line prediction with other
speci(cid:2)c loss functions. For example, for work on prediction loss, see Feder, Merhav and Gutman [10],
Cesa›Bianchi et al. [5] and for work on more general families of loss functions see Vovk [29] and Kivinen
and Warmuth [23].

Another extension of the on›line decision problem that is worth mentioning here is making decisions
when the feedback given is a single entry of the game matrix. In other words, we assume that after the row
player has chosen a distribution over the rows, a single row is chosen at random according to the distribution.
The row player suffers the loss associated with the selected row and the column chosen by its opponent, and
the game repeats. The goal of the row player is the same as before(cid:151)to minimize its expected average loss
over a sequence of repeated games. Clearly, the goal is much harder here since only a single entry of the
matrix is revealed on each round. Auer et al. [2] study this model in detail and show that a variant of the
multiplicative weights algorithm converges to the performance of the best row distribution in repeated play.

8

(cid:22)
(cid:1)
(cid:27)
(cid:6)
(cid:4)
(cid:30)
6


<!-- pdf-page: 9 -->
5 Proof of the minmax theorem

. More
Corollary 5 shows that the loss of MW can never exceed the value of the game (cid:3)
interestingly, Corollary 4 can be used to derive a very simple proof of von Neumann’s minmax theorem. To
prove this theorem, we need to show that

by more than D

min
P

max
Q

M (cid:6) P (cid:9) Q (cid:12)

max
Q

min
P

M (cid:6) P (cid:9) Q (cid:12)(cid:24)(cid:20)

(cid:6) 9 (cid:12)

(Proving that minP maxQ M (cid:6) P (cid:9) Q (cid:12)

is relatively straightforward and so is omitted.)
Suppose that we run algorithm MW against a maximally adversarial environment which always chooses

maxQ minP M (cid:6) P (cid:9) Q (cid:12)

strategies which maximize the learner’s loss. That is, on each round (cid:18) , the environment chooses

(cid:4)#(cid:5)

(cid:4)(cid:6)(cid:5)

(cid:0)(cid:8)(cid:7)

(cid:0)(cid:8)(cid:7)

(cid:9)(cid:0)

(cid:10)(cid:0)

Q

arg max

Q

M (cid:6) P

(cid:9) Q (cid:12)

(cid:6) 10 (cid:12)

Let (cid:4)

1

and (cid:5)

1 (cid:4)

1

1 (cid:5)

. Clearly, (cid:4)

and (cid:5)

are probability distributions.

Then we have:

min
P

max
Q

PTMQ

PTMQ

max
Q

1

(cid:0)%(cid:7)

max
Q

1

P

TMQ

by de(cid:2)nition of P

1

(cid:0)(cid:8)(cid:7)

1

(cid:0)(cid:8)(cid:7)

1

1

P

TMQ

max
Q

P

TMQ

by de(cid:2)nition of Q

1

(cid:0)(cid:8)(cid:7)

PTMQ

1

PTMQ

min
P

min
P

max
Q

min
P

PTMQ

by Corollary 4

by de(cid:2)nition of Q

Since D

can be made arbitrarily close to zero, this proves Eq. (9) and the minmax theorem.

6 Approximately solving a game

Aside from yielding a proof for a famous theorem that by now has many proofs, the preceding derivation
shows that algorithm MW can be used to (cid:2)nd an approximate minmax or maxmin strategy. Finding these
(cid:147)optimal(cid:148) strategies is called solving the game (cid:3)

.

can use the average of the generated row distributions over (cid:23)
and
game. This method sets (cid:23)

We give three methods for solving a game using exponential weights. In Section 6.1 we show how one
iterations as an approximate solution for the
as a function of the desired accuracy before starting the iterative process.
In Section 6.2 we show that if an upper bound (cid:0) on the value of the game is known ahead of time then
one can use a variant of MW that generates a sequence of row distributions such that the expected loss of the
. Finally, in Section 6.3 we describe a related adaptive method that generates a
(cid:18) th distribution approaches (cid:0)
sparse approximate solution for the column distribution. At the end of the paper, in Section 7, we show that
the convergence rate of the two last methods is asymptotically optimal.

9

(cid:5)
$
(cid:14)
+
(cid:6)
(cid:0)
(cid:8)
(cid:0)
(cid:20)
(cid:8)
(cid:5)
(cid:8)
(cid:5)
+
(cid:8)
(cid:23)
(cid:5)
(cid:15)
(cid:0)
+
(cid:23)
(cid:5)
(cid:15)
(cid:0)
(cid:8)
(cid:23)
(cid:5)
(cid:15)
(cid:0)
(cid:0)
(cid:0)
+
(cid:23)
(cid:5)
(cid:15)
(cid:0)
(cid:25)
D
(cid:5)
$
(cid:14)
(cid:8)
(cid:25)
D
(cid:5)
$
(cid:14)
+
(cid:25)
D
(cid:5)
$
(cid:14)
(cid:20)
(cid:5)
$
(cid:14)
(cid:30)


<!-- pdf-page: 10 -->
6.1 Using the average of the row distributions

Skipping the (cid:2)rst inequality of the sequence of equalities and inequalities at the end of Section 5, we see
that

M (cid:6) P (cid:9) Q (cid:12)

max
Q

max
Q

min
P

M (cid:6) P (cid:9) Q (cid:12)

Thus, the vector (cid:4)

is an approximate minmax strategy in the sense that for all column strategies (cid:5)

(cid:3)(cid:7)(cid:6)

(cid:9)(cid:7)(cid:5)

(cid:12) does not exceed the game value (cid:16) by more than D

. Since D

,
can be made arbitrarily small,

this approximation can be made arbitrarily tight.

Similarly, ignoring the last inequality of this derivation, we have that

M (cid:6) P (cid:9) Q (cid:12)

min
P

also is an approximate maxmin strategy. Furthermore, it can be shown that a column strategy (cid:5)

so (cid:5)
satisfying Eq. (10) can always be chosen to be a pure strategy (i.e., a mixed strategy concentrated on a single
has the additional favorable property of
column of (cid:3)
being sparse in the sense that at most (cid:23) of its entries will be nonzero.

). Therefore, the approximate maxmin strategy (cid:5)

6.2 Using the ﬁnal row distribution

In the analysis presented so far we have shown that the average of the strategies used by MW converges to
an optimal strategy. Now we show that if the row player knows an upper bound (cid:0) on the value of the game
then it can use a variant of MW to generate a sequence of mixed strategies that approach a strategy which
for each round of the game.
, then the row player does not change the
then the row player

achieves loss (cid:0)
If the expected loss on the (cid:18) th iteration (cid:3)(cid:7)(cid:6)(cid:6)(cid:4)
mixed strategy, because, in a sense, it is (cid:147)good enough.(cid:148) However, if (cid:3)(cid:7)(cid:6)
uses MW with parameter

.1 To do that we have the algorithm select a different value of

is less than (cid:0)

(cid:3)(cid:0)

(cid:3)(cid:0)

(cid:3)(cid:0)

(cid:10)(cid:0)

(cid:9)(cid:0)

(cid:9)(cid:12)(cid:5)

(cid:9)(cid:12)(cid:5)

(cid:11)(cid:12)

(cid:6) 1

(cid:6) 1

(cid:9)(cid:0)

(cid:10)(cid:0)

(cid:3)(cid:7)(cid:6)

(cid:9)(cid:12)(cid:5)

(cid:12)(cid:10)(cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

(cid:11)(cid:9)(cid:7)(cid:5)

(cid:11)(cid:12)

We call this algorithm vMW (the (cid:147)v(cid:148) stands for (cid:147)variable(cid:148)). For this algorithm, as the following theorem
and any mixed strategy that achieves (cid:0) decreases by an amount that is a
shows, the distance between (cid:4)
function of the divergence between (cid:3)(cid:7)(cid:6)

(cid:8)(cid:12) and (cid:0)

.

(cid:10)(cid:0)

(cid:1)(cid:0)

(cid:1)(cid:0)

,+

(cid:9)(cid:7)(cid:5)

Theorem 8 Let (cid:152)P be any mixed strategy for the rows such that maxQ M (cid:6) (cid:152)P (cid:9) Q (cid:12)
of algorithm vMW in which M (cid:6) P

the relative entropy between (cid:152)P and P

(cid:9) Q

(cid:0)(cid:8)(cid:29)

(cid:0)(cid:8)(cid:29)

. Then on any iteration
1 satisﬁes

RE (cid:0) (cid:152)P

(cid:26)+

P

1 (cid:1)

(cid:3)(cid:0)

RE (cid:0) (cid:152)P

P

RE

M (cid:6) P

(cid:9) Q

Proof: Note that when (cid:0)
of (cid:152)(cid:4)

and the statement of Lemma 2 we get that

(cid:9)(cid:0)(cid:8)(cid:29)

(cid:9)(cid:0)

(cid:3)(cid:7)(cid:6)

(cid:9)(cid:12)(cid:5)

(cid:12) we get that

1. Combining this observation with the de(cid:2)nition

RE (cid:0) (cid:152)(cid:4)

1 (cid:1)

(cid:8)(cid:12)

(cid:3)(cid:7)(cid:6) (cid:152)(cid:4)

(cid:9)(cid:12)(cid:5)

ln (cid:6) 1

RE (cid:0) (cid:152)(cid:4)

(cid:12) ln (cid:6) 1

ln

1

(cid:6) 1

(cid:9)(cid:0)

(cid:3)(cid:0)

(cid:3)(cid:7)(cid:6)

(cid:9)(cid:12)(cid:5)

(11)

ln

1

(cid:6) 1

(cid:8)(cid:12)

(cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

(cid:9)(cid:12)(cid:5)

(cid:8)(cid:12)

1If no such upper bound is known, one can use the standard trick of solving the larger game matrix

whose value is always zero.

(cid:3)(cid:4)(cid:1)

T

10

+
(cid:25)
D
(cid:5)
$
(cid:14)
(cid:8)
(cid:16)
(cid:25)
D
(cid:5)
$
(cid:14)
(cid:20)
(cid:4)
(cid:5)
$
(cid:14)
(cid:5)
$
(cid:14)
(cid:6)
(cid:16)
(cid:27)
D
(cid:5)
$
(cid:14)
(cid:0)
(cid:16)
(cid:30)
(cid:0)
(cid:4)
(cid:12)
(cid:6)
(cid:0)
(cid:30)
(cid:0)
(cid:8)
(cid:0)
(cid:27)
(cid:4)
(cid:12)
(cid:12)
(cid:27)
(cid:0)
(cid:20)
(cid:4)
(cid:0)
(cid:0)
(cid:0)
(cid:12)
(cid:6)
(cid:0)
(cid:12)
+
(cid:12)
(cid:0)
(cid:1)
(cid:27)
(cid:11)
(cid:0)
(cid:12)
(cid:0)
(cid:0)
(cid:12)
(cid:13)
(cid:20)
(cid:4)
(cid:0)
(cid:30)
(cid:0)
+
(cid:12)
(cid:4)
(cid:27)
(cid:12)
(cid:4)
(cid:1)
+
(cid:0)
6
(cid:30)
(cid:0)
(cid:12)
(cid:25)
(cid:11)
(cid:27)
(cid:27)
(cid:30)
(cid:0)
(cid:12)
(cid:4)
(cid:0)
(cid:0)
(cid:12)
(cid:13)
+
(cid:0)
6
(cid:30)
(cid:0)
(cid:25)
(cid:11)
(cid:27)
(cid:27)
(cid:30)
(cid:0)
(cid:13)
(cid:20)
(cid:17)
(cid:1)
(cid:2)
(cid:2)
(cid:18)
(cid:5)


<!-- pdf-page: 11 -->
The choice of
expression we get the statement of the theorem.

was chosen to minimize the last expression. Plugging the given choice of

into this last

Suppose (cid:3)(cid:7)(cid:6)(cid:6)(cid:4)
yielding the bound

(cid:9)(cid:12)(cid:5)

for all (cid:18) . Then the main inequality of this theorem can be applied repeatedly

RE (cid:0) (cid:152)(cid:4)

1 (cid:1)

RE (cid:0) (cid:152)(cid:4)

1 (cid:1)

(cid:10)(cid:0)

(cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

(cid:9)(cid:7)(cid:5)

(cid:8)(cid:12)

(cid:0)(cid:8)(cid:7)

RE

1

Since relative entropy is nonnegative, and since the inequality holds for all (cid:23)

, we have

(cid:10)(cid:0)

(cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

(cid:9)(cid:7)(cid:5)

(cid:11)(cid:12)

RE (cid:0) (cid:152)(cid:4)

1 (cid:1)

(cid:0)(cid:8)(cid:7)

RE

1

(cid:6) 12 (cid:12)

Assuming that RE (cid:0) (cid:152)(cid:4)
for instance, that (cid:3)(cid:7)(cid:6)(cid:6)(cid:4)
can prove the following:

(cid:9)(cid:12)(cid:5)

(cid:3)(cid:0)

is (cid:2)nite (as it will be, for example, if (cid:4)

(cid:2) at most (cid:2)nitely often for any (cid:2)

1 is uniform), this inequality implies,
0. More speci(cid:2)cally, we

1 (cid:1)
(cid:8)(cid:12) can exceed (cid:0)

Corollary 9 Suppose that vMW is used to play a game M whose value is known to be at most (cid:0)
. Suppose
also that we choose P1 to be the uniform distribution. Then for any sequence of column strategies Q1 (cid:9) Q2 (cid:9)(cid:21)(cid:20)(cid:22)(cid:20)(cid:21)(cid:20) ,
the number of rounds on which the loss M (cid:6) P

is at most

(cid:9) Q

(cid:8)(cid:12)

ln (cid:0)

(cid:1)(cid:0)

(cid:3)(cid:0)

RE

(cid:1)(cid:0)

Proof: Since rounds on which (cid:3)(cid:7)(cid:6)
of generality that (cid:3)(cid:7)(cid:6)(cid:6)(cid:4)
for which the loss is at least (cid:0)

(cid:10)(cid:0)

(cid:9)(cid:7)(cid:5)

(cid:8)(cid:12)

(cid:11)(cid:9)(cid:12)(cid:5)

(cid:11)(cid:12)

for all rounds (cid:18) . Let

(cid:0) are effectively ignored by vMW, we assume without loss
(cid:2)(cid:3)(cid:2) be the set of rounds

: (cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

(cid:10)(cid:0)

(cid:1)(cid:0)

(cid:9)(cid:7)(cid:5)

(cid:8)(cid:12)

(cid:2) , and let (cid:4)

(cid:13) be a minmax strategy. By Eq. (12), we have that

(cid:9)(cid:0)

(cid:3)(cid:0)

RE

RE

(cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

(cid:9)(cid:12)(cid:5)

(cid:8)(cid:12)

(cid:9)(cid:0)

(cid:3)(cid:0)

(cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

(cid:9)(cid:12)(cid:5)

(cid:8)(cid:12)

1

ln (cid:0)

RE

(cid:3)(cid:2)(cid:5)(cid:4)

(cid:8)(cid:2)(cid:9)(cid:4)

(cid:0)(cid:8)(cid:7)

1
RE

ln (cid:0)

1+

RE

Therefore,

In Section 7, we show that this dependence on (cid:0)

, (cid:0) and (cid:2) cannot be improved by any constant factor.

6.3 Convergence of a column distribution

is (cid:2)xed, we showed in Section 6.1 that the average (cid:5)

When
game, i.e., that there are no rows (cid:4) for which (cid:3)(cid:7)(cid:6)
above in which

’s is an approximate solution of the
. For the algorithm described
varies, we can derive a more re(cid:2)ned bound of this kind for a weighted mixture of the

of the (cid:5)
is less than (cid:16)

(cid:3)(cid:0)

(cid:3)(cid:27)

’s.

11

(cid:30)
(cid:0)
(cid:30)
(cid:0)
(cid:0)
(cid:0)
(cid:12)
(cid:6)
(cid:0)
(cid:12)
(cid:4)
(cid:5)
(cid:29)
+
(cid:12)
(cid:4)
(cid:27)
(cid:5)
(cid:15)
(cid:11)
(cid:0)
(cid:12)
(cid:0)
(cid:13)
(cid:20)
(cid:0)
(cid:15)
(cid:11)
(cid:0)
(cid:12)
(cid:0)
(cid:13)
+
(cid:12)
(cid:4)
(cid:20)
(cid:12)
(cid:4)
(cid:0)
(cid:25)
(cid:3)
(cid:0)
(cid:0)
(cid:6)
(cid:0)
(cid:25)
(cid:2)
(cid:11)
(cid:0)
(cid:12)
(cid:0)
(cid:25)
(cid:2)
(cid:13)
(cid:20)
(cid:4)
(cid:10)
(cid:6)
(cid:0)
(cid:1)
(cid:8)
(cid:1)
(cid:18)
(cid:6)
(cid:0)
(cid:25)
(cid:25)
(cid:15)
(cid:0)
(cid:11)
(cid:0)
(cid:12)
(cid:0)
(cid:25)
(cid:2)
(cid:13)
+
(cid:15)
(cid:0)
(cid:11)
(cid:0)
(cid:12)
(cid:13)
+
(cid:0)
(cid:15)
(cid:11)
(cid:0)
(cid:12)
(cid:13)
+
(cid:11)
(cid:4)
(cid:13)
(cid:12)
(cid:4)
(cid:13)
+
(cid:20)
(cid:9)
(cid:1)
(cid:9)
(cid:11)
(cid:0)
(cid:12)
(cid:0)
(cid:25)
(cid:2)
(cid:13)
(cid:20)
(cid:30)
(cid:0)
(cid:4)
(cid:9)
(cid:5)
(cid:12)
D
(cid:5)
$
(cid:14)
(cid:30)
(cid:0)
(cid:5)


<!-- pdf-page: 12 -->
Theorem 10 Assume that on every iteration of algorithm vMW, we have that M (cid:6) P

(cid:4)#(cid:5)

(cid:0)(cid:8)(cid:7)

(cid:9) Q

(cid:8)(cid:12)

. Let

(cid:136)Q (cid:8)

(cid:4)(cid:6)(cid:5)

(cid:0)(cid:8)(cid:7)

1 Q

ln (cid:6) 1

(cid:8)(cid:12)

1 ln (cid:6) 1

Then

(cid:16)%$

(+

:M

(cid:0)(cid:2)(cid:1)

(cid:136)Q

P1 (cid:6)

(cid:4)(cid:11)(cid:12)

exp

(cid:0)(cid:8)(cid:7)

RE

1

M (cid:6) P

(cid:9) Q

(cid:8)(cid:12)

Proof: If (cid:3)(cid:7)(cid:6) (cid:152)(cid:4)

(cid:9) (cid:136)(cid:5)

, then, combining Eq. 11 for (cid:18)(cid:19)(cid:8)

1 (cid:9)(cid:21)(cid:20)(cid:22)(cid:20)(cid:21)(cid:20)

(cid:9)(cid:24)(cid:23)

, we have

(cid:3)(cid:0)

(cid:9)(cid:0)

(cid:3)(cid:0)

RE (cid:0) (cid:152)(cid:4)

1 (cid:1)

RE (cid:0) (cid:152)(cid:4)

1 (cid:1)

(cid:0)(cid:8)(cid:7)

(cid:3)(cid:7)(cid:6) (cid:152)(cid:4)

(cid:9)(cid:12)(cid:5)

(cid:12) ln (cid:6) 1

ln

1

(cid:6) 1

(cid:0)%(cid:7)

1

(cid:11)(cid:12)

(cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

(cid:9)(cid:12)(cid:5)

(cid:11)(cid:12)

(cid:9)(cid:0)

(cid:3)(cid:0)

1

(cid:3)(cid:7)(cid:6) (cid:152)(cid:4)

(cid:9) (cid:136)(cid:5)

(cid:0)%(cid:7)

(cid:0)%(cid:7)

ln (cid:6) 1

1

ln

1

(cid:6) 1

1

(cid:8)(cid:12)

(cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

(cid:9)(cid:12)(cid:5)

(cid:8)(cid:12)

(cid:10)(cid:0)

(cid:0)(cid:8)(cid:7)

(cid:0)(cid:8)(cid:7)

(cid:4)(cid:3)

ln (cid:6) 1

1

ln

1

(cid:6) 1

1

(cid:9)(cid:0)

(cid:3)(cid:0)

(cid:8)(cid:12)

(cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

(cid:9)(cid:7)(cid:5)

(cid:8)(cid:12)

(cid:0)%(cid:7)

RE

1

(cid:3)(cid:7)(cid:6)

(cid:9)(cid:12)(cid:5)

(cid:9)+

for our choice of
pure strategy, we get

. In particular, if (cid:4)

is a row for which (cid:3)(cid:7)(cid:6)(cid:8)(cid:4)

(cid:9) (cid:136)(cid:5)

, then, setting (cid:152)(cid:4)

to the associated

so

(cid:16)%$

&()

(cid:16)%$

&()

ln

1 (cid:6)

(cid:4)(cid:11)(cid:12)

1 (cid:6)(cid:8)(cid:4)

(cid:0)(cid:8)(cid:7)

RE

1

 #"

 #"

1 (cid:6)(cid:8)(cid:4)(cid:11)(cid:12)

(cid:4)(cid:11)(cid:12) exp

1 (cid:6)

:

(cid:0)(cid:2)(cid:1)

(cid:136)

(cid:0)(cid:2)(cid:1)

(cid:136)

(cid:0)(cid:8)(cid:7)

:

exp

RE

1

since (cid:4)

1 is a distribution.

(cid:10)(cid:0)

(cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

(cid:9)(cid:12)(cid:5)

(cid:0)(cid:8)(cid:7)

RE

1

(cid:10)(cid:0)

(cid:10)(cid:0)

(cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

(cid:9)(cid:7)(cid:5)

(cid:8)(cid:12)

(cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

(cid:9)(cid:7)(cid:5)

(cid:8)(cid:12)

(cid:2)+

Thus, if (cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

1) for which
(cid:0) drops to zero exponentially fast. This will be the case, for instance, if Eq. (10) holds and

, the fraction of rows (cid:4) (as measured by (cid:4)

is bounded away from (cid:0)

(cid:9)(cid:7)(cid:5)

(cid:11)(cid:12)

(cid:28)+

(cid:3)(cid:7)(cid:6)(cid:8)(cid:4)(cid:10)(cid:9) (cid:136)(cid:5)

(cid:9)(cid:27)

(cid:2) for some (cid:2)

(cid:3) 0 where (cid:16)

is the value of (cid:3)

.

Thus a single application of the exponential weights algorithm yields approximate solutions for both
the column and row players. The solution for the row player consists of the multiplicative weights, while
the solution for the column player consists of the distribution on the observed columns as described in
Theorem 10.

Given a game matrix (cid:3)

, we have a choice of whether to solve (cid:3)

be to choose the orientation which minimizes the number of rows.
the relationship between solving (cid:3)
machine learning.
problem described in Section 4, while the (cid:147)dual(cid:148) solution for
called (cid:147)boosting.(cid:148)

In that context, the solution for game matrix (cid:3)

T. One natural choice would
or
In a related paper [16], we studied
T using the multiplicative weights algorithm in the context of
is related to the on›line prediction
T corresponds to a method of learning

or

12

(cid:0)
(cid:0)
(cid:6)
(cid:0)
(cid:0)
6
(cid:30)
(cid:0)
6
(cid:30)
(cid:0)
(cid:12)
(cid:20)
(cid:15)
(cid:16)
"
)
+
(cid:11)
(cid:27)
(cid:5)
(cid:15)
(cid:11)
(cid:0)
(cid:12)
(cid:0)
(cid:0)
(cid:13)
(cid:12)
(cid:20)
(cid:12)
(cid:0)
(cid:12)
(cid:4)
(cid:5)
(cid:29)
(cid:27)
(cid:12)
(cid:4)
+
(cid:5)
(cid:15)
6
(cid:30)
(cid:0)
(cid:12)
(cid:25)
(cid:5)
(cid:15)
(cid:11)
(cid:27)
(cid:27)
(cid:30)
(cid:0)
(cid:13)
(cid:8)
(cid:12)
(cid:5)
(cid:15)
6
(cid:30)
(cid:0)
(cid:12)
(cid:25)
(cid:5)
(cid:15)
(cid:11)
(cid:27)
(cid:27)
(cid:30)
(cid:0)
(cid:13)
+
(cid:0)
(cid:5)
(cid:15)
6
(cid:30)
(cid:0)
(cid:12)
(cid:25)
(cid:5)
(cid:15)
(cid:11)
(cid:27)
(cid:27)
(cid:30)
(cid:0)
(cid:0)
(cid:13)
(cid:8)
(cid:27)
(cid:5)
(cid:15)
(cid:11)
(cid:0)
(cid:12)
(cid:4)
(cid:12)
(cid:13)
(cid:30)
(cid:0)
(cid:12)
(cid:0)
(cid:17)
(cid:4)
(cid:4)
(cid:5)
(cid:29)
(cid:12)
(cid:18)
+
(cid:27)
(cid:5)
(cid:15)
(cid:11)
(cid:0)
(cid:12)
(cid:0)
(cid:0)
(cid:12)
(cid:13)
(cid:15)
(cid:16)
(cid:4)
+
(cid:15)
(cid:16)
(cid:4)
(cid:5)
(cid:29)
(cid:11)
(cid:27)
(cid:5)
(cid:15)
(cid:11)
(cid:0)
(cid:12)
(cid:0)
(cid:13)
(cid:12)
+
(cid:11)
(cid:27)
(cid:5)
(cid:15)
(cid:11)
(cid:0)
(cid:12)
(cid:0)
(cid:13)
(cid:12)
(cid:5)
(cid:29)
(cid:0)
(cid:12)
(cid:0)
(cid:16)
(cid:27)
(cid:3)
(cid:27)
(cid:3)
(cid:27)
(cid:3)


<!-- pdf-page: 13 -->
6.4 Application to linear programming

It is well known that any linear programming problem can be reduced to the problem of solving a game
(see, for instance, Owen [26, Theorem III.2.6]). Thus, the algorithms we have presented for approximately
solving a game can be applied more generally for approximate linear programming.

Similar and closely related methods of approximately solving linear programming problems have pre›
viously appeared, for instance, in the work of Young [31], Grigoriadis and Khachiyan [18, 19] and Plotkin,
Shmoys and Tardos [27].

Although, in principle, our algorithms are applicable to general linear programming problems, they are
best suited to problems of a particular form. Speci(cid:2)cally, they may be most appropriate for the setting
we have described of approximately solving a game when an oracle is available for choosing columns of
the matrix on every round. When such an oracle is available, our algorithm can be applied even when the
number of columns of the matrix is very large or even in(cid:2)nite, a setting that is clearly infeasible for some
of the other, more traditional linear programming algorithms. Solving linear programming problems in the
presence of such an oracle was also studied by Young [31] and Plotkin, Shmoys and Tardos [27]. See also
our earlier paper [16] for detailed examples of problems arising naturally in the (cid:2)eld of machine learning
with exactly these characteristics.

7 Optimality of the convergence rate

In Corollary 9, we showed that using the algorithm vMW starting from the uniform distribution over the rows
guarantees that the number of times that (cid:3)(cid:7)(cid:6)(cid:6)(cid:4)
where (cid:0)
of the rate of convergence on (cid:0)
beat this bound even by a constant factor. This result is formalized by Theorem 11 below.

. In this section, we show that this dependence
is optimal in the sense that no adaptive game›playing algorithm can

is a known upper bound on the value of the game (cid:3)
, (cid:0) and (cid:2)

is bounded by (cid:6) ln (cid:0)

(cid:8)(cid:12) can exceed (cid:0)

RE

(cid:10)(cid:0)

(cid:9)(cid:7)(cid:5)

46

A related lower bound result is proved by Klein and Young [24] in the context of approximately solving

linear programs.

Theorem 11 Let 0 (cid:10)
game-playing algorithm (cid:0)
such that:

, there exists a game matrix M of (cid:0)

1, and let (cid:0) be a sufﬁciently large integer. Then for any adaptive
rows and a sequence of column strategies

1. the value of game M is at most (cid:0) ; and

2. the loss M (cid:6) P

(cid:9) Q

(cid:12) suffered by (cid:0) on each round (cid:18)(cid:19)(cid:8)

1 (cid:9)(cid:22)(cid:20)(cid:21)(cid:20)(cid:22)(cid:20)

is at least (cid:0)

(cid:2) , where

ln (cid:0)
RE

5 ln ln (cid:0)

(cid:3)(cid:2)

(cid:6) 1
RE

(cid:5)(cid:4)(cid:13)(cid:6) 1 (cid:12)(cid:10)(cid:12) ln (cid:0)

Proof: The proof uses a probabilistic argument to show that for any algorithm, there exists a matrix (and
sequence of column strategies) with the properties stated in the theorem. That is, for the purposes of the
proof, we imagine choosing the matrix (cid:3)
at random according to an appropriate distribution, and we show
that the stated properties hold with strictly positive probability, implying that there must exist at least one
matrix for which they hold.

Let (cid:6)

(cid:2) . The random matrix (cid:3)

(cid:3)(cid:7)(cid:6)(cid:8)(cid:4)(cid:10)(cid:9)(cid:11)(cid:5)(cid:13)(cid:12) independently to be 1 with probability (cid:6) , and 0 with probability 1
(algorithm (cid:0)
column player responds with column (cid:18) . That is, the column strategy (cid:5)
on column (cid:18) .

) chooses a row distribution (cid:4)

rows and (cid:23)

columns, and is chosen by selecting each entry
(cid:7)(cid:6) . On round (cid:18) , the row player
, and, for the purposes of our construction, we assume that the
is concentrated

chosen on round (cid:18)

has (cid:0)

13

(cid:0)
(cid:25)
(cid:2)
(cid:12)
(cid:11)
(cid:0)
(cid:12)
(cid:0)
(cid:25)
(cid:2)
(cid:13)
(cid:0)
(cid:10)
(cid:0)
(cid:25)
(cid:2)
(cid:10)
(cid:0)
(cid:0)
(cid:9)
(cid:23)
(cid:25)
(cid:23)
(cid:8)
(cid:1)
(cid:27)
(cid:11)
(cid:0)
(cid:12)
(cid:0)
(cid:25)
(cid:2)
(cid:13)
(cid:6)
(cid:27)
(cid:11)
(cid:0)
(cid:12)
(cid:0)
(cid:25)
(cid:2)
(cid:13)
(cid:20)
(cid:8)
(cid:0)
(cid:25)
(cid:27)
(cid:0)
(cid:0)


<!-- pdf-page: 14 -->
Given this random construction, we need to show that properties 1 and 2 hold with positive probability

for (cid:0)

suf(cid:2)ciently large.

We begin with property 2. On round (cid:18) , the row player chooses a distribution (cid:4)

responds with column (cid:18) . We require that the loss (cid:3)(cid:7)(cid:6)
(cid:12) be at least (cid:6)
is chosen at random, we need a lower bound on the probability that (cid:3)(cid:7)(cid:6)(cid:6)(cid:4)
the row player has sole control over the choice of (cid:4)
independent of (cid:4)

. To this end, we prove the following lemma:

(cid:9)(cid:24)(cid:18)

, and the column player
(cid:2) . Since the matrix (cid:3)
(cid:6) . Moreover, because
, we need a lower bound on this probability which is

(cid:10)(cid:0)

(cid:9)(cid:24)(cid:18)

Lemma 12 For every (cid:6)
positive integer, and let (cid:3) 1 (cid:9)(cid:22)(cid:20)(cid:21)(cid:20)(cid:21)(cid:20)(cid:10)(cid:9)(cid:4)(cid:3)
independent Bernoulli random variables with Pr [ (cid:1)

be nonnegative numbers such that
(cid:6) and Pr [ (cid:1)

(cid:6) 0 (cid:9) 1 (cid:12) , there exists a number (cid:0)(cid:2)(cid:1)

1] (cid:8)

0 with the following property: Let (cid:0) be any
be

1 (cid:9)(cid:21)(cid:20)(cid:22)(cid:20)(cid:21)(cid:20)

1 (cid:3)
0] (cid:8)

1. Let (cid:1)
(cid:7)(cid:6) . Then

1

Pr

1

(cid:0)(cid:5)(cid:1)

(cid:3) 0 (cid:20)

Proof: See appendix.

(cid:9)(cid:0)

To apply the lemma, let (cid:3)

(cid:8)(cid:10)(cid:4)

(cid:6)(cid:8)(cid:4)

(cid:12) and let (cid:1)

(cid:3)(cid:7)(cid:6)(cid:8)(cid:4)

(cid:9)(cid:24)(cid:18)

(cid:12) . Then the lemma implies that

Pr (cid:6)

(cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

(cid:9)(cid:24)(cid:18)

(cid:6)(cid:8)(cid:7)

(cid:0)(cid:9)(cid:1)

(cid:10)(cid:0)

where (cid:0)(cid:5)(cid:1)

is a positive number which depends on (cid:6) but which is independent of (cid:0) and (cid:4)

. It follows that

Pr (cid:6)(cid:11)(cid:10)

: (cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

(cid:9)(cid:24)(cid:18)

In other words, property 2 holds with probability at least (cid:0)

.

We next show that property 1 fails to hold with probability strictly smaller than (cid:0)

so that both properties

must hold simultaneously with positive probability.

46

De(cid:2)ne the weight of row (cid:4) , denoted (cid:12)

,+

We say that a row is light if (cid:12)
rows and zero on the heavy rows. We will show that, with high probability, max (cid:13)
an upper bound of (cid:0) on the value of game (cid:3)

(cid:6)(cid:8)(cid:4)(cid:11)(cid:12) , to be the fraction of 1’s in the row: (cid:12)
1

.
. Let (cid:4)(cid:15)(cid:14) be a row distribution which is uniform over the light
, implying

1 (cid:3)(cid:7)(cid:6)

.

(cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

(cid:4)(cid:11)(cid:12)(cid:19)(cid:8)

(cid:9)(cid:11)(cid:5)(cid:13)(cid:12)

(cid:9)(cid:11)(cid:5)(cid:13)(cid:12)

(cid:6)(cid:8)(cid:4)(cid:11)(cid:12)

Let (cid:16) denote the probability that a given row (cid:4) is light; this will be the same probability for all rows. Let

(cid:14) be the number of light rows.

We show (cid:2)rst that (cid:0)

2 with high probability. The expected value of (cid:0)

(cid:14) is (cid:16)

. Using a form of

Chernoff bounds proved by Angluin and Valiant [1], we have that

(+

Pr (cid:6)

(cid:10)(cid:17)(cid:16)

2(cid:7)

exp (cid:6)

(cid:2)(cid:16)

8 (cid:12)(cid:12)(cid:20)

(cid:6) 13 (cid:12)

We next upper bound the probability that (cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

. Conditional on (cid:4) being
. Moreover, if (cid:4) 1 and (cid:4) 2 are distinct rows, then
(cid:5)(cid:13)(cid:12) are independent, even if we condition on both being light rows. Therefore, applying

(cid:5)(cid:13)(cid:12) exceeds (cid:0)
1

for any column (cid:5)

1 is at most (cid:0)

((cid:27)

a light row, the probability that (cid:3)(cid:7)(cid:6)(cid:8)(cid:4)(cid:10)(cid:9)(cid:11)(cid:5)(cid:13)(cid:12)
(cid:3)(cid:7)(cid:6)(cid:8)(cid:4) 1 (cid:9)(cid:11)(cid:5)(cid:13)(cid:12) and (cid:3)(cid:7)(cid:6)
Hoeffding’s inequality [22] to column (cid:5) and the (cid:0)

(cid:4) 2 (cid:9)

(cid:14) light rows, we have that, for all (cid:5)

,

(+

Thus,

Pr (cid:6)

(cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

(cid:9)(cid:11)(cid:5)(cid:13)(cid:12)

(cid:2)(cid:19)(cid:18)

(cid:21)(cid:20)(cid:23)(cid:22)

2

2

Pr (cid:24) max(cid:13)

(cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

(cid:9)(cid:11)(cid:5)(cid:13)(cid:12)

(cid:14)(cid:26)(cid:25)

2

2

14

(cid:0)
(cid:4)
(cid:0)
(cid:8)
(cid:0)
(cid:25)
(cid:12)
(cid:6)
(cid:0)
(cid:0)
(cid:22)
(cid:3)
(cid:14)
(cid:4)
(cid:14)
(cid:16)
(cid:7)
(cid:16)
(cid:8)
(cid:9)
(cid:1)
(cid:14)
(cid:16)
(cid:8)
(cid:16)
(cid:8)
(cid:27)
-
(cid:14)
(cid:15)
(cid:16)
(cid:7)
(cid:3)
(cid:16)
(cid:1)
(cid:16)
(cid:6)
(cid:6)
3
(cid:6)
(cid:16)
(cid:16)
(cid:8)
(cid:0)
(cid:12)
(cid:6)
(cid:6)
(cid:18)
(cid:0)
(cid:12)
(cid:6)
(cid:6)
(cid:7)
(cid:6)
(cid:0)
(cid:5)
(cid:1)
(cid:20)
(cid:5)
(cid:1)
(cid:5)
(cid:1)
(cid:6)
(cid:4)
(cid:5)
(cid:13)
(cid:7)
(cid:4)
(cid:23)
(cid:0)
(cid:27)
6
(cid:23)
(cid:14)
+
(cid:0)
(cid:0)
(cid:14)
(cid:6)
(cid:16)
(cid:0)
6
(cid:0)
(cid:0)
(cid:14)
(cid:0)
6
(cid:27)
(cid:0)
6
(cid:14)
(cid:9)
(cid:8)
6
(cid:23)
(cid:14)
(cid:3)
(cid:0)
(cid:9)
(cid:0)
(cid:14)
(cid:7)
(cid:14)
(cid:5)
(cid:20)
(cid:14)
(cid:3)
(cid:0)
(cid:9)
(cid:0)
+
(cid:23)
(cid:2)
(cid:18)
(cid:14)
(cid:20)
(cid:22)
(cid:5)


<!-- pdf-page: 15 -->
and so

Pr (cid:24) max(cid:13)

(cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

(cid:9)(cid:11)(cid:5)(cid:13)(cid:12)

2(cid:25)

2

(cid:2)(cid:19)(cid:18)(cid:1)(cid:0)

Combined with Eq. (13), this implies that

Pr (cid:24) max(cid:13)

(cid:3)(cid:7)(cid:6)(cid:6)(cid:4)

(cid:9)(cid:11)(cid:5)(cid:13)(cid:12)

(cid:18)(cid:2)(cid:0)

(cid:18)(cid:1)(cid:0)

(cid:22) 2

(cid:21)(cid:22)

2

1 (cid:12)

(cid:18)(cid:1)(cid:0)

2

for (cid:23)

3.

Therefore, the probability that either of properties 1 or 2 fails to hold is at most

1 (cid:12)

(cid:18)(cid:2)(cid:0)

2

1

If this quantity is strictly less than 1, then there must exist at least one matrix (cid:3)
and 2 hold. This will be the case if and only if

for which both properties 1

2

ln (cid:6) 1

(cid:0)(cid:5)(cid:1)

ln (cid:6)

1 (cid:12)

(cid:6) 14 (cid:12)

Therefore, to complete the proof, we need only prove Eq. (14) by lower bounding (cid:16)

.

We have that

Pr (cid:6)

Pr (cid:6)

(cid:4)(cid:11)(cid:12)

(cid:4)(cid:11)(cid:12)

1

1

exp

exp

1

1

(cid:2)(cid:27)

(cid:2)(cid:27)

1 (cid:7)

1 (cid:4)

(cid:2)(cid:27)

(cid:3) RE

1 (cid:4)

(cid:3) RE

2

The second inequality follows from Cover and Thomas [8, Theorem 12.1.4].

By straightforward algebra,

(cid:3) RE

2

(cid:6) RE

2 ln

(cid:3) RE

1

1

(cid:2)(cid:27)

2

RE

(cid:2)(cid:27)

2

2

for (cid:23)

suf(cid:2)ciently large, where (cid:5)

is the constant

Thus,

and therefore, Eq. (14) holds if

2 ln

1
1

2

2

(cid:18)(cid:2)(cid:6)

exp

1

(cid:3) RE

(cid:3) RE

ln (cid:0)

ln (cid:0)

2

1 (cid:12)

ln (cid:6) 1

(cid:0)(cid:5)(cid:1)

ln (cid:6)

1 (cid:12)(cid:10)(cid:12)

By our choice of (cid:23)
hand side is ln (cid:0)

, we have that the left hand side of this inequality is at most ln (cid:0)
(cid:6) 4

. Therefore, the inequality holds for (cid:0)

5 ln ln (cid:0)
suf(cid:2)ciently large.

(cid:12) ln ln (cid:0)

(cid:6) 1 (cid:12)

, and the right

15

(cid:14)
(cid:3)
(cid:0)
(cid:9)
(cid:0)
(cid:14)
(cid:6)
(cid:16)
(cid:0)
6
+
(cid:23)
(cid:14)
(cid:22)
(cid:5)
(cid:20)
(cid:14)
(cid:3)
(cid:0)
(cid:25)
+
(cid:2)
(cid:14)
(cid:25)
(cid:23)
(cid:2)
(cid:14)
(cid:5)
+
(cid:6)
(cid:23)
(cid:25)
(cid:2)
(cid:14)
(cid:22)
(cid:5)
(cid:6)
(cid:6)
(cid:23)
(cid:25)
(cid:2)
(cid:14)
(cid:22)
(cid:5)
(cid:25)
(cid:27)
(cid:0)
(cid:5)
(cid:1)
(cid:20)
(cid:16)
(cid:3)
(cid:23)
(cid:0)
(cid:11)
(cid:23)
6
(cid:12)
(cid:25)
(cid:23)
(cid:25)
(cid:13)
(cid:20)
(cid:16)
(cid:8)
(cid:12)
(cid:6)
(cid:3)
(cid:23)
+
(cid:23)
(cid:0)
(cid:6)
(cid:12)
(cid:6)
(cid:3)
(cid:23)
(cid:8)
(cid:3)
(cid:23)
(cid:0)
(cid:7)
(cid:6)
(cid:23)
(cid:25)
(cid:11)
(cid:27)
(cid:23)
(cid:11)
(cid:3)
(cid:23)
(cid:0)
6
(cid:23)
(cid:12)
(cid:0)
(cid:25)
(cid:2)
(cid:13)
(cid:13)
(cid:6)
(cid:23)
(cid:25)
(cid:11)
(cid:27)
(cid:23)
(cid:11)
(cid:0)
(cid:27)
6
(cid:23)
(cid:12)
(cid:0)
(cid:25)
(cid:2)
(cid:13)
(cid:13)
(cid:20)
(cid:23)
(cid:11)
(cid:0)
(cid:27)
6
(cid:23)
(cid:12)
(cid:0)
(cid:25)
(cid:2)
(cid:13)
(cid:8)
(cid:23)
(cid:3)
(cid:11)
(cid:0)
(cid:12)
(cid:0)
(cid:25)
(cid:2)
(cid:13)
(cid:27)
(cid:11)
(cid:0)
(cid:12)
(cid:0)
(cid:27)
6
(cid:23)
(cid:13)
(cid:12)
(cid:25)
(cid:17)
(cid:27)
(cid:0)
(cid:25)
6
(cid:23)
(cid:27)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:25)
(cid:2)
(cid:0)
6
(cid:23)
(cid:18)
+
(cid:23)
(cid:11)
(cid:0)
(cid:12)
(cid:0)
(cid:25)
(cid:2)
(cid:13)
(cid:25)
(cid:5)
(cid:5)
(cid:8)
(cid:17)
(cid:27)
(cid:0)
6
(cid:27)
(cid:0)
(cid:27)
(cid:2)
(cid:3)
(cid:0)
(cid:25)
(cid:2)
(cid:0)
6
(cid:18)
(cid:20)
(cid:16)
(cid:6)
(cid:2)
(cid:23)
(cid:25)
(cid:11)
(cid:27)
(cid:23)
(cid:11)
(cid:0)
(cid:12)
(cid:0)
(cid:25)
(cid:2)
(cid:13)
(cid:13)
(cid:23)
(cid:11)
(cid:0)
(cid:12)
(cid:0)
(cid:25)
(cid:2)
(cid:13)
(cid:10)
(cid:27)
(cid:5)
(cid:27)
(cid:23)
(cid:6)
(cid:23)
(cid:25)
(cid:6)
(cid:23)
6
(cid:12)
(cid:25)
(cid:23)
(cid:25)
(cid:1)
(cid:20)
(cid:27)
(cid:27)
(cid:25)
(cid:4)


<!-- pdf-page: 16 -->
Acknowledgments

We are especially grateful to Neal Young for many helpful discussions, and for bringing much of the relevant
literature to our attention. Dean Foster and Rakesh Vohra also helped us to locate relevant literature. Thanks
(cid:2)nally to Colin Mallows and Joel Spencer for their help in proving Lemma 12.

References

[1] Dana Angluin and Leslie G. Valiant. Fast probabilistic algorithms for Hamiltonian circuits and

matchings. Journal of Computer and System Sciences, 18(2):155(cid:150)193, April 1979.

[2] Peter Auer, Nicol(cid:30)o Cesa›Bianchi, Yoav Freund, and Robert E. Schapire. Gambling in a rigged casino:
The adversarial multi›armed bandit problem. In 36th Annual Symposium on Foundations of Computer
Science, pages 322(cid:150)331, 1995.

[3] David Blackwell. An analog of the minimax theorem for vector payoffs. Paciﬁc Journal of Mathematics,

6(1):1(cid:150)8, Spring 1956.

[4] David Blackwell and M.A. Girshick. Theory of games and statistical decisions. dover, 1954.

[5] Nicol(cid:30)o Cesa›Bianchi, Yoav Freund, David Haussler, David P. Helmbold, Robert E. Schapire, and
Manfred K. Warmuth. How to use expert advice. Journal of the Association for Computing Machinery,
44(3):427(cid:150)485, May 1997.

[6] T. M. Cover and E. Ordentlich. Universal portfolios with side information. IEEE Transactions on

Information Theory, March 1996.

[7] Thomas M. Cover. Universal portfolios. Mathematical Finance, 1(1):1(cid:150)29, January 1991.

[8] Thomas M. Cover and Joy A. Thomas. Elements of Information Theory. Wiley, 1991.

[9] A. P. Dawid. Statistical theory: The prequential approach. Journal of the Royal Statistical Society,

Series A, 147:278(cid:150)292, 1984.

[10] M. Feder, N. Merhav, and M. Gutman. Universal prediction of individual sequences. IEEE Transactions

on Information Theory, 38:1258(cid:150)1270, 1992.

[11] Thomas S. Ferguson. Mathematical Statistics: A Decision Theoretic Approach. Academic Press,

1967.

[12] Dean P. Foster. Prediction in the worst case. The Annals of Statistics, 19(2):1084(cid:150)1090, 1991.

[13] Dean P. Foster and Rakesh Vohra. Regret in the on›line decision problem. unpublished manuscript,

1997.

[14] Dean P. Foster and Rakesh V. Vohra. A randomization rule for selecting forecasts. Operations Research,

41(4):704(cid:150)709, July(cid:150)August 1993.

[15] Dean P. Foster and Rakesh V. Vohra. Asymptotic calibration. Biometrika, 85(2):379(cid:150)390, 1998.

[16] Yoav Freund and Robert E. Schapire. Game theory, on›line prediction and boosting. In Proceedings

of the Ninth Annual Conference on Computational Learning Theory, pages 325(cid:150)332, 1996.

16



<!-- pdf-page: 17 -->
[17] Drew Fudenberg and David K. Levine. Consistency and cautious (cid:2)ctitious play. Journal of Economic

Dynamics and Control, 19:1065(cid:150)1089, 1995.

[18] Michael D. Grigoriadis and Leonid G. Khachiyan. Approximate solution of matrix games in parallel.

Technical Report 91›73, DIMACS, July 1991.

[19] Michael D. Grigoriadis and Leonid G. Khachiyan. A sublinear›time randomized approximation

algorithm for matrix games. Operations Research Letters, 18(2):53(cid:150)58, Sep 1995.

[20] James Hannan. Approximation to Bayes risk in repeated play.

In M. Dresher, A. W. Tucker, and
P. Wolfe, editors, Contributions to the Theory of Games, volume III, pages 97(cid:150)139. Princeton University
Press, 1957.

[21] David P. Helmbold, Robert E. Schapire, Yoram Singer, and Manfred K. Warmuth. On›line portfolio

selection using multiplicative updates. Mathematical Finance, 8(4):325(cid:150)347, 1998.

[22] Wassily Hoeffding. Probability inequalities for sums of bounded random variables. Journal of the

American Statistical Association, 58(301):13(cid:150)30, March 1963.

[23] Jyrki Kivinen and Manfred K. Warmuth. Additive versus exponentiated gradient updates for linear

prediction. Information and Computation, 132(1):1(cid:150)64, January 1997.

[24] Philip Klein and Neal Young. On the number of iterations for Dantzig›Wolfe optimization and
packing›covering approximation algorithms. In Proceedings of the Seventh Conference on Integer
Programming and Combinatorial Optimization, 1999.

[25] Nick Littlestone and Manfred K. Warmuth. The weighted majority algorithm.

Information and

Computation, 108:212(cid:150)261, 1994.

[26] Guillermo Owen. Game Theory. Academic Press, second edition, 1982.

[27] Serge A. Plotkin, David B. Shmoys, and ·Eva Tardos. Fast approximation algorithms for fractional
packing and covering problems. Mathematics of Operations Research, 20(2):257(cid:150)301, May 1995.

[28] Y. M. Shtar‘kov. Universal sequential coding of single messages. Problems of information Transmission

(translated from Russian), 23:175(cid:150)186, July›September 1987.

[29] V. G. Vovk. A game of prediction with expert advice. Journal of Computer and System Sciences,

56(2):153(cid:150)173, April 1998.

[30] Volodimir G. Vovk. Aggregating strategies. In Proceedings of the Third Annual Workshop on Compu-

tational Learning Theory, pages 371(cid:150)383, 1990.

[31] Neal Young. Randomized rounding without solving the linear program. In Proceedings of the Sixth

Annual ACM-SIAM Symposium on Discrete Algorithms, pages 170(cid:150)178, 1995.

[32] Jacob Ziv. Coding theorems for individual sequences. IEEE Transactions on Information Theory,

24(4):405(cid:150)412, July 1978.

17



<!-- pdf-page: 18 -->
A Proof of Lemma 12

Let

Our goal is to derive a lower bound on Pr [ (cid:8)
and Var (cid:8)

(cid:8)(cid:1)(cid:0) . In addition, by Hoeffding’s inequality [22], it can be shown that, for all (cid:2)

1 (cid:3)

(cid:7)(cid:6)

2

1 (cid:3)

0]. Let (cid:0)

(cid:6)(cid:13)(cid:6) 1

(cid:7)(cid:6)

(cid:12) . It can be easily veri(cid:2)ed that E (cid:8)

0

(cid:3) 0,

(cid:6) 15 (cid:12)

Pr [ (cid:8)

(cid:2) ]

Pr [ (cid:8)

(cid:2) ]

2

2 (cid:2)

2

2 (cid:2)

(cid:4) ]. Throughout this proof, we use

and

For (cid:4)

(cid:12)(cid:19)(cid:8) Pr [ (cid:8)
, let (cid:4)
set of (cid:4) ’s which includes all (cid:4)
analogously.

for which (cid:4)

0. Restricted summations (such as

to denote summation over a (cid:2)nite
(cid:5) 0) are de(cid:2)ned

Let (cid:6)(cid:13)(cid:3) 0 be any number. We de(cid:2)ne the following quantities:

0 (cid:8)

(cid:8)(cid:10)(cid:9)

(cid:4)(cid:13)(cid:4)

(cid:8) 0

(cid:9)(cid:12)(cid:8)

(cid:4)(cid:10)(cid:4)

2

2

(cid:12)(cid:12)(cid:20)

1

2

3

We prove the lemma by deriving a lower bound on (cid:7)

Pr [ (cid:8)

0].

The expected value of (cid:8)

is:

0 (cid:8) E (cid:8)

(cid:4)(cid:10)(cid:4)

Thus,

Next, we have that

(cid:8) Var (cid:8)

(cid:4)(cid:10)(cid:4)

(cid:4)(cid:10)(cid:4)

(cid:4)(cid:10)(cid:4)

(cid:4)(cid:10)(cid:4)

0

(cid:9)(cid:12)(cid:8)

1 (cid:20)

(cid:8) 0

0 (cid:8)

(cid:8)(cid:10)(cid:9)

(cid:16)(cid:6)

1 (cid:20)

(cid:6) 16 (cid:12)

2

2

2

2

2

(cid:9)(cid:12)(cid:8)

(cid:8) 0

0 (cid:8)

(cid:8)(cid:10)(cid:9)

2

2 (cid:7)

3 (cid:20)

18

(cid:8)
(cid:8)
(cid:4)
(cid:14)
(cid:16)
(cid:7)
(cid:16)
(cid:1)
(cid:16)
(cid:27)
(cid:4)
(cid:4)
(cid:14)
(cid:16)
(cid:7)
(cid:16)
(cid:20)
(cid:6)
(cid:8)
(cid:27)
(cid:8)
(cid:6)
+
(cid:2)
(cid:18)
+
(cid:27)
+
(cid:2)
(cid:18)
(cid:20)
(cid:22)
(cid:3)
(cid:6)
(cid:4)
(cid:8)
(cid:4)
(cid:2)
(cid:6)
(cid:4)
(cid:12)
(cid:3)
(cid:4)
(cid:2)
(cid:7)
(cid:8)
(cid:15)
(cid:2)
(cid:4)
(cid:6)
(cid:4)
(cid:12)
(cid:11)
(cid:8)
(cid:27)
(cid:15)
(cid:18)
(cid:2)
(cid:6)
(cid:4)
(cid:12)
(cid:14)
(cid:8)
(cid:15)
(cid:2)
(cid:15)
(cid:9)
(cid:6)
(cid:4)
(cid:12)
(cid:14)
(cid:8)
(cid:15)
(cid:2)
(cid:0)
(cid:18)
(cid:9)
(cid:4)
(cid:4)
(cid:6)
(cid:4)
(cid:12)
(cid:14)
(cid:8)
(cid:15)
(cid:2)
(cid:15)
(cid:9)
(cid:4)
(cid:4)
(cid:6)
(cid:4)
+
(cid:6)
(cid:8)
(cid:15)
(cid:2)
(cid:6)
(cid:4)
(cid:12)
(cid:8)
(cid:15)
(cid:2)
(cid:0)
(cid:18)
(cid:9)
(cid:6)
(cid:4)
(cid:12)
(cid:25)
(cid:15)
(cid:18)
(cid:2)
(cid:6)
(cid:4)
(cid:12)
(cid:25)
(cid:15)
(cid:2)
(cid:6)
(cid:4)
(cid:12)
(cid:25)
(cid:15)
(cid:2)
(cid:15)
(cid:9)
(cid:6)
(cid:4)
(cid:12)
+
(cid:27)
(cid:11)
(cid:25)
(cid:6)
(cid:7)
(cid:25)
(cid:14)
(cid:11)
+
(cid:7)
(cid:25)
(cid:14)
(cid:0)
(cid:8)
(cid:15)
(cid:2)
(cid:4)
(cid:4)
(cid:6)
(cid:4)
(cid:12)
(cid:8)
(cid:15)
(cid:2)
(cid:0)
(cid:18)
(cid:9)
(cid:4)
(cid:4)
(cid:6)
(cid:4)
(cid:12)
(cid:25)
(cid:15)
(cid:18)
(cid:2)
(cid:4)
(cid:4)
(cid:6)
(cid:4)
(cid:12)
(cid:25)
(cid:15)
(cid:2)
(cid:4)
(cid:4)
(cid:6)
(cid:4)
(cid:12)
(cid:25)
(cid:15)
(cid:2)
(cid:15)
(cid:9)
(cid:4)
(cid:4)
(cid:6)
(cid:4)
(cid:12)
+
(cid:14)
(cid:25)
(cid:6)
(cid:11)
(cid:25)
(cid:6)
(cid:25)
(cid:14)


<!-- pdf-page: 19 -->
Combined with Eq. (16), it follows that

(cid:1)+

2 (cid:7)

2 (cid:6)

1

2

3 (cid:20)

(cid:6) 17 (cid:12)

We next upper bound (cid:14)

1, (cid:14)

2 and (cid:14)

3. This will allow us to immediately lower bound (cid:7)

using Eq. (17).

To bound (cid:14)

1, note that

1 (cid:8)(cid:1)(cid:6)

(cid:1)(cid:0)

(cid:2)(cid:0)

(cid:3)(cid:0)

,+

2

(cid:4)(cid:10)(cid:4)

(cid:12)(cid:19)(cid:8)

3 (cid:20)

(cid:6) 18 (cid:12)

To bound (cid:14)

(cid:4)(cid:0)

3, let (cid:6)(cid:14)(cid:8)

0 (cid:10)

1 (cid:10)

(cid:19) be a sequence of numbers such that if (cid:4)

(cid:3) 0 and (cid:4)

(cid:5)(cid:0)

then (cid:4)
Let

(cid:12)(cid:19)(cid:8)

(cid:7)(cid:6)

for some (cid:4) . In other words, every (cid:4)
(cid:12) . By Eq. (15),

,+

(cid:5)(cid:0)

3 (cid:8)

2

2

0

2
0

2
0

2

0

(cid:5)(cid:0)

0 (cid:12)

2

2 (cid:9)

To bound the summation, note that

2

2

(cid:5)(cid:0)

(cid:5)(cid:0)

(cid:6) with positive probability is represented by some
for

(cid:3) 0. We can compute (cid:14)

3 as follows:

.

1

0

(cid:5)(cid:0)

(cid:10)(cid:0)

(cid:11)(cid:0)

(cid:13)(cid:12)

2

1

2

1

(cid:5)(cid:0)

(cid:10)(cid:0)

(cid:5)(cid:0)

1

2

1

2

0
1

0

(cid:5)(cid:0)

(cid:10)(cid:0)

2

1

(cid:15)(cid:19)(cid:16)

2

2

1 (cid:12)

1

(cid:15)(cid:17)(cid:16)

2

(cid:15)(cid:17)(cid:16)

(cid:15)(cid:19)(cid:16)

(cid:5)(cid:0)

(cid:10)(cid:0)

2

1

2

2

2

1

1

0

(cid:15)(cid:19)(cid:16)

1

1

1

0
1

0

2 (cid:4)

2

2
0

0

1
2 (cid:6)

2 (cid:4)

2

2

1

2

2

2 (cid:4)

(cid:2)(cid:21)(cid:18)

2

2

,+

2(cid:18)

2

2

2 (cid:9)

1
2 (cid:2)

Thus, (cid:14)

3

2

1

2 (cid:12)

2

2 (cid:9)

. A bound on (cid:14)

2 follows by symmetry.

Combining with Eqs. (17) and (18), we have

(cid:1)+

2 (cid:7)

2 (cid:6)

2

3 (cid:6)

1

2 (cid:12)

2

2 (cid:9)

and so

Since this holds for all (cid:6)

, we have that Pr [ (cid:8)

0]

((cid:27)

Pr [ (cid:8)

0]

2

2 (cid:9)

2 (cid:12)

1
2

2

3 (cid:6)

2 (cid:6)
(cid:0)(cid:2)(cid:1) where

(cid:0)(cid:9)(cid:1)

sup
(cid:5) 0

2

3 (cid:6)

2 (cid:12)

1
2

2 (cid:6)

2

2 (cid:9)

(cid:6)(cid:13)(cid:6) 1

(cid:12) . This number is clearly positive since the numerator of the inside expression can be made
and (cid:0)
positive by choosing (cid:6) suf(cid:2)ciently large. (For instance, it can be shown that this expression is positive when
we set (cid:6)(cid:17)(cid:8)

(cid:0) .)

1

19

(cid:0)
(cid:25)
(cid:6)
(cid:14)
(cid:25)
(cid:14)
(cid:25)
(cid:14)
(cid:6)
(cid:14)
(cid:15)
(cid:2)
(cid:15)
(cid:9)
(cid:6)
(cid:4)
(cid:12)
(cid:15)
(cid:2)
(cid:15)
(cid:9)
(cid:4)
(cid:4)
(cid:6)
(cid:4)
(cid:14)
(cid:3)
(cid:3)
(cid:3)
(cid:10)
(cid:6)
(cid:4)
(cid:12)
(cid:6)
(cid:6)
(cid:8)
(cid:16)
(cid:6)
(cid:0)
(cid:16)
(cid:1)
(cid:6)
(cid:4)
(cid:2)
(cid:15)
(cid:4)
(cid:6)
(cid:4)
(cid:1)
(cid:6)
(cid:12)
(cid:2)
(cid:18)
(cid:6)
(cid:0)
(cid:14)
(cid:15)
(cid:2)
(cid:15)
(cid:9)
(cid:4)
(cid:4)
(cid:6)
(cid:4)
(cid:12)
(cid:8)
(cid:19)
(cid:15)
(cid:16)
(cid:7)
(cid:0)
(cid:16)
(cid:4)
(cid:6)
(cid:16)
(cid:12)
(cid:8)
(cid:0)
(cid:19)
(cid:15)
(cid:13)
(cid:7)
(cid:4)
(cid:6)
(cid:13)
(cid:12)
(cid:25)
(cid:19)
(cid:18)
(cid:15)
(cid:16)
(cid:7)
(cid:8)
(cid:9)
(cid:6)
(cid:16)
(cid:29)
(cid:27)
(cid:16)
(cid:12)
(cid:19)
(cid:15)
(cid:13)
(cid:7)
(cid:16)
(cid:29)
(cid:4)
(cid:6)
(cid:13)
(cid:12)
(cid:14)
(cid:8)
(cid:0)
(cid:1)
(cid:6)
(cid:25)
(cid:19)
(cid:18)
(cid:15)
(cid:16)
(cid:7)
(cid:6)
(cid:16)
(cid:29)
(cid:27)
(cid:16)
(cid:12)
(cid:1)
(cid:6)
(cid:16)
(cid:29)
+
(cid:6)
(cid:2)
(cid:18)
(cid:25)
(cid:19)
(cid:18)
(cid:15)
(cid:16)
(cid:7)
(cid:6)
(cid:16)
(cid:29)
(cid:27)
(cid:16)
(cid:12)
(cid:2)
(cid:18)
(cid:6)
(cid:20)
(cid:19)
(cid:18)
(cid:15)
(cid:16)
(cid:7)
(cid:6)
(cid:16)
(cid:29)
(cid:27)
(cid:16)
(cid:12)
(cid:2)
(cid:18)
(cid:6)
(cid:8)
(cid:19)
(cid:18)
(cid:15)
(cid:16)
(cid:7)
(cid:18)
(cid:6)
(cid:6)
(cid:15)
(cid:2)
(cid:18)
(cid:6)
(cid:6)
(cid:4)
+
(cid:19)
(cid:18)
(cid:15)
(cid:16)
(cid:7)
(cid:18)
(cid:6)
(cid:6)
(cid:15)
(cid:2)
(cid:6)
(cid:4)
(cid:8)
(cid:18)
(cid:6)
(cid:18)
(cid:6)
(cid:2)
(cid:18)
(cid:2)
(cid:6)
(cid:4)
(cid:8)
(cid:2)
(cid:18)
(cid:6)
(cid:27)
(cid:2)
(cid:18)
(cid:6)
(cid:12)
(cid:18)
(cid:20)
+
(cid:6)
(cid:6)
(cid:25)
6
(cid:2)
(cid:18)
(cid:0)
(cid:25)
(cid:6)
(cid:25)
6
(cid:2)
(cid:18)
(cid:6)
(cid:6)
(cid:7)
(cid:6)
(cid:0)
(cid:27)
(cid:6)
(cid:25)
6
(cid:2)
(cid:18)
(cid:20)
(cid:6)
(cid:6)
(cid:8)
(cid:9)
(cid:0)
(cid:6)
(cid:25)
6
(cid:2)
(cid:18)
(cid:8)
(cid:27)
(cid:6)
(cid:13)
6

