<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: 01f49de027c4c2c146869da85f8e8482d6b723344cb80ce957d11e93c615e7cc -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
Journal of Computer and System Sciences (cid:21) SS1504

journal of computer and system sciences 55, 119(cid:21)139 (1997)
article no. SS971504

A Decision-Theoretic Generalization of On-Line Learning
and an Application to Boosting*

Yoav Freund and Robert E. Schapire-

AT6T Labs, 180 Park Avenue, Florham Park, New Jersey 07932

Received December 19, 1996

In the first part of the paper we consider the problem of dynamically
apportioning resources among a set of options in a worst-case on-line
framework. The model we study can be interpreted as a broad, abstract
extension of the well-studied on-line prediction model to a general
decision-theoretic setting. We show that the multiplicative weight-
update Littlestone(cid:21)Warmuth rule can be adapted to this model, yielding
bounds that are slightly weaker in some cases, but applicable to a con-
siderably more general class of learning problems. We show how the
resulting learning algorithm can be applied to a variety of problems,
including gambling, multiple-outcome prediction, repeated games, and
prediction of points in Rn. In the second part of the paper we apply the
multiplicative weight-update technique to derive a new boosting algo-
rithm. This boosting algorithm does not require any prior knowledge
about the performance of the weak learning algorithm. We also study
generalizations of the new boosting algorithm to the problem of
learning functions whose range, rather than being binary, is an arbitrary
finite set or a bounded segment of the real line. ] 1997 Academic Press

1. INTRODUCTION

A gambler, frustrated by persistent horse-racing losses
and envious of his friends’ winnings, decides to allow a
group of his fellow gamblers to make bets on his behalf. He
decides he will wager a fixed sum of money in every race, but
that he will apportion his money among his friends based on
how well they are doing. Certainly, if he knew psychically
ahead of time which of his friends would win the most, he
would naturally have that friend handle all his wagers.
Lacking such clairvoyance, however, he attempts to allocate
each race’s wager in such a way that his total winnings for
the season will be reasonably close to what he would have
won had he bet everything with the luckiest of his friends.

In this paper, we describe a simple algorithm for solving
such dynamic allocation problems, and we show that our
solution can be applied to a great assortment of learning
problems. Perhaps the most surprising of these applications
is the derivation of a new algorithm for ‘‘boosting,’’ i.e., for

converting a ‘‘weak’’ PAC learning algorithm that performs
just slightly better than random guessing into one with
arbitrarily high accuracy.

We formalize our on-line allocation model as follows. The
allocation agent A has N options or strategies to choose
from; we number these using the integers 1, ..., N. At each
time step t=1, 2, ..., T, the allocator A decides on a distribu-
tion pt over the strategies; that is p t
i (cid:30)0 is the amount
allocated to strategy i, and (cid:29) N
i =1. Each strategy i then
suffers some loss l t
i which is determined by the (possibly
adversarial) ‘‘environment.’’ The loss suffered by A is then
(cid:29) n
i =pt } l t, i.e., the average loss of the strategies with
respect to A’s chosen allocation rule. We call this loss func-
tion the mixture loss.

i=1 p t

i=1 p t

i l t

In this paper, we always assume that the loss suffered by
any strategy is bounded so that, without loss of generality,
l t
i # [0, 1]. Besides this condition, we make no assumptions
about the form of the loss vectors lt, or about the manner
in which they are generated; indeed, the adversary’s choice
for lt may even depend on the allocator’s chosen mixture pt.
The goal of the algorithm A is to minimize its cumulative
loss relative to the loss suffered by the best strategy. That is,
A attempts to minimize its net loss

where

LA&min

i

Li

T
LA= :
t=1

pt } l t

is the total cumulative loss suffered by algorithm A on the
first T trials, and

T
Li= :
t=1

l t
i

* An extended abstract of this work appeared in the ‘‘Proceedings of
the Second European Conference on Computational Learning Theory,
Barcelona, March, 1995.’’

- E-mail: [yoav, schapire](cid:20)research.att.com.

is strategy i’s cumulative loss.

In Section 2, we show that Littlestone and Warmuth’s
[20] ‘‘weighted majority’’ algorithm can be generalized to

119

0022-0000(cid:18)97 (cid:30)25.00
Copyright (cid:23) 1997 by Academic Press
All rights of reproduction in any form reserved.

File: 571J 150401 . By:CV . Date:28:07:01 . Time:05:54 LOP8M. V8.0. Page 01:01
Codes: 6428 Signs: 4372 . Length: 60 pic 11 pts, 257 mm



<!-- pdf-page: 2 -->
120

FREUND AND SCHAPIRE

handle this problem, and we prove a number of bounds on
the net loss. For instance, one of our results shows that the
net loss of our algorithm can be bounded by O(- T ln N)
or, put another way, that the average per trial net loss is
decreasing at the rate O(- (ln N)(cid:18)T). Thus, as T increases,
this difference decreases to zero.

Our results for the on-line allocation model can be
learning problems, as we
applied to a wide variety of
describe in Section 3. In particular, we generalize the results
of Littlestone and Warmuth [20] and Cesa-Bianchi et al.
[4] for the problem of predicting a binary sequence using
the advice of a team of ‘‘experts.’’ Whereas these authors
proved worst-case bounds for making on-line randomized
decisions over a binary decision and outcome space with
a [0, 1]-valued discrete loss, we prove (slightly weaker)
bounds that are applicable to any bounded loss function
over any decision and outcome spaces. Our bounds express
explicitly the rate at which the loss of the learning algorithm
approaches that of the best expert.

Related generalizations of the expert prediction model
were studied by Vovk [25], Kivinen and Warmuth [19],
and Haussler et al. [15]. Like us, these authors focused
primarily on multiplicative weight-update algorithms. Chung
[5] also presented a generalization, giving the problem a
game-theoretic treatment.

Boosting

Returning to the horse-racing story, suppose now that the
gambler grows weary of choosing among the experts and
instead wishes to create a computer program that will
accurately predict the winner of a horse race based on the
usual information (number of races recently won by each
horse, betting odds for each horse, etc.). To create such a
program, he asks his favorite expert to explain his betting
strategy. Not surprisingly, the expert is unable to articulate
a grand set of rules for selecting a horse. On the other hand,
when presented with the data for a specific set of races, the
expert has no trouble coming up with a ‘‘rule-of-thumb’’ for
that set of races (such as, ‘‘Bet on the horse that has recently
won the most races’’ or ‘‘Bet on the horse with the most
favored odds’’). Although such a rule-of-thumb, by itself, is
obviously very rough and inaccurate, it is not unreasonable
to expect it to provide predictions that are at least a little bit
better than random guessing. Furthermore, by repeatedly
asking the expert’s opinion on different collections of races,
the gambler is able to extract many rules-of-thumb.

In order to use these rules-of-thumb to maximum advan-
tage, there are two problems faced by the gambler: First,
how should he choose the collections of races presented to
the expert so as to extract rules-of-thumb from the expert
that will be the most useful? Second, once he has collected
many rules-of-thumb, how can they be combined into a
single, highly accurate prediction rule?

Boosting refers to this general problem of producing a
very accurate prediction rule by combining rough and
moderately inaccurate rules-of-thumb. In the second part of
the paper, we present and analyze a new boosting algorithm
inspired by the methods we used for solving the on-line
allocation problem.

Formally, boosting proceeds as follows: The booster is
provided with a set of labelled training examples (x 1 , y 1),
..., (xN , yN), where yi is the label associated with instance xi ;
for instance, in the horse-racing example, xi might be the
observable data associated with a particular horse race, and
yi the outcome (winning horse) of that race. On each round
t=1, ..., T, the booster devises a distribution Dt over the set
of examples, and requests (from an unspecified oracle) a
weak hypothesis (or rule-of-thumb) ht with low error =t with
respect to Dt (that is, =t=PritDt[ht(xi){ yi]). Thus, dis-
tribution Dt specifies the relative importance of each example
for the current round. After T rounds, the booster must
combine the weak hypotheses into a single prediction rule.

Unlike the previous boosting algorithms of Freund
[10, 11] and Schapire [22], the new algorithm needs no
prior knowledge of the accuracies of the weak hypotheses.
Rather,
it adapts to these accuracies and generates a
weighted majority hypothesis in which the weight of each
weak hypothesis is a function of its accuracy. For binary
prediction problems, we prove in Section 4 that the error
of this final hypothesis (with respect to the given set of
examples) is bounded by exp( &2 (cid:29) T
t ) where =t=
1(cid:18)2&#t is the error of the tth weak hypothesis. Since a
hypothesis that makes entirely random guesses has error
1(cid:18)2, #t measures the accuracy of the t th weak hypothesis
relative to random guessing. Thus, this bound shows that if
we can consistently find weak hypotheses that are slightly
better than random guessing, then the error of the final
hypothesis drops exponentially fast.

t=1 # 2

Note that

the bound on the accuracy of the final
hypothesis improves when any of the weak hypotheses is
improved. This is in contrast with previous boosting algo-
rithms whose performance bound depended only on the
accuracy of the least accurate weak hypothesis. At the same
time, if the weak hypotheses all have the same accuracy, the
performance of the new algorithm is very close to that
achieved by the best of the known boosting algorithms.

In Section 5, we give two extensions of our boosting algo-
rithm to multi-class prediction problems in which each
example belongs to one of several possible classes (rather than
just two). We also give an extension to regression problems in
which the goal is to estimate a real-valued function.

2. THE ON-LINE ALLOCATION ALGORITHM
AND ITS ANALYSIS

In this

section, we present our algorithm, called
Hedge( ;), for the on-line allocation problem. The algorithm

File: 571J 150402 . By:CV . Date:28:07:01 . Time:05:54 LOP8M. V8.0. Page 01:01
Codes: 6472 Signs: 5755 . Length: 56 pic 0 pts, 236 mm



<!-- pdf-page: 3 -->
A DECISION THEORETIC GENERALIZATION

121

and its analysis are direct generalizations of Littlestone and
Warmuth’s weighted majority algorithm [20].

i=1 w 1

1 , ..., w t

The pseudo-code for Hedge( ;) is shown in Fig. 1. The
algorithm maintains a weight vector whose value at time t
is denoted wt=( w t
N). At all times, all weights will
be nonnegative. All of the weights of the initial weight
vector w1 must be nonnegative and sum to one, so that
(cid:29)N
i =1. Besides these conditions, the initial weight vec-
tor may be arbitrary, and may be viewed as a ‘‘prior’’ over
the set of strategies. Since our bounds are strongest for those
strategies receiving the greatest initial weight, we will want
to choose the initial weights so as to give the most weight to
those strategies which we expect are most likely to perform
the best. Naturally, if we have no reason to favor any of the
strategies, we can set all of the initial weights equally so that
w1
i =1(cid:18)N. Note that the weights on future trials need not
sum to one.

Algorithm Hedge(;)
Parameters: ; # [0, 1]

initial weight vector w1 # [0, 1]N with (cid:29) N
number of trials T
Do for t=1, 2, ..., T

i=1 w1

i =1

1. Choose allocation

pt=

wt
i=1 w t

i

(cid:29) N

2. Receive loss vector lt # [0, 1]N from environment.
3. Suffer loss pt } l t.

4. Set the new weights vector to be

w t+1

i =w t

i ; li

t

FIG. 1. The on-line allocation algorithm.

Our algorithm allocates among the strategies using the
current weight vector, after normalizing. That is, at time t,
Hedge( ;) chooses the distribution vector

Proof. By a convexity argument, it can be shown that

:r(cid:29)1&(1&:) r

(3)

pt=

wt
i=1 w t

i

(cid:29) N

.

(1)

for :(cid:30)0 and r # [0, 1]. Combined with Eqs. (1) and (2),
this implies

After the loss vector lt has been received, the weight

vector wt is updated using the multiplicative rule

N
:
i=1

w t+1

N
i = :
i=1

t

w t

i ; li

wt+1

i =w t

i } ; l i

t

.

(2)

N
(cid:29) :
i=1

w t

i(1&(1&;) l t
i)

N

=\ :

i=1

w t

i+ (1&(1&;) pt } l t).

(4)

Applying repeatedly for t=1, ..., T yields

N
:
i=1

w T+1

T
i (cid:29) ‘
t=1

(1&(1&;) pt } lt)

(cid:29)exp \ &(1&;) :

t=1

T

p t } lt+

since 1+x(cid:29)ex for all x. The lemma follows imme-
diately. K

Thus,

L Hedge( ;)(cid:29)

Note that, from Eq. (2),

&ln((cid:29) N

i=1 w T+1
1&;

i

w T+1

i =w 1

T
i ‘
t=1

t

; li

=w 1

i ; Li.

)

.

(5)

(6)

This is all that is needed to complete our analysis.

More generally,
it can be shown that our analysis is
applicable with only minor modification to an alternative
update rule of the form

w t+1

i =wt

i } U;(l t
i )

where U; : [0, 1] (cid:20) [0, 1] is any function, parameterized
by ; # [0, 1] satisfying

;r(cid:29)U;(r)(cid:29)1&(1&;) r

for all r # [0, 1].

2.1. Analysis

The analysis of Hedge( ;) mimics directly that given by
Littlestone and Warmuth [20]. The main idea is to derive
upper and lower bounds on (cid:29) N
which, together,
imply an upper bound on the loss of the algorithm. We
begin with an upper bound.

i=1 w T+1

i

Lemma 1. For any sequence of loss vectors l1, ..., lT,

N

ln \ :

i=1

w T+1
i

+ (cid:29) &(1&;) L Hedge( ;) .

File: 571J 150403 . By:CV . Date:28:07:01 . Time:05:54 LOP8M. V8.0. Page 01:01
Codes: 4496 Signs: 2689 . Length: 56 pic 0 pts, 236 mm



<!-- pdf-page: 4 -->
122

FREUND AND SCHAPIRE

Theorem 2. For any sequence of loss vectors l1, ..., l T,

and for any i # [1, ..., N], we have

L Hedge( ;)(cid:29)

&ln(w 1

i )&Li ln ;
1&;

.

(7)

Theorem 3. Let B be an algorithm for the on-line alloca-
tion problem with an arbitrary number of strategies. Suppose
that there exists positive real numbers a and c such that for
any number of strategies N and for any sequence of loss
vectors l1, ..., lT

More generally, for any nonempty set S(cid:31)[1, ..., N], we have

LB(cid:29)c min

i

L i+a ln N.

L Hedge( ;)(cid:29)

&ln((cid:29) i # S w 1

i )&(ln ;) maxi # S Li

1&;

.

(8)

Then for all ; # (0, 1), either

Proof. We prove the more general statement (8) since

Eq. (7) follows in the special case that S=[i].

From Eq. (6),

N
:
i=1

w T+1

i (cid:30) :
i # S

w T+1
i

= :
i # S

w 1

i ;Li

(cid:30);maxi # S Li :
i # S

w 1
i .

The theorem now follows immediately from Eq. (5). K

The simpler bound (7) states that Hedge(;) does not
perform ‘‘too much worse’’ than the best strategy i for the
sequence. The difference in loss depends on our choice of ;
and on the initial weight w 1
i of each strategy. If each weight
is set equally so that w 1

i =1(cid:18)N, then this bound becomes

L Hedge( ;)(cid:29)

mini Li ln(1(cid:18);)+ln N
1&;

.

(9)

c(cid:30)

ln(1(cid:18);)
1&;

or

a(cid:30)

1
(1&;)

.

The proof is given in the appendix.

2.2. How to Choose ;

So far, we have analyzed Hedge( ;) for a given choice of
;, and we have proved reasonable bounds for any choice of
;. In practice, we will often want to choose ; so as to maxi-
mally exploit any prior knowledge we may have about the
specific problem at hand.

The following lemma will be helpful for choosing ; using

the bounds derived above.

Lemma 4. Suppose 0(cid:29)L(cid:29)L(cid:25) and 0<R(cid:29)R(cid:25) . Let ;=

g(L(cid:25) (cid:18)R(cid:25) ) where g(z)=1(cid:18)(1+- 2(cid:18)z). Then

&L ln ;+R
1&;

(cid:29)L+- 2L(cid:25) R(cid:25) +R.

Proof.

(Sketch) It can be shown that &ln ;(cid:29)(1&;2)(cid:18)
(2;) for ; # (0, 1]. Applying this approximation and the
given choice of ; yields the result.

K

Since it depends only logarithmically on N, this bound is
reasonable even for a very large number of strategies.

The more complicated bound (8) is a generalization of
the simpler bound that is especially applicable when the
number of strategies is infinite. Naturally, for uncountable
collections of strategies, the sum appearing in Eq. (8) can be
replaced by an integral, and the maximum by a supremum.

The bound given in Eq. (9) can be written as

Lemma 4 can be applied to any of the bounds above since
all of these bounds have the form given in the lemma. For
example, suppose we have N strategies, and we also know a
prior bound L(cid:25) on the loss of the best strategy. Then,
combining Eq. (9) and Lemma 4, we have

L Hedge( ;)(cid:29)min

i

Li+- 2L(cid:25)

ln N+ln N

(11)

L Hedge( ;)(cid:29)c min

i

Li+a ln N,

(10)

where c=ln(1(cid:18);)(cid:18)(1&;) and a=1(cid:18)(1&;). Vovk [24]
analyzes prediction algorithms that have performance
bounds of this form, and proves tight upper and lower
bounds for the achievable values of c and a. Using Vovk’s
results, we can show that the constants a and c achieved by
Hedge( ;) are optimal.

for ;= g(L(cid:25) (cid:18)ln N). In general, if we know ahead of time the
number of trials T, then we can use L(cid:25) =T as an upper
bound on the cumulative loss of each strategy i.

Dividing both sides of Eq. (11) by T, we obtain an explicit
bound on the rate at which the average per-trial loss of
Hedge( ;) approaches the average loss for the best strategy:

L Hedge( ;)
T

(cid:29)min

i

L i
T

+

ln N

- 2L(cid:25)
T

+

ln N
T

.

(12)

File: 571J 150404 . By:CV . Date:28:07:01 . Time:05:54 LOP8M. V8.0. Page 01:01
Codes: 4723 Signs: 3172 . Length: 56 pic 0 pts, 236 mm



<!-- pdf-page: 5 -->
A DECISION THEORETIC GENERALIZATION

123

Since L(cid:25) (cid:29)T, this gives a worst case rate of convergence of
O(- (ln N)(cid:18)T). However, if L(cid:25)
is close to zero, then the rate
of convergence will be much faster, roughly, O((ln N)(cid:18)T ).

Lemma 4 can also be applied to the other bounds given in

Theorem 2 to obtain analogous results.

The bound given in Eq. (11) can be improved in special
cases in which the loss is a function of a prediction and an
outcome and this function is of a special form (see Example 4
below). However, for the general case, one cannot improve
the square-root term - 2L(cid:25)
ln N, by more than a constant
factor. This is a corollary of the lower bound given by Cesa-
Bianchi et al. ([4], Theorem 7) who analyze an on-line
prediction problem that can be seen as a special case of the
on-line allocation model.

3. APPLICATIONS

The framework described up to this point is quite general
and can be applied in a wide variety of learning problems.
Consider the following set-up used by Chung [5]. We are
given a decision space 2, a space of outcomes 0, and a
bounded loss function * : 2_0 (cid:20) [0, 1]. (Actually, our
results require only that * be bounded, but, by rescaling, we
can assume that its range is [0, 1].) At every time step t, the
learning algorithm selects a decision $t # 2, receives an out-
come |t # 0, and suffers loss *($t, |t). More generally, we
may allow the learner to select a distribution Dt over the
space of decisions, in which case it suffers the expected loss
of a decision randomly selected according to Dt; that is, its
expected loss is 4(Dt, |t) where

4(D, |)=E$t D[*($, |)].

To decide on distribution Dt, we assume that the learner
has access to a set of N experts. At every time step t, expert
i produces its own distribution E t
i on 2, and suffers loss
4(E t

i , |t).

The goal of the learner is to combine the distributions
produced by the experts so as to suffer expected loss ‘‘not
much worse’’ than that of the best expert.

The results of Section 2 provide a method for solving this
problem. Specifically, we run algorithm Hedge(;), treating
each expert as a strategy. At every time step, Hedge( ;)
produces a distribution pt on the set of experts which is used
to construct the mixture distribution

N
Dt= :
i=1

i E t
p t
i .

Thus, if we define l t
learner is pt } lt,
analyzed in Section 2.

i =4(Et
i , |t) then the loss suffered by the
i.e., exactly the mixture loss that was

Hence, the bounds of Section 2 can be applied to our
current framework. For instance, applying Eq. (11), we
obtain the following:

Theorem 5. For any loss function *, for any set of
experts, and for any sequence of outcomes, the expected loss
of Hedge( ;) if used as described above is at most

T
:
t=1

4(D t, |t)(cid:29)min

i

T
:
t=1

4(E t

i , |t)+- 2L(cid:25)

ln N+ln N

where L(cid:25) (cid:29)T is an assumed bound on the expected loss of the
best expert, and ;= g(L(cid:25) (cid:18)ln N).

Example 1.

In the k-ary prediction problem, 2=0=
[1, 2, ..., k], and *($, |) is 1 if ${| and 0 otherwise. In
other words, the problem is to predict a sequence of letters
over an alphabet of size k. The loss function * is 1 if a
mistake was made, and 0 otherwise. Thus, 4(D, |) is the
probability (with respect to D) of a prediction that disagrees
with |. The cumulative loss of the learner, or of any expert,
is therefore the expected number of mistakes on the entire
sequence. So, in this case, Theorem 2 states that the expec-
ted number of mistakes of the learning algorithm will exceed
the expected number of mistakes of the best expert by at
most O(- T ln N), or possibly much less if the loss of the
best expert can be bounded ahead of time.

Bounds of this type were previously proved in the binary
case (k=2) by Littlestone and Warmuth [20] using the
same algorithm. Their algorithm was later improved by
Vovk [25] and Cesa-Bianchi et al. [4]. The main result of
this section is a proof that such bounds can be shown to
hold for any bounded loss function.

Example 2. The loss function * may represent an
arbitrary matrix game, such as ‘‘rock, paper, scissors.’’ Here,
2=0=[R, P, S], and the loss function is defined by the
matrix:

|

R P S
0
1
1
1
2
1
0
2

R 1
2
$ P 0

S 1

For any outcome |t, the loss suffered by Hedge( ;) will
then be

N
4(Dt, |t)= :
i=1

i 4(E t
p t

i , |t).

The decision $ represents the learner’s play, and the out-
come | is the adversary’s play; then *($, |), the learner’s
loss, is 1 if the learner loses the round, 0 if it wins the round,
and 1(cid:18)2 if the round is tied. (For instance, *(S, P)=0 since
‘‘scissors cut paper.’’) So the cumulative loss of the learner

File: 571J 150405 . By:BV . Date:29:07:01 . Time:05:35 LOP8M. V8.0. Page 01:01
Codes: 5719 Signs: 4418 . Length: 56 pic 0 pts, 236 mm



<!-- pdf-page: 6 -->
124

FREUND AND SCHAPIRE

To see how to handle the problem of finding deterministic
predictions, notice that the loss function *($, |) is convex
with respect to $:

&(a$1+(1&a) $2)&|&(cid:29)a &$1&|&+(1&a) &$2&|&

(13)

for any a # [0, 1] and any | # 0. Thus we can do as follows.
At time t, the learner predicts with the weighted average of
the experts’ predictions: $t=(cid:29) N
i # Rn is the
prediction of the i th expert at time t. Regardless of the
outcome |t, Eq. (13) implies that

i where = t

i=1 p t

i = t

N
&$t&|t&(cid:29) :
i=1

i &= t
p t

i &| t&.

Since Theorem 2 provides an upper bound on the right
hand side of this inequality, we also obtain upper bounds
for the left hand side. Thus, our results in this case give
explicit bounds on the total error (i.e., distance between
predicted and observed points) for the learner relative to the
best of a team of experts.

In the one-dimensional case (n=1),

this case was
previously analyzed by Littlestone and Warmuth [20], and
later improved upon by Kivinen and Warmuth [19].

This result depends only on the convexity and the
bounded range of the loss function *($, |) with respect to $.
Thus, it can also be applied, for example, to the squared-
distance loss function *($, |)=&$&|&2, as well as the log
loss function *($, |)=&ln($ } |) used by Cover [6] for the
design of ‘‘universal’’ investment portfolios. (In this last
case, 2 is the set of probability vectors on n points, and
0=[1(cid:18)B, B] n for some constant B>1.)

In many of the cases listed above, superior algorithms or
analyses are known. Although weaker in specific cases, it
should be emphasized that our results are far more general,
and can be applied in settings that exhibit considerably less
structure, such as the horse-racing example described in the
introduction.

4. BOOSTING

In this section we show how the algorithm presented in
Section 2 for the on-line allocation problem can be modified
to boost the performance of weak learning algorithms.

We very briefly review the PAC learning model (see, for
instance, Kearns and Vazirani [18] for a more detailed
description). Let X be a set called the domain. A concept is
a Boolean function c : X (cid:20) [0, 1]. A concept class C is a
collection of concepts. The learner has access to an oracle
which provides labelled examples of the form (x, c(x))
where x is chosen randomly according to some fixed but

(or an expert) is the expected number of losses in a series of
rounds of game play (counting ties as half a loss). Our
results show then that,
in repeated play, the expected
number of rounds lost by our algorithm will converge
quickly to the expected number that would have been lost
by the best of the experts (for the particular sequence of
moves that were actually played by the adversary).

Example 3. Suppose that 2 and 0 are finite, and that *
represents a game matrix as in the last example. Suppose
further that we create one expert for each decision $ # 2 and
that expert always recommends playing $. In game-
theoretic terminology such experts would be identified with
pure strategies. Von Neumann’s classical min-max theorem
states that for any fixed game matrix there exists a distribu-
tion over the actions, also called a mixed strategy, which
achieves the min-max optimal value of the expected loss
against any adversarial strategy. This min-max value is also
called the value of the game.

Suppose that we use algorithm Hedge(;) to choose dis-
tributions over the actions when playing a matrix game
repeatedly. In this case, Theorem 2 implies that the gap
between the learner’s average per-round loss can never be
much larger than that of the best pure strategy, and that the
maximal gap decreases to zero at the rate O(1- T log |2| ).
However, the expected loss of the optimal mixed strategy is
a fixed convex combination of the losses of the pure
strategies, thus it can never be smaller than the loss of the
best pure strategy for a particular sequence of events.
We conclude that the expected per-trial loss of Hedge( ;)
is upper bounded by the value of
the game plus
O(1(cid:18)- T log |2| ). In other words, the algorithm can never
perform much worse that an algorithm that uses the optimal
mixed strategy for the game, and it can be better if the
adversary does not play optimally. Moreover, this holds
true even if the learner knows nothing at all about the game
that is being played (so that * is unknown to the learner),
the adversarial opponent has complete
and even if
knowledge both of the game that is being played and the
algorithm that is being used by the learner. Algorithms with
similar properties (but weaker convergence bounds) were
first devised by Blackwell [2] and Hannan [14]. For more
details see our related paper [13].

Example 4. Suppose that 2=0 is the unit ball in Rn,
and that *($, |)=&$&|&. Thus, the problem here is to
predict the location of a point |, and the loss suffered is the
Euclidean distance between the predicted point $ and the
actual outcome |. Theorem 2 can be applied if probabilistic
predictions are allowed. However, in this setting it is more
natural to require that the learner and each expert predict a
single point (rather than a measure on the space of possible
points). Essentially, this is the problem of
‘‘tracking’’ a
sequence of points |1, ..., |T where the loss function
measures the distance to the predicted point.

File: 571J 150406 . By:CV . Date:28:07:01 . Time:05:54 LOP8M. V8.0. Page 01:01
Codes: 6096 Signs: 5274 . Length: 56 pic 0 pts, 236 mm



<!-- pdf-page: 7 -->
A DECISION THEORETIC GENERALIZATION

125

unknown and arbitrary distribution D on the domain X,
and c # C is the target concept. After some amount of time,
the learner must output a hypothesis h: X (cid:20) [0, 1]. The
value h(x) can be interpreted as a randomized prediction of
the label of x that is 1 with probability h(x) and 0 with prob-
ability 1&h(x). (Although we assume here that we have
direct access to the bias of this prediction, our results can be
extended to the case that h is instead a random mapping
into [0, 1].) The error of the hypothesis h is the expected
value Ext D( |h(x)&c(x)| ) where x is chosen according to
D. If h(x) is interpreted as a stochastic prediction, then this
is simply the probability of an incorrect prediction.

A strong PAC-learning algorithm is an algorithm that,
given =, $>0 and access to random examples, outputs with
probability 1&$ a hypothesis with error at most =. Further,
the running time must be polynomial in 1(cid:18)=, 1(cid:18)$ and other
relevant parameters (namely, the ‘‘size’’ of the examples
received, and the ‘‘size’’ or ‘‘complexity’’ of the target
concept). A weak PAC-learning algorithm satisfies the same
conditions but only for =(cid:30)1(cid:18)2&# where #>0 is either a
constant, or decreases as 1(cid:18)p where p is a polynomial in the
relevant parameters. We use WeakLearn to denote a generic
weak learning algorithm.

Schapire [22] showed that any weak learning algorithm
can be efficiently transformed or ‘‘boosted’’ into a strong
learning algorithm. Later, Freund [10, 11] presented the
‘‘boost-by-majority’’ algorithm that is considerably more
efficient than Schapire’s. Both algorithms work by calling a
given weak learning algorithm WeakLearn multiple times,
each time presenting it with a different distribution over the
domain X, and finally combining all of the generated
hypotheses into a single hypothesis. The intuitive idea is to
alter the distribution over the domain X in a way that
increases the probability of the ‘‘harder’’ parts of the space,
thus forcing the weak learner to generate new hypotheses
that make less mistakes on these parts.

An important, practical deficiency of

the boost-by-
majority algorithm is the requirement that the bias # of the
weak learning algorithm WeakLearn be known ahead of
time. Not only is this worst-case bias usually unknown in
practice, but the bias that can be achieved by WeakLearn
will typically vary considerably from one distribution to the
next. Unfortunately, the boost-by-majority algorithm can-
not take advantage of hypotheses computed by WeakLearn
with error significantly smaller than the presumed worst-
case bias of 1(cid:18)2&#.

In this section, we present a new boosting algorithm
which was derived from the on-line allocation algorithm of
Section 2. This new algorithm is very nearly as efficient as
boost-by-majority. However, unlike boost-by-majority,
the accuracy of the final hypothesis produced by the new
algorithm depends on the accuracy of all the hypotheses
returned by WeakLearn, and so is able to more fully exploit
the power of the weak learning algorithm.

Also,

this new algorithm gives a clean method for
handling real-valued hypotheses which often are produced
by neural networks and other learning algorithms.

4.1. The New Boosting Algorithm

Although boosting has its roots in the PAC model, for the
remainder of the paper, we adopt a more general learning
framework in which the learner receives examples (xi , yi)
chosen randomly according to some fixed but unknown
distribution P on X_Y, where Y is a set of possible labels.
As usual, the goal is to learn to predict the label y given an
instance x.

We start by describing our new boosting algorithm in the
simplest case that the label set Y consists of just two possible
labels, Y=[0, 1]. In later sections, we give extensions of the
algorithm for more general label sets.

Freund [11] describes two frameworks in which boosting
can be applied: boosting by filtering and boosting by
sampling. In this paper, we use the boosting by sampling
framework, which is the natural framework for analyzing
‘‘batch’’ learning,
learning using a fixed training set
i.e.,
which is stored in the computer’s memory.

We assume that a sequence of N training examples
(labelled instances) (x1 , y1), ..., (x N , yN) is drawn randomly
from X_Y according to distribution P. We use boosting to
find a hypothesis hf which is consistent with most of the
sample (i.e., hf (x i)= yi for most 1(cid:29)i(cid:29)N). In general, a
hypothesis which is accurate on the training set might not
be accurate on examples outside the training set; this
problem is sometimes referred to as ‘‘over-fitting.’’ Often,
however, overfitting can be avoided by restricting the
hypothesis to be simple. We will come back to this problem
in Section 4.3.

The new boosting algorithm is described in Fig. 2. The
goal of the algorithm is to find a final hypothesis with low
error relative to a given distribution D over the training
examples. Unlike the distribution P which is over X_Y
and is set by ‘‘nature,’’ the distribution D is only over the
instances in the training set and is controlled by the learner.
Ordinarily, this distribution will be set to be uniform so that
D(i)=1(cid:18)N. The algorithm maintains a set of weights wt over
the training examples. On iteration t a distribution pt is
computed by normalizing these weights. This distribution is
fed to the weak learner WeakLearn which generates a
hypothesis ht that (we hope) has small error with respect to
the distribution.1 Using the new hypothesis ht , the boosting

1 Some learning algorithms can be generalized to use a given distribution
directly. For instance, gradient based algorithms can use the probability
associated with each example to scale the update step size which is based
on the example. If the algorithm cannot be generalized in this way, the
training sample can be re-sampled to generate a new set of training exam-
ples that is distributed according to the given distribution. The computa-
tion required to generate each re-sampled example takes O(log N) time.

File: 571J 150407 . By:CV . Date:28:07:01 . Time:05:54 LOP8M. V8.0. Page 01:01
Codes: 6774 Signs: 6015 . Length: 56 pic 0 pts, 236 mm



<!-- pdf-page: 8 -->
126

FREUND AND SCHAPIRE

of a real-valued neural network, observed that summing the
outcomes of the networks and then selecting the best predic-
tion performs better than selecting the best prediction of
each network and then combining them with a majority
rule. It is interesting that the new boosting algorithm’s
final hypothesis uses the same combination rule that was
observed to be better in practice, but which previously
lacked theoretical justification.

Since it was first introduced, several successful experi-
ments have been conducted using AdaBoost, including work
by the authors [12], Drucker and Cortes [8], Jackson and
Craven [16], Quinlan [21], and Breiman [3].

4.2. Analysis

Comparing Figs. 1 and 2, there is an obvious similarity
between the algorithms Hedge(;) and AdaBoost. This
similarity reflects a surprising ‘‘dual’’ relationship between
the on-line allocation model and the problem of boosting.
Put another way, there is a direct mapping or reduction of
the boosting problem to the on-line allocation problem. In
such a reduction, one might naturally expect a corres-
pondence relating the strategies to the weak hypotheses and
the trials (and associated loss vectors) to the examples in the
training set. However, the reduction we have used is rever-
sed: the ‘‘strategies’’ correspond to the examples, and the
trials are associated with the weak hypotheses. Another
reversal is in the definition of the loss: in Hedge( ;) the loss
l t
i is small if the ith strategy suggests a good action on the
tth trial while in AdaBoost the ‘‘loss’’ l t
i =1& |ht(xi)& yi |
appearing in the weight-update rule (Step 5) is small if the
tth hypothesis suggests a bad prediction on the i th example.
The reason is that in Hedge( ;) the weight associated with
a strategy is increased if the strategy is successful while
in AdaBoost the weight associated with an example is
increased if the example is ‘‘hard.’’

The main technical difference between the two algorithms
is that in AdaBoost the parameter ; is no longer fixed ahead
of time but rather changes at each iteration according to =t .
If we are given ahead of
time the information that
=t(cid:29)1(cid:18)2&# for some #>0 and for all t=1, ..., T, then we
could instead directly apply algorithm Hedge(;) and its
analysis as follows: Fix ; to be 1&#, and set l t
i =1&
|ht(x i)& yi |, and hf as in AdaBoost, but with equal weight
assigned to all T hypotheses. Then pt } lt is exactly the
accuracy of ht on distribution pt, which, by assumption, is at
is
least 1(cid:18)2+#. Also,
straightforward to show that if i # S then

letting S=[i : hf (xi){ yi],

it

Li
T

=

1
T

T
:
t=1

l t

i =1&

1
T

T
:
t=1

| yi&ht(x i)|

=1&} y i&

1
T

T
:
t=1

ht(xi)} (cid:29)1(cid:18)2

Algorithm AdaBoost
Input: sequence of N labeled examples ((x1 , y1), ..., (xN , yN))

distribution D over the N examples
weak learning algorithm WeakLearn
integer T specifying number of iterations

Initialize the weight vector: w1
Do for t=1, 2, ..., T

i =D(i) for i=1, ..., N.

1. Set

pt=

wt
i=1 w t

i

(cid:29) N

2. Call WeakLearn, providing it with the distribution pt; get back a

hypothesis ht : X (cid:20) [0, 1].

3. Calculate the error of ht: =t=(cid:29) N
4. Set ;t==t (cid:18)(1&=t).
5. Set the new weights vector to be

i=1 p t

i |ht(xi)& yi |.

w t+1

i =w t

i ; 1& |ht(xi)& yi |

t

Output the hypothesis

hf (x)={1

0

t=1 (log 1(cid:18); t) ht(x)(cid:30) 1

2 (cid:29) T

t=1 log 1(cid:18);t

if (cid:29)T
otherwise.

FIG. 2. The adaptive boosting algorithm.

algorithm generates the next weight vector wt+1, and the
process repeats. After T such iterations, the final hypothesis
hf is output. The hypothesis hf combines the outputs of the
T weak hypotheses using a weighted majority vote.

We call the algorithm AdaBoost because, unlike previous
algorithms, it adjusts adaptively to the errors of the weak
hypotheses returned by WeakLearn. If WeakLearn is a PAC
weak learning algorithm in the sense defined above, then
=t(cid:29)1(cid:18)2&# for all t (assuming the examples have been
generated appropriately with yi=c(x i) for some c # C).
However, such a bound on the error need not be known
ahead of time. Our results hold for any =t # [0, 1], and
depend only on the performance of the weak learner on
those distributions that are actually generated during the
boosting process.

The parameter ;t is chosen as a function of =t and is used
for updating the weight vector. The update rule reduces
the probability assigned to those examples on which the
hypothesis makes a good prediction and increases the prob-
ability of the examples on which the prediction is poor.2

Note that AdaBoost, unlike boost-by-majority, combines
the weak hypotheses by summing their probabilistic predic-
tions. Drucker, Schapire and Simard [9], in experiments
they performed using boosting to improve the performance

2 Furthermore, if h t is Boolean (with range [0, 1]), then it can be shown
that this update rule exactly removes the advantage of the last hypothesis.
That is, the error of ht on distribution pt+1 is exactly 1(cid:18)2.

File: 571J 150408 . By:CV . Date:28:07:01 . Time:05:54 LOP8M. V8.0. Page 01:01
Codes: 6184 Signs: 4760 . Length: 56 pic 0 pts, 236 mm



<!-- pdf-page: 9 -->
A DECISION THEORETIC GENERALIZATION

127

by hf ’s definition, and since yi # [0, 1]. Thus, by Theorem 2,

Combining this inequality over t=1, ..., T, we get that

T
T } (1(cid:18)2+#)(cid:29) :
t=1

pt } lt

N
:
i=1

w T+1

T
i (cid:29) ‘
t=1

(1&(1&=t)(1&;t)).

(16)

(cid:29)

&ln((cid:29) i # S D(i))+(#+#2)(T(cid:18)2)
#

The final hypothesis hf , as defined in Fig. 2, makes a mistake
on instance i only if

T
‘
t=1

; &|ht(xi)& yi |

t

T

(cid:30)\ ‘

t=1

&1(cid:18)2

;t+

(17)

(since yi # [0, 1]). The final weight of any instance i is

w T+1

T
i =D(i) ‘
t=1

; 1& |ht(xi)& yi |

t

.

(18)

Combining Eqs. (17) and (18) we can lower bound the sum
of the final weights by the sum of the final weights of the
examples on which hf is incorrect:

N
:
i=1

w T+1

i (cid:30) :

wT+1
i

i : hf (xi){ yi

T

D(i)+\ ‘

t=1

i : hf (xi){ yi

(cid:30)\ :
== }\ ‘

T

t=1

1(cid:18)2

; t+

1(cid:18)2

;t+

(19)

where = is the error of hf . Combining Eqs. (16) and (19), we
get that

T
=(cid:29) ‘
t=1

1&(1&=t)(1&; t)
- ; t

.

(20)

As all the factors in the product are positive, we can
minimize the right hand side by minimizing each factor
separately. Setting the derivative of the t th factor to zero, we
find that the choice of ;t which minimizes the right hand
into
side is ;t==t(cid:18)(1&=t). Plugging this choice of ;t
Eq. (20) we get Eq. (14), completing the proof.

K

The bound on the error given in Theorem 6, can also be

written in the form

T
=(cid:29) ‘
t=1

- 1&4# 2
t

T

t=1

=exp \ & :
(cid:29)exp \ &2 :

T

t=1

KL(1(cid:18)2 & 1(cid:18)2&#t)+

# 2

t +

(21)

since &ln(;)=&ln(1&#)(cid:29)#+#2 for # # [0, 1(cid:18)2]. This
implies that the error ==(cid:29)i # S D(i) of hf is at most e&T#2(cid:18)2.
The boosting algorithm AdaBoost has two advantages
over this direct application of Hedge( ;). First, by giving a
more refined analysis and choice of ;, we obtain a
significantly superior bound on the error =. Second, the
algorithm does not require prior knowledge of the accuracy
of the hypotheses that WeakLearn will generate. Instead, it
measures the accuracy of ht at each iteration and sets its
parameters accordingly. The update factor ;t decreases with
=t which causes the difference between the distributions pt
and pt+1 to increase. Decreasing ;t also increases the weight
ln(1(cid:18);t) which is associated with ht in the final hypothesis.
This makes intuitive sense: more accurate hypotheses cause
larger changes in the generated distributions and have more
influence on the outcome of the final hypothesis.

We now give our analysis of

the performance of
AdaBoost. Note that this theorem applies also if, for some
hypotheses, =t(cid:30)1(cid:18)2.

Theorem 6. Suppose

the weak learning algorithm
WeakLearn, when called by AdaBoost, generates hypotheses
with errors =1 , ..., =T (as defined in Step 3 of Fig. 2.) Then the
error ==PritD[hf (x i){ y i] of the final hypothesis hf output
by AdaBoost is bounded above by

T
=(cid:29)2T ‘
t=1

- =t(1&=t).

(14)

Proof. We adapt the main arguments from Lemma 1
and Theorem 2. We use pt and wt as they are defined in
Fig. 2.

Similar to Eq. (4), the update rule given in Step 5 in Fig. 2

implies that

N
:
i=1

w t+1

N
i = :
i=1

N
(cid:29) :
i=1

w t

i ; 1& |ht(xi)& yi |

t

w t

i(1&(1&;t)(1& |ht(xi)& y i | ))

N

=\ :

i=1

w t

i+ (1&(1&=t)(1&; t)).

(15)

File: 571J 150409 . By:CV . Date:28:07:01 . Time:05:54 LOP8M. V8.0. Page 01:01
Codes: 4650 Signs: 2859 . Length: 56 pic 0 pts, 236 mm



<!-- pdf-page: 10 -->
128

FREUND AND SCHAPIRE

where KL(a & b)=a ln(a(cid:18)b)+(1&a) ln((1&a)(cid:18)(1&b)) is
the Kullback(cid:21)Leibler divergence, and where =t has been
replaced by 1(cid:18)2&#t . In the case where the errors of all the
hypotheses are equal to 1(cid:18)2&#, Eq. (21) simplifies to

=(cid:29)(1&4#2)T(cid:18)2

=exp( &T } KL(1(cid:18)2 & 1(cid:18)2&#))

(cid:29)exp( &2T#2).

(22)

This is a form of the Chernoff bound for the probability that
less than T(cid:18)2 coin flips turn out ‘‘heads’’ in T tosses of a ran-
dom coin whose probability for ‘‘heads’’ is 1(cid:18)2&#. This
bound has the same asymptotic behavior as the bound
given for the boost-by-majority algorithm [11]. From
Eq. (22) we get that the number of iterations of the boosting
algorithm that is sufficient to achieve error = of hf is

on the VC-dimension of the concept class. This method
is sometimes called ‘‘structural risk minimization.’’ See
Vapnik’s book [23] for an extensive discussion of the
theory of structural risk minimization. For our purposes, we
quote Vapnik’s Theorem 6.7:

Theorem 7 (Vapnik). Let H be a class of binary func-
tions over some domain X. Let d be the VC-dimension of H.
Let P be a distribution over the pairs X_[0, 1]. For h # H,
define the ( generalization) error of h with respect to P to be

=g(h).Pr (x, y)t P [h(x){ y].

Let S=[(x1 , y1), ..., (xN , yN)] be a sample (training set) of
N independent random examples drawn from X_[0, 1]
according to P. Define the empirical error of h with respect
to the sample S to be

1
KL(1(cid:18)2 & 1(cid:18)2&#)

T=(cid:18)
(cid:29)(cid:18) 1

2#2 ln

1

=|.

ln

1

=|

=^ (h).

|[i : h(xi){ yi]|
N

.

(23)

Then, for any $>0 we have that

Pr __h # H : |=^ (h)&=g(h)|

>2 (cid:28)d(ln 2N(cid:18)d+1)+ln 9(cid:18)$

N

&(cid:29)$

where the probability is computed with respect to the random
choice of the sample S.

Let % : R (cid:20) [0, 1] be defined by

%(x)={1

0

if x(cid:30)0
otherwise

and, for any class H of functions, let 3T (H) be the class of
all functions defined as a linear threshold of T functions
in H:

T

3T (H)={% \ :

t=1

ath t&b+ : b, a1 , ..., aT # R;

h1 , ..., h T # H= .

Clearly, if all hypotheses generated by WeakLearn belong to
some class H, then the final hypothesis of AdaBoost, after T
rounds of boosting, belongs to 3T (H). Thus, the next
theorem provides an upper bound on the VC-dimension of
the class of final hypotheses generated by AdaBoost in terms
of the weak hypothesis class.

Note, however, that when the errors of the hypotheses
generated by WeakLearn are not uniform, Theorem 6
implies that the final error depends on the error of all of the
weak hypotheses. Previous bounds on the errors of boosting
algorithms depended only on the maximal error of the
weakest hypothesis and ignored the advantage that can be
gained from the hypotheses whose errors are smaller. This
advantage seems to be very relevant to practical applica-
tions of boosting, because there one expects the error of the
learning algorithm to increase as the distributions fed to
WeakLearn shift more and more away from the target
distribution.

4.3. Generalization Error

We now come back to discussing the error of the final
hypothesis outside the training set. Theorem 6 guarantees
that the error of hf on the sample is small; however, the
quantity that interests us is the generalization error of hf ,
which is the error of hf over the whole instance space X; that
is, =g=Pr (x, y)t P[h f (x){ y]. In order to make =g close to
the empirical error =^ on the training set, we have to restrict
the choice of hf in some way. One natural way of doing this
in the context of boosting is to restrict the weak learner to
choose its hypotheses from some simple class of functions
and restrict T, the number of weak hypotheses that are com-
bined to make hf . The choice of the class of weak hypotheses
is specific to the learning problem at hand and should reflect
our knowledge about the properties of the unknown con-
cept. As for the choice of T, various general methods can be
devised. One popular method is to use an upper bound

File: 571J 150410 . By:CV . Date:28:07:01 . Time:05:54 LOP8M. V8.0. Page 01:01
Codes: 5261 Signs: 3766 . Length: 56 pic 0 pts, 236 mm



<!-- pdf-page: 11 -->
A DECISION THEORETIC GENERALIZATION

129

Theorem 8. Let H be a class of binary functions of
VC-dimension d(cid:30)2. Then the VC-dimension of 3T (H) is at
most 2(d+1)(T+1) log2(e(T+1)) (where e is the base of
the natural logarithm).

Therefore, if the hypotheses generated by WeakLearn are
chosen from a class of VC-dimension d(cid:30)2, then the final
hypotheses generated by AdaBoost after T iterations
belong to a class of VC-dimension at most 2(d+1)(T+1)
log2[e(T+1)].

Proof. We use a result about the VC-dimension of com-
putation networks proved by Baum and Haussler [1]. We
can view the final hypothesis output by AdaBoost as a func-
tion that is computed by a two-layer feed-forward network
where the computation units of the first layer are the weak
hypotheses and the computation unit of the second layer is
the linear threshold function which combines the weak
hypotheses. The VC-dimension of the set of linear threshold
functions over RT is T+1 [26]. Thus the sum over all
computation units of the VC-dimensions of the classes of
functions associated with each unit
is Td+(T+1)<
(T+1)(d+1). Baum and Haussler’s Theorem 1 [1] implies
that the number of different functions that can be realized
by h # 3T (H) when the domain is restricted to a set of size
m is at most ((T+1) em(cid:18)(T+1)(d+1)) (T+1)(d+1). If d(cid:30)2,
T(cid:30)1 and we set m=W2(T+1)(d+1) log2[e(T+1)]X,
then the number of realizable functions is smaller than 2m
which implies that the VC-dimension of 3T (H) is smaller
than m.

K

Following the guidelines of structural risk minimization
we can do the following (assuming we know a reasonable
upper bound on the VC-dimension of the class of weak
hypotheses). Let hT
f be the hypothesis generated by running
AdaBoost for T iterations. By combining the observed
empirical error of h T
f with the bounds given in Theorems 7
and 8, we can compute an upper bound on the generaliza-
tion error of h T
for all T. We would then select the
f
hypothesis h T
f that minimizes the guaranteed upper bound.
While structural risk minimization is a mathematically
sound method, the upper bounds on =g that are generated in
this way might be larger than the actual value and so the
chosen number of iterations T might be much smaller than
the optimal value, leading to inferior performance. A simple
alternative is to use ‘‘cross-validation’’ in which a fraction of
the training set is left outside the set used to generate hf as
the so-called ‘‘validation’’ set. The value of T is then chosen
to be the one for which the error of the final hypothesis on
the validation set is minimized. (For an extensive analysis of
the relations between different methods for selecting model
complexity in learning, see Kearns et al. [17].)

Some initial experiments using AdaBoost on real-world
problems conducted by ourselves and Drucker and Cortes
[8] indicate that AdaBoost tends not to over-fit; on many

problems, even after hundreds of rounds of boosting, the
generalization error continues to drop, or at least does not
increase.

4.4. A Bayesian Interpretation

The final hypothesis generated by AdaBoost is closely
related to one suggested by a Bayesian analysis. As usual,
we assume that examples (x, y) are being generated
according to some distribution P on X_[0, 1]; all
probabilities in this subsection are taken with respect to P.
Suppose we are given a set of [0, 1]-valued hypotheses
h1 , ..., h T and that our goal is to combine the predictions of
these hypotheses in the optimal way. Then, given an
instance x and the hypothesis predictions ht(x), the Bayes
optimal decision rule says that we should predict the label
with the highest likelihood, given the hypothesis values, i.e.,
we should predict 1 if

Pr[ y=1 | h1(x), ..., hT (x)]>Pr[ y=0 | h1(x), ..., h T (x)],

and otherwise we should predict 0.

This rule is especially easy to compute if we assume that
the errors of the different hypotheses are independent of one
another and of the target concept, that is, if we assume that
the event ht(x){ y is conditionally independent of the
actual label y and the predictions of all the other hypotheses
h1(x), ..., ht&1(x), ht+1(x), ..., hT (x).
case, by
applying Bayes rule, we can rewrite the Bayes optimal deci-
sion rule in a particularly simple form in which we predict
1 if

In this

Pr[ y=1] ‘

=t ‘

(1&= t)

t : ht(x)=0

t : ht(x)=1

>Pr[ y=0] ‘

(1&=t) ‘

=t ,

t : ht(x)=0

t : ht(x)=1

and 0 otherwise. Here =t=Pr[ht(x){ y]. We add to the set
of hypotheses the trivial hypothesis h0 which always
predicts the value 1. We can then replace Pr[ y=0] by =0 .
Taking the logarithm of both sides in this inequality and
rearranging the terms, we find that the Bayes optimal
decision rule is identical to the combination rule that is
generated by AdaBoost.

If the errors of the different hypotheses are dependent,
then the Bayes optimal decision rule becomes much more
complicated. However, in practice, it is common to use the
simple rule described above even when there is no justifica-
tion for assuming independence. (This is sometimes called
‘‘naive Bayes.’’) An interesting and more principled alter-
native to this practice would be to use the algorithm
AdaBoost to find a combination rule which, by Theorem 6,
has a guaranteed non-trivial accuracy.

File: 571J 150411 . By:CV . Date:28:07:01 . Time:05:54 LOP8M. V8.0. Page 01:01
Codes: 6095 Signs: 5147 . Length: 56 pic 0 pts, 236 mm



<!-- pdf-page: 12 -->
130

FREUND AND SCHAPIRE

4.5. Improving the Error Bound

Since yi # [0, 1] and by definition of r(xi), this implies that

We show in this section how the bound given in
Theorem 6 can be improved by a factor of two. The main
idea of this improvement is to replace the ‘‘hard’’ [0, 1]-
valued decision used by hf by a ‘‘soft’’ threshold.

To be more precise, let

=(cid:29)

=

; 1(cid:18)2& |ht(xi)& yi |

t

+

T

N
:

1
2

t=1

i=1 \D(i) ‘
2 \ :

w T+1
i

i=1

1

N

T

+ ‘

t=1

; &1(cid:18)2
t

(cid:29)

1
2

T
‘
t=1

((1&(1&=t)(1&;t)) ; &1(cid:18)2

t

).

The last two steps follow from Eqs. (18) and (16), respec-
tively. The theorem now follows from our choice of ;t . K

5. BOOSTING FOR MULTI-CLASS AND
REGRESSION PROBLEMS

So far, we have restricted our attention to binary
classification problems in which the set of labels Y contains
only two elements. In this section, we describe two possible
extensions of AdaBoost to the multi-class case in which Y is
any finite set of class labels. We also give an extension for a
regression problem in which Y is a real bounded interval.

is

first

The

extension of AdaBoost, which we

We start with the multiple-label classification problem.
Let Y=[1, 2, ..., k] be the set of possible labels. The
boosting algorithms we present output hypotheses hf :
X (cid:20) Y, and the error of the final hypothesis is measured in
the usual way as the probability of an incorrect prediction.
call
AdaBoost.M1,
the most direct. The weak learner
generates hypotheses which assign to each instance one of
the k possible labels. We require that each weak hypothesis
have prediction error less than 1(cid:18)2 (with respect to the dis-
tribution on which it was trained). Provided this require-
ment can be met, we are able to prove that the error of the
combined final hypothesis decreases exponentially, as in
the binary case. Intuitively, however, this requirement on
the performance of the weak learner is stronger than might
be desired. In the binary case (k=2), a random guess will be
correct with probability 1(cid:18)2, but when k>2, the probability
of a correct random prediction is only 1(cid:18)k<1(cid:18)2. Thus, our
requirement that the accuracy of the weak hypothesis be
greater than 1(cid:18)2 is significantly stronger than simply
requiring that the weak hypothesis perform better than
random guessing.

In fact, when the performance of the weak learner is
measured only in terms of error rate, this difficulty is
unavoidable as is shown by the following informal example
(also presented by Schapire [22]): Consider a learning
problem where Y=[0, 1, 2] and suppose that it is ‘‘easy’’ to
predict whether the label is 2 but ‘‘hard’’ to predict whether
the label
is 0 or 1. Then a hypothesis which predicts
correctly whenever the label is 2 and otherwise guesses

r(x)=

(cid:29) T

t=1 (log 1
; t
t=1 log 1
(cid:29) T
; t

) h t(x)

be a weighted average of the weak hypotheses ht . We will
here consider final hypotheses of the form hf (x)=F(r(x))
where F: [0, 1] (cid:20) [0, 1]. For the version of AdaBoost given
in Fig. 2, F(r) is the hard threshold that equals 1 if r(cid:30)1(cid:18)2
and 0 otherwise. In this section, we will instead use soft
threshold functions that take values in [0, 1]. As mentioned
above, when hf (x) # [0, 1], we can interpret hf as a
randomized hypothesis and hf (x) as the probability of
predicting 1. Then the error EitD[ |hf (x i)& y i | ] is simply
the probability of an incorrect prediction.

Theorem 9. Let =1 , ..., =T be as in Theorem 6, and let
r(xi) be as defined above. Let the modified final hypothesis be
defined by hf (x)=F(r(x)) where F satisfies the following for
r # [0, 1]:

F(1&r)=1&F(r);

and

F(r)(cid:29)

T

1

2 \ ‘

t=1

1(cid:18)2&r
.

; t+

Then the error = of hf is bounded above by

T
=(cid:29)2T&1 ‘
t=1

- =t(1&=t).

For instance, it can be shown that the sigmoid function
)&1 satisfies the conditions of the

t=1 ; 2r&1

t

F(r)=(1+> T
theorem.

Proof. By our assumptions on F, the error of hf is

N
== :
i=1

N
= :
i=1

D(i) } |F(r(xi))& yi |

D(i) F(|r(xi)& yi | )

(cid:29)

1
2

T

N
:

i=1 \D(i) ‘

t=1

; 1(cid:18)2& |r(xi)& yi |

t

+ .

File: 571J 150412 . By:CV . Date:28:07:01 . Time:05:54 LOP8M. V8.0. Page 01:01
Codes: 5125 Signs: 3769 . Length: 56 pic 0 pts, 236 mm



<!-- pdf-page: 13 -->
A DECISION THEORETIC GENERALIZATION

131

Finally, in Section 5.3 we extend AdaBoost to boosting
regression algorithms. In this case Y=[0, 1], and the error
of a hypothesis is defined as E(x, y)t P[(h(x)& y)2]. We
describe a boosting algorithm AdaBoost.R. which, using
methods similar to those used in AdaBoost.M2, boosts the
performance of a weak regression algorithm.

5.1. First Multi-class Extension

In our first and most direct extension to the multi-class
case, the goal of the weak learner is to generate on round t
a hypothesis ht : X (cid:20) Y with low classification error =t .
Prit p t[ht(x i){ yi]. Our extended boosting algorithm,
called AdaBoost.M1, is shown in Fig. 3, and differs only
slightly from AdaBoost. The main difference is in the
replacement of the error |ht(x i)&y i | for the binary case by
(cid:26)ht(xi){ yi(cid:25) where, for any predicate ?, we define (cid:26)?(cid:25) to be
1 if ? holds and 0 otherwise. Also, the final hypothesis hf , for
a given instance x, now outputs the label y that maximizes
the sum of the weights of the weak hypotheses predicting
that label.

In the case of binary classification (k=2), a weak
hypothesis h with error significantly larger than 1(cid:18)2 is of
equal value to one with error significantly less than 1(cid:18)2 since
h can be replaced by 1&h. However, for k>2, a hypothesis
ht with error =t(cid:30)1(cid:18)2 is useless to the boosting algorithm. If

Algorithm AdaBoost.M1
Input: sequence of N examples ( (x1 , y 1). .., (xN , yN)) with labels
yi # Y=[1, ..., k]

distribution D over the N examples
weak learning algorithm WeakLearn
integer T specifying number of iterations

Initialize the weight vector: w 1
Do for t=1, 2, ..., T

i =D(i) for i=1, ..., N.

1. Set

pt=

wt
i=1 w t

i

(cid:29) N

2. Call WeakLearn, providing it with the distribution pt; get back a

hypothesis ht : X (cid:20) Y.

3. Calculate the error of ht: =t=(cid:29) N
If =t>1(cid:18)2, then set T=t&1 and abort loop.
4. Set ;t==t (cid:18)(1&=t).
5. Set the new weights vector to be

i=1 p t

i (cid:26)ht(xi){ yi(cid:25).

w t+1

i =w t

i ; 1& (cid:26)ht(xi){y% i(cid:25)

t

Output the hypothesis

hf (x)=arg max
y # Y

T
:

t=1\log

1

; t+ (cid:26)ht(x)= y(cid:25).

FIG. 3. A first multi-class extension of AdaBoost.

randomly between 0 and 1 is guaranteed to be correct at
least half of the time (significantly beating the 1(cid:18)3 accuracy
achieved by guessing entirely at random). On the other
hand, boosting this learner to an arbitrary accuracy is
infeasible since we assumed that it is hard to distinguish
0- and 1-labelled instances.

As a more natural example of this problem, consider
classification of handwritten digits in an OCR application.
It may be easy for the weak learner to tell that a particular
image of a ‘‘7’’ is not a ‘‘0’’ but hard to tell for sure if it is a
‘‘7’’ or a ‘‘9’’. Part of the problem here is that, although the
boosting algorithm can focus the attention of the weak
learner on the harder examples, it has no way of forcing the
weak learner to discriminate between particular labels that
may be especially hard to distinguish.

In our second version of multi-class boosting, we attempt
to overcome this difficulty by extending the communication
between the boosting algorithm and the weak learner. First,
we allow the weak learner to generate more expressive
hypotheses whose output is a vector in [0, 1] k, rather than
a single label in Y. Intuitively, the y th component of this
vector represents a ‘‘degree of belief’’ that the correct label
is y. The components with large values (close to 1)
correspond to those labels considered to be plausible.
Likewise, labels considered implausible are assigned a small
value (near 0), and questionable labels may be assigned a
value near 1(cid:18)2. If several labels are considered plausible (or
implausible), then they all may be assigned large (or small)
values.

While we give the weak learning algorithm more
expressive power, we also place a more complex require-
ment on the performance of the weak hypotheses. Rather
than using the usual prediction error, we ask that the weak
hypotheses do well with respect to a more sophisticated
error measure that we call the pseudo-loss. This pseudo-loss
varies from example to example, and from one round to the
next. On each iteration, the pseudo-loss function is supplied
to the weak learner by the boosting algorithm, along with
the distribution on the examples. By manipulating the
pseudo-loss function, the boosting algorithm can focus the
weak learner on the labels that are hardest to discriminate.
The boosting algorithm AdaBoost.M2, described in
Section 5.2, is based on these ideas and achieves boosting if
each weak hypothesis has pseudo-loss slightly better than
random guessing (with respect to the pseudo-loss measure
that was supplied to the weak learner).

In addition to the two extensions described in this paper,
we mention an alternative, standard approach which would
be to convert the given multi-class problem into several
binary problems, and then to use boosting separately on
each of the binary problems. There are several standard
ways of making such a conversion, one of the most success-
ful being the error-correcting output coding approach
advocated by Dietterich and Bakiri [7].

File: 571J 150413 . By:CV . Date:28:07:01 . Time:05:54 LOP8M. V8.0. Page 01:01
Codes: 6060 Signs: 5002 . Length: 56 pic 0 pts, 236 mm



<!-- pdf-page: 14 -->
132

FREUND AND SCHAPIRE

such a weak hypothesis is returned by the weak learner, our
algorithm simply halts, using only the weak hypotheses that
were already computed.

Theorem 10. Suppose the weak learning algorithm
WeakLearn, when called by AdaBoost.M1, generates
hypotheses with errors =1 , ..., =T , where =t
is as defined
in Fig. 3. Assume each =t(cid:29)1(cid:18)2. Then the error ==
PritD[hf (xi){ y i] of the final hypothesis hf output by
AdaBoost.M1 is bounded above by

T
=(cid:29)2T ‘
t=1

- =t(1&=t).

Proof. To prove this theorem, we reduce our setup for
AdaBoost.M1 to an instantiation of AdaBoost, and then
apply Theorem 6. For clarity, we mark with tildes variables
in the reduced AdaBoost space. For each of the given
examples (xi , yi), we define an AdaBoost example (x~ i , y~ i) in
which x~ i=i and y~ i=0. We define the AdaBoost distribution
D(cid:25) over examples to be equal to the AdaBoost.M1 distribu-
tion D. On the tth round, we provide AdaBoost with a
hypothesis h(cid:25) t defined by the rule

h(cid:25) t(i)= (cid:26)ht(x i){ yi(cid:25)

in terms of the tth hypothesis ht which was returned to
AdaBoost.M1 by WeakLearn.

Given this setup, it can be easily proved by induction on
the number of rounds that the weight vectors, distributions
and errors computed by AdaBoost and AdaBoost.M1 are
identical so that w~ t=wt, p~ t=pt, =~ t== t and ;(cid:25) t=;t.

Suppose that AdaBoost.M1’s final hypothesis hf makes a
mistake on instance i so that hf (x i){ y i. Then, by definition
of hf ,

T
:
t=1

T
:t(cid:26)h t(x i)= yi(cid:25) (cid:29) :
t=1

: t(cid:26)ht(x i)=hf (xi)(cid:25)

where :t=ln(1(cid:18);t). This implies

T
:
t=1

:t(cid:26)ht(x i)= yi(cid:25) (cid:29) 1

T
2 :
t=1

:t ,

using the fact that each :t(cid:30)0 since =t(cid:29)1(cid:18)2. By definition of
h(cid:25) t , this implies

T
:
t=1

:t h(cid:25) t(i)(cid:30) 1

T
2 :
t=1

:t ,

so h(cid:25) f (i)=1 by definition of the final AdaBoost hypothesis.

Therefore,

PritD[hf (x i){ yi](cid:29)PritD[h(cid:25) f (i)=1].

Since each AdaBoost instance has a 0-label, PritD[h(cid:25) f (i)
=1] is exactly the error of h(cid:25) f . Applying Theorem 6, we can
obtain a bound on this error, completing the proof.

K

It is possible, for this version of the boosting algorithm, to
allow hypotheses which generate for each x, not only a
predicted class label h(x) # Y, but also a ‘‘confidence’’
}(x) # [0, 1]. The learner then suffers loss 1(cid:18)2&}(x)(cid:18)2 if its
prediction is correct and 1(cid:18)2+}(x)(cid:18)2 otherwise. (Details
omitted.)

5.2. Second Multi-class Extension

In this section we describe a second alternative extension
of AdaBoost to the case where the label space Y is finite. This
extension requires more elaborate communication between
the boosting algorithm and the weak learning algorithm.
The advantage of doing this is that it gives the weak learner
more flexibility in making its predictions. In particular, it
sometimes enables the weak learner to make useful con-
tributions to the accuracy of the final hypothesis even when
the weak hypothesis does not predict the correct label with
probability greater than 1(cid:18)2.
As described above,

the weak learner generates
hypotheses which have the form h : X_Y (cid:20) [0, 1]. Roughly
speaking, h(x, y) measures the degree to which it is believed
that y is the correct label associated with instance x. If, for
a given x, h(x, y) attains the same value for all y then we say
that the hypothesis is uninformative on instance x. On the
other hand, any deviation from strict equality is potentially
informative, because it predicts some labels to be more
plausible than others. As will be seen, any such information
is potentially useful for the boosting algorithm.

Below, we formalize the goal of the weak learner by
defining a pseudo-loss which measures the goodness of the
weak hypotheses. To motivate our definition, we first
consider the following setup. For a fixed training example
(xi , yi), we use a given hypothesis h to answer k&1 binary
questions. For each of the incorrect labels y{ yi we ask the
question:

‘‘Which is the label of xi : yi or y?’’
In other words, we ask that the correct label yi be

discriminated from the incorrect label y.

Assume momentarily that h only takes values in [0, 1].
Then if h(xi , y)=0 and h(xi , yi)=1, we interpret h’s
answer to the question above to be yi (since h deems yi to
be a plausible label for x i , but y is considered implausible).
Likewise, if h(xi , y)=1 and h(xi , yi)=0 then the answer is
y. If h(xi , y)=h(xi , yi), then one of the two answers is
chosen uniformly at random.

File: 571J 150414 . By:CV . Date:28:07:01 . Time:05:54 LOP8M. V8.0. Page 01:01
Codes: 5566 Signs: 4204 . Length: 56 pic 0 pts, 236 mm



<!-- pdf-page: 15 -->
A DECISION THEORETIC GENERALIZATION

133

In the more general case that h takes values in [0, 1], we
interpret h(x, y) as a randomized decision for the procedure
above. That is, we first choose a random bit b(x, y) which
is 1 with probability h(x, y) and 0 otherwise. We then apply
the above procedure to the stochastically chosen binary
function b. The probability of choosing the incorrect answer
y to the question above is

Pr[b(xi , yi)=0 7 b(xi , y)=1]+ 1

2 Pr[b(xi , yi)=b(xi , y)]

= 1

2 (1&h(xi , yi)+h(xi , y)).

If the answers to all k&1 questions are considered
equally important, then it is natural to define the loss of the
hypothesis to be the average, over all k&1 questions, of the
probability of an incorrect answer:

1
k&1

1
2

:
y{ yi

(1&h(x i , yi)+h(xi , y))

=

1

2 \1&h(xi , y i)+

1
k&1

:
y{ yi

h(x i , y)+ .

(24)

However, as was discussed in the introduction to Section 5,
different discrimination questions are likely to have different
importance in different situations. For example, considering
the OCR problem described earlier, it might be that at some
point during the boosting process, some example of the digit
‘‘7’’ has been recognized as being either a ‘‘7’’ or a ‘‘9’’. At this
stage the question that discriminates between ‘‘7’’ (the
correct label) and ‘‘9’’ is clearly much more important than
the other eight questions that discriminate ‘‘7’’ from the
other digits.

A natural way of attaching different degrees of impor-
tance to the different questions is to assign a weight to each
question. So, for each instance xi and incorrect label y{ yi ,
we assign a weight q(i, y) which we associate with the ques-
tion that discriminates label y from the correct label yi . We
then replace the average used in Eq. (24) with an average
weighted according to q(i, y); the resulting formula is called
the pseudo-loss of h on training instance i with respect to q:

The weak learner’s goal is to minimize the expected pseudo-
loss for given distribution D and weighting function q:

plossD, q(h) :=EitD [plossq(h, i)].

As we have seen, by manipulating both the distribution
on instances, and the label weighting function q, our
boosting algorithm effectively forces the weak learner to
focus not only on the hard instances, but also on the
incorrect class labels that are hardest to eliminate. Con-
versely, this pseudo-loss measure may make it easier for the
weak learner to get a weak advantage. For instance, if the
weak learner can simply determine that a particular
instance does not belong to a certain class (even if it has no
idea which of the remaining classes is the correct one), then,
depending on q, this may be enough to gain a weak advan-
tage.

Theorem 11, the main result of this section, shows that a
weak learner can be boosted if it can consistently produce
weak hypotheses with pseudo-losses smaller than 1(cid:18)2. Note
that pseudo-loss 1(cid:18)2 can be achieved trivially by any unin-
formative hypothesis. Furthermore, a weak hypothesis h
with pseudo-loss =>1(cid:18)2 is also beneficial to boosting since
it can be replaced by the hypothesis 1&h whose pseudo-loss
is 1&=<1(cid:18)2.

Example 5. As a simple example illustrating the use of
pseudo-loss, suppose we seek an oblivious weak hypothesis,
i.e., a weak hypothesis whose value depends only on the
class label y so that h(x, y)=h( y) for all x. Although
oblivious hypotheses per se are generally too weak to be of
interest,
it may often be appropriate to find the best
oblivious hypothesis on a part of the instance space (such as
the set of instances covered by a leaf of a decision tree).

Let D be the target distribution, and q the label weighting
function. For notational convenience, let us define q(i, yi)
=&1 for all i so that

plossq(h, i)= 1

2 \1+ :

y # Y

q(i, y) h(xi , y)+ .

Setting $( y)=(cid:29)i D(i) q(i, y), it can be verified that for an
oblivious hypothesis h,

plossq(h, i). 1

2 \1&h(xi , yi)+ :

y{ yi

q(i, y) h(xi , y)+ .

plossD, q(h)= 1

2 \1+ :

y # Y

h( y) $( y)+ ,

The function q=[1, ..., N]_Y (cid:20) [0, 1], called the label
weighting function, assigns to each example i in the training
set a probability distribution over the k&1 discrimination
problems defined above. So, for all i,

which is clearly minimized by the choice

h( y)={1

0

if $( y)<0
otherwise.

q(i, y)=1.

:
y{ yi

Suppose now that q(i, y)=1(cid:18)(k&1) for y{ yi , and let
d( y)=PritD[ yi= y] be the proportion of examples with

File: 571J 150415 . By:CV . Date:28:07:01 . Time:05:54 LOP8M. V8.0. Page 01:01
Codes: 5466 Signs: 4208 . Length: 56 pic 0 pts, 236 mm



<!-- pdf-page: 16 -->
134

FREUND AND SCHAPIRE

Algorithm AdaBoost.M2
Input: sequence of N examples ( (x1 , y 1). .., (xN , yN)) with labels
yi # Y=[1, ..., k]

distribution D over the N examples
weak learning algorithm WeakLearn
integer T specifying number of iterations

Initialize the weight vector: w 1
Do for t=1, 2, ..., T

i, y=D(i)(cid:18)(k&1) for i=1, ..., N, y # Y&[ yi].

1. Set W t

i =(cid:29)y{ yi w t

i, y ;

qt(i, y)=

wt
i, y
W t
i

for y{ yi ; and set

Dt(i)=

W t
i
i=1 W t

i

(cid:29) N

.

2. Call WeakLearn, providing it with the distribution Dt and label

weighting function qt ; get back a hypothesis h t: X_Y (cid:20) [0, 1].

3. Calculate the pseudo-loss of ht :

=t=

1
2

N
:
i=1

Dt(i)\1&ht(xi , y i)+ :

y{ yi

qt(i, y) ht(xi , y)+ .

4. Set ;t==t (cid:18)(1&=t).

5. Set the new weights vector to be

w t+1

i, y =w t

i, y ; (1(cid:18)2)(1+ht(xi , yi)&ht(xi , y))

t

for i=1, ..., N, y # Y&[ yi].

Output the hypothesis

hf (x)=arg max
y # Y

T
:

t=1\log

1

; t+ ht(x, y).

FIG. 4. A second multi-class extension of AdaBoost.

For each training instance (xi , yi) and for each incorrect
label y # Y&[ yi], we define one AdaBoost instance x~ i, y=
(i, y) with associated label y~ i, y=0. Thus, there are N(cid:25) =
N(k&1) AdaBoost instances, each indexed by a pair (i, y).
The distribution over these instances is defined to be D(cid:25) (i, y)
=D(i)(cid:18)(k&1). The tth hypothesis h(cid:25) t provided to AdaBoost
for this reduction is defined by the rule

h(cid:25) t(i, y)= 1

2 (1&h t(xi , yi)+ht(x i , y)).

With this setup, it can be verified that the computed dis-
tributions and errors will be identical so that w~ t
i, y ,
i, y= p t
p~ t

i, y , =~ t==t and ;(cid:25) t=;t .

i, y=w t

label y. Then it can be verified that h will always have
pseudo-loss strictly smaller than 1(cid:18)2 except in the case of a
uniform distribution of
labels (d( y)=1(cid:18)k for all y). In
contrast, when the weak learner’s goal is minimization of
prediction error (as in Section 5.1), it can be shown that an
oblivious hypothesis with prediction error strictly less than
1(cid:18)2 can only be found when one label y covers more than 1(cid:18)2
the distribution (d( y)>1(cid:18)2). So in this case, it is much
easier to find a hypothesis with small pseudo-loss rather
than small prediction error.

On the other hand, if q(i, y)=0 for some values of y, then
the quality of prediction on these labels is of no conse-
quence. In particular, if q(i, y)=0 for all but one incorrect
label for each instance i, then in order to make the pseudo-
loss smaller than 1(cid:18)2 the hypothesis has to predict the
correct label with probability larger than 1(cid:18)2, which means
that in this case the pseudo-loss criterion is as stringent as
the usual prediction error. However, as discussed above,
this case is unavoidable because a hard binary classification
problem can always be embedded in a multi-class problem.
This example suggests that it may often be significantly
easier to find weak hypotheses with small pseudo-loss rather
than hypotheses whose prediction error is small. On the
other hand, our theoretical bound for boosting using the
prediction error (Theorem 10) is stronger than the bound
for ploss (Theorem 11). Empirical tests [12] have shown
that pseudo-loss is generally more successful when the weak
learners use very restricted hypotheses. However, for more
powerful weak learners, such as decision-tree learning algo-
rithms, there is little difference between using pseudo-loss
and prediction error.

Our algorithm called AdaBoost.M2, is shown in Fig. 4.
Here, we maintain weights w t
i, y for each instance i and each
label y # Y&[ yi]. The weak learner must be provided both
with a distribution Dt and a label weight function qt. Both
of these are computed using the weight vector wt as shown
in Step 1. The weak learner’s goal then is to minimize the
pseudo-loss =t , as defined in Step 3. The weights are updated
as shown in Step 5. The final hypothesis hf outputs, for a
given instance x, the label y that maximizes a weighted
average of the weak hypothesis values ht(x, y).

Theorem 11. Suppose the weak learning algorithm
WeakLearn, when called by AdaBoost.M2 generates
hypotheses with pseudo-losses =1 , ..., =T , where =t is as defined
in Fig. 4. Then the error ==PritD[h f (x i){ y i] of the final
hypothesis hf output by AdaBoost.M2 is bounded above by

T
=(cid:29)(k&1) 2T ‘
t=1

- =t(1&= t).

Proof. As in the proof of Theorem 10, we reduce to an
instance of AdaBoost and apply Theorem 6. As before, we
mark AdaBoost variables with a tilde.

File: 571J 150416 . By:CV . Date:28:07:01 . Time:05:54 LOP8M. V8.0. Page 01:01
Codes: 5640 Signs: 4166 . Length: 56 pic 0 pts, 236 mm



<!-- pdf-page: 17 -->
A DECISION THEORETIC GENERALIZATION

135

Suppose now that hf (x i){ yi for some example i. Then,

by definition of hf,

P, and we focus only on the minimization of the empirical
MSE:

T
:
t=1

T
:t ht(x i , yi)(cid:29) :
t=1

:tht(xi , hf (xi)),

1
N

N
:
i=1

(h(xi)& yi)2.

Using techniques similar to those outlined in Section 4.3,
the true MSE given in Eq. (25) can be related to the empiri-
cal MSE.

To derive a boosting algorithm in this context, we reduce
the given regression problem to a binary classification
problem, and then apply AdaBoost. As was done for the
reductions used in the proofs of Theorems 10 and 11, we
mark with tildes all variables in the reduced (AdaBoost)
space. For each example (xi , yi) in the training set, we
define a continuum of examples indexed by pairs (i, y) for
all y # [0, 1]: the associated instance is x~ i, y=(xi , y), and
the label is y~ i, y= (cid:26) y(cid:30) yi(cid:25). (Recall that (cid:26)?(cid:25) is 1 if predicate
? holds and 0 otherwise.) Although it is obviously infeasible
to explicitly maintain an infinitely large training set, we will
see later how this method can be implemented efficiently.
Also, although the results of Section 4 only dealt with
finitely large training sets, the extension to infinite training
sets is straightforward.

Thus, informally, each instance (xi , y i) is mapped to an
infinite set of binary questions, one for each y # Y, and each
of the form: ‘‘Is the correct label yi bigger or smaller than y?’’
In a similar manner, each hypothesis h : X (cid:20) Y is reduced
to a binary-valued hypothesis h(cid:25) : X_Y (cid:20) [0, 1] defined by
the rule

h(cid:25) (x, y)= (cid:26) y(cid:30)h(x)(cid:25).

Thus, h(cid:25) attempts to answer these binary questions in a
natural way using the estimated value h(x).

Finally, as was done for classification problems, we
assume we are given a distribution D over the training set;
ordinarily, this will be uniform so that D(i)=1(cid:18)N. In our
reduction, this distribution is mapped to a density D(cid:25) over
pairs (i, y) in such a way that minimization of classification
error in the reduced space is equivalent to minimization of
MSE for the original problem. To do this, we define

D(cid:25) (i, y)=

D(i) | y& yi |
Z

where Z is a normalization constant:

N
Z= :
i=1

1

| y& yi | dy.

D(i) |

0

It is straightforward to show that 1(cid:18)4(cid:29)Z(cid:29)1(cid:18)2.

where :t=ln(1(cid:18);t). This implies that

T
:
t=1

:th(cid:25) t(i, hf (xi))= 1

T
2 :
t=1

:t (1&ht(x i , y i)+ht(x i , hf (xi)))

(cid:30) 1

T
2 :
t=1

: t

so h(cid:25) f (i, hf (xi))=1 by definition of h(cid:25) f .

Therefore,

PritD[hf (x i){ y i](cid:29)PritD[_y{ yi : h(cid:25) f (i, y)=1].

Since all AdaBoost instances have a 0-label, and by defini-
tion of D(cid:25) , the error of h(cid:25) f is

Pr (i, y)tD(cid:25) [h(cid:25) f (i, y)=1]

(cid:30)

1
k&1

PritD[_y{ yi : h(cid:25) f (i, y)=1].

Applying Theorem 6 to bound the error of h(cid:25) f,
completes the proof.

K

this

Although we omit

the bound for
AdaBoost.M2 can be improved by a factor of two in a
manner similar to that described in Section 4.5.

the details,

5.3. Boosting Regression Algorithms

In this section we show how boosting can be used for a
regression problem. In this setting,
the label space is
Y=[0, 1]. As before, the learner receives examples (x, y)
chosen at random according to some distribution P, and its
goal is to find a hypothesis h : X (cid:20) Y which, given some x
value, predicts approximately the value y that is likely to be
seen. More precisely, the learner attempts to find an h with
small mean squared error (MSE):

E(x, y)t P[(h(x)& y) 2].

(25)

Our methods can be applied to any reasonable bounded
error measure, but, for the sake of concreteness, we concen-
trate here on the squared error measure.

Following our approach for classification problems, we
assume that the leaner has been provided with a training set
(x1 , y1), ..., (xN , yN) of examples distributed according to

File: 571J 150417 . By:CV . Date:28:07:01 . Time:05:54 LOP8M. V8.0. Page 01:01
Codes: 5122 Signs: 3534 . Length: 56 pic 0 pts, 236 mm



<!-- pdf-page: 18 -->
136

FREUND AND SCHAPIRE

Algorithm AdaBoost.R
Input: sequence of N examples ( (x1 , y 1). .., (xN , yN)) with labels
yi # Y=[0, 1]

distribution D over the examples
weak learning algorithm WeakLearn
integer T specifying number of iterations

Initialize the weight vector:

w 1

i, y=

D(i) | y& yi |
Z

for i=1, ..., N, y # Y, where

N
Z= :
i=1

D(i) |

1

0

| y& yi | dy.

Do for t=1, 2, ..., T

1. Set

pt=

wt
0 wt
i=1 (cid:30) 1

(cid:29) N

i, y dy

.

2. Call WeakLearn, providing it with the density pt; get back a

hypothesis ht : X_Y.

3. Calculate the loss of ht :

ht(xi)

N
=t= :

i=1}|

yi

p t

i, y dy}.

If =t>1(cid:18)2, then set T=t&1 and abort the loop.

4. Set ;t==t (cid:18)(1&=t).

5. Set the new weights vector to be

w t+1

i, y ={w t

w t

i, y
i, y ;t

if yi(cid:29) y(cid:29)ht(xi) or ht(xi)(cid:29) y(cid:29) yi
otherwise.

for i=1, ..., N, y # Y.

Output the hypothesis

hf (x)=inf {y # Y : :

t : ht(x)(cid:29) y

log(1(cid:18); t)(cid:30) 1

2 :
t

log(1(cid:18);t)= .

FIG. 5. An extension of AdaBoost to regression problems.

The

following theorem describes our performance
guarantee for AdaBoost.R. The proof
follows from the
reduction described above coupled with a direct application
of Theorem 6.

Theorem 12. Suppose the weak learning algorithm
WeakLearn, when called by AdaBoost.R, generates hypo-
theses with errors =1 , ..., =T , where =t is as defined in Fig. 5.
Then the mean squared error ==EitD[(hf (x i)& yi)2] of

If we calculate the binary error of h(cid:25) with respect to the
density D(cid:25) , we find that, as desired, it is directly proportional
to the mean squared error:

N
:
i=1

1

0

|

| y~ i, y&h(cid:25) (x~ i, y)| D(cid:25) (i, y) dy

=

1
Z

N
:
i=1

D(i) }|

h(xi)

yi

| y& yi | dy}

=

1
2Z

N
:
i=1

D(i)(h(xi)& yi)2.

The constant of proportionality is 1(cid:18)(2Z) # [1, 2].

Unravelling this reduction, we obtain the regression
boosting procedure AdaBoost.R shown in Fig. 5. As
prescribed by the reduction, AdaBoost.R maintains a weight
wt
i, y for each instance i and label y # Y. The initial weight
function w1 is exactly the density D(cid:25) defined above. By nor-
malizing the weights wt, a density pt is defined at Step 1 and
provided to the weak learner at Step 2. The goal of the weak
learner is to find a hypothesis ht : X (cid:20) Y that minimizes the
loss =t defined in Step 3. Finally, at Step 5, the weights are
updated as prescribed by the reduction.

The definition of =t at Step 3 follows directly from the
reduction above; it is exactly the classification error of h(cid:25) f in
the reduced space. Note that, similar to AdaBoost.M2,
AdaBoost.R not only varies the distribution over the
examples (xi , yi), but also modifies from round to round the
definition of the loss suffered by a hypothesis on each
example. Thus, although our ultimate goal is minimization
of the squared error, the weak learner must be able to
handle loss functions that are more complicated than MSE.
The final hypothesis hf also is consistent with the reduc-
tion. Each reduced weak hypothesis h(cid:25) f (x, y)
is non-
decreasing as a function of y. Thus, the final hypothesis h(cid:25) f
generated by AdaBoost in the reduced space, being the
threshold of a weighted sum of these hypotheses, also is
non-decreasing as a function of y. As the output of h(cid:25) f is
binary, this implies that for every x there is one value of y
for which h(cid:25) f (x, y$)=0 for all y$< y and h(cid:25) f (x, y$)=1 for all
y$> y. This is exactly the value of y given by hf (x) as defined
in the figure. Note that hf is actually computing a weighted
median of the weak hypotheses.

i, y is a piece-wise linear function. For t=1, w 1

At first, it might seem impossible to maintain weights w t
i, y
over an uncountable set of points. However, on closer
inspection, it can be seen that, when viewed as a function of
y, w t
i, y has two
linear pieces, and each update at Step 5 potentially breaks
one of the pieces in two at the point ht(x i). Initializing,
storing and updating such piece-wise linear functions are
all straightforward operations. Also, the integrals which
appear in the figure can be evaluated explicitly since these
only involve integration of piece-wise linear functions.

File: 571J 150418 . By:CV . Date:28:07:01 . Time:05:54 LOP8M. V8.0. Page 01:01
Codes: 5416 Signs: 3774 . Length: 56 pic 0 pts, 236 mm



<!-- pdf-page: 19 -->
A DECISION THEORETIC GENERALIZATION

137

an outcome |t # 0, the learner and each expert i incur loss
*($t, |t) and *(= t
i , |t), respectively. The goal of the learning
algorithm is to generate decisions in such a way that its
cumulative loss will not be much larger than the cumulative
loss of the best expert. The following four properties are
assumed to hold:

1. 2 is a compact topological space.
2. For each |, the function $ (cid:20) *($, |) is continuous.
3. There exists $ such that, for all |, *($, |)<(cid:31).

4. There exists no $ such that, for all |, *($, |)=0.

We now give Vovk’s main result [24]. Let a decision
problem defined by 0, 2 and * obey Assumptions 1(cid:21)4. Let
c and a be positive real numbers. We say that the decision
problem is (c, a)-bounded if there exists an algorithm A such
that for any finite set of experts and for any finite sequence
of trials, the cumulative loss of the algorithm is bounded by

T
:
t=1

*($t, |t)(cid:29)c min

i

T
:
t=1

*(= t

i , | t)+a ln N,

where N is the number of experts.

We say that a distribution D is simple if it is non-zero on
a finite set denoted dom(D). Let S be the set of simple dis-
tributions over 2. Vovk defines the following function
c : (0, 1) (cid:20) [0, (cid:31)] which characterizes the hardness of any
decision problem:

c( ;)= sup
D # S

inf
$ # 2

sup
| # 0

*($, |)
log ; (cid:29) = # dom(D) ;*(=, |)D(=)

.

(27)

He then proves the following powerful theorem:

Theorem 13 (Vovk). A decision problem is

(c, a)-
for all ; # (0, 1), c(cid:30)c( ;) or

bounded if and only if
a(cid:30)c( ;)(cid:18)ln(1(cid:18);).

Proof of Theorem 3. The proof consists of the following
three steps: We first define a decision problem that conforms
to Vovk’s framework. We then show a lower bound on the
function c( ;) for this problem. Finally, we show how any
algorithm A for the on-line allocation problem can be used
to generate decisions in the defined problem, and so we get
from Theorem 13 a lower bound on the worst case
cumulative loss of A.

The decision problem is defined as follows. We fix an
integer K>1 and set 2=SK where SK is the K dimensional
simplex, i.e., SK=[x # [0, 1] K : (cid:29) K
i=1 xi=1]. We set 0 to
be the set of unit vectors in RK, i.e., 0=[e1 , ..., eK] where
ei # [0, 1] K has a 1 in the ith component, and 0 in all other
components. Finally, we define the loss function to be
*($, ei).$ } ei=$i . One can easily verify that these defini-
tions conform to Assumptions 1(cid:21)4.

the final hypothesis hf output by AdaBoost.R is bounded
above by

T
=(cid:29)2T ‘
t=1

- =t(1&=t).

(26)

An unfortunate property of this setup is that there is no
trivial way to generate a hypothesis whose loss is 1(cid:18)2. This
is a similar situation to the one we encountered with algo-
rithm AdaBoost.M1. A remedy to this problem might be to
allow weak hypotheses from a more general class of
functions. One simple generalization is to allow for weak
hypotheses that are defined by two functions: h : X (cid:20) [0, 1]
as before, and } : X (cid:20) [0, 1] which associates a measure of
confidence to each prediction of h. The reduced hypothesis
which we associate with this pair of functions is

h(cid:25) (x, y)={(1+}(x))(cid:18)2

(1&}(x))(cid:18)2

h(x)(cid:30) y

if
otherwise.

These hypotheses are used in the same way as the ones
defined before and a slight variation of algorithm
AdaBoost.R can be used to boost the accuracy of these more
general weak learners (details omitted). The advantage of
this variant is that any hypothesis for which }(x) is identi-
cally zero has pseudo-loss exactly 1(cid:18)2 and slight deviations
from this hypothesis can be used to encode very weak
predictions.

The method presented in this section for boosting with
square loss can be used with any reasonable bounded loss
function L : Y_Y (cid:20) [0, 1]. Here, L( y$, y) is a measure of
the ‘‘discrepancy’’ between the observed label y and a
predicted label y$; for instance, above we used L( y$, y)=
( y$& y)2. The goal of learning is to find a hypothesis h with
small average loss E(x, y)t P[L(h(x), y)]. Assume, for any
y, that L( y, y)=0 and that L( y$, y) is differentiable with
respect to y$, non-increasing for y$(cid:29) y and non-decreasing
for y$(cid:30) y. Then, to modify AdaBoost.R to handle such a loss
function, we need only replace | y& yi | in the initialization
step with |(cid:28)L( y, yi)(cid:18)(cid:28)y|. The rest of the algorithm is
unchanged, and the modifications needed for the analysis
are straightforward.

APPENDIX: PROOF OF THEOREM 3

We start with a brief review of a framework used by Vovk
[24], which is very similar to the framework used in
Section 3. In this framework, an on-line decision problem
consists of a decision space 2, an outcome space 0 and a
loss function *: 2_0 (cid:20) [0, (cid:31)], which associates a loss to
each decision and outcome pair. At each trial t the learning
algorithm receives the decisions = t
N # 2 of N experts,
and then generates its own decision $t # 2. Upon receiving

1 , ..., = t

File: 571J 150419 . By:CV . Date:28:07:01 . Time:05:54 LOP8M. V8.0. Page 01:01
Codes: 5890 Signs: 4625 . Length: 56 pic 0 pts, 236 mm



<!-- pdf-page: 20 -->
138

FREUND AND SCHAPIRE

To prove a lower bound on c( ;) for this decision problem
we choose a particular simple distribution over the decision
space 2. Let D be the uniform distribution over the unit vec-
tors, i.e., dom(D)=[e1 , ..., eK]. For this distribution, we
can explicitly calculate

then the decision problem is (c, a))-bounded. On the other
hand, using the lower bound given by Theorem 13 and the
lower bound on c( ;) given in Eq. (31), we get that for any
K and any ;, either

c( ;)(cid:30) inf
$ # 2

sup
| # 0

*($, |)
log; (cid:29) = # dom(D) ; *(=, |)D(=)

.

(28)

First, it is easy to see that the denominator in Eq. (28) is a
constant:

c(cid:30)

ln(1(cid:18);)
K ln(1&(1&;)(cid:18)K)

or a(cid:30)

1
K ln(1&(1&;)(cid:18)K)

. (32)

As K is a free parameter we can let K (cid:20) (cid:31) and the
denominators in Eq. (22) become 1&; which gives the
statement of the theorem. K

:
= # dom(D)

;*(=, |)D(=)=

;
K

+

K&1
K

.

(29)

ACKNOWLEDGMENTS

For any probability vector $ # 2, there must exist one com-
ponent i for which $i(cid:29)1(cid:18)K. Thus

Thanks are due to Corinna Cortes, Harris Drucker, David Helmbold,
Keith Messer, Volodya Vovk, and Manfred Warmuth for helpful discus-
sions.

REFERENCES

1. E. B. Baum and D. Haussler, What size net gives valid generalization?,
Adv. Neural Inform. Process. Systems I,’’ pp. 81(cid:21)90, Morgan Kauf-
mann, 1989.

2. D. Blackwell, An analog of the minimax theorem for vector payoffs,

Pacific J. Math. 6, No. 1 (Spring 1956), 1(cid:21)8.

3. L. Breiman, Bias, variance, and arcing classifiers, Technical Report
*460, Statistics Dept., University of California, 1996; available from
ftp:(cid:18)(cid:18)ftp.stat.berkeley.edu(cid:18)pub(cid:18)users(cid:18)breiman(cid:18)arcall.ps.Z., 1996.

4. N. Cesa-Bianchi, Y. Freund, D. P. Helmhold, D. Haussler, R. E.
Schapire, and M. K. Warmuth, How to use expert advice,
in
‘‘Proceedings of the Twenty-Fifth Annual ACM Symposium on the
Theory of Computing, 1993,’’ pp. 382(cid:21)391.

5. T. H. Chung, Approximate methods for sequential decision making
using expert advice, in ‘‘Proceedings of the Seventh Annual ACM Con-
ference on Computational Learning Theory, 1994,’’ pp. 183(cid:21)189.
6. T. M. Cover, Universal portfolios, Math. Finance 1, No. 1 (Jan. 1991),

1(cid:21)29.

7. T. G. Dietterich and G. Bakiri, Solving multiclass learning problems
via error-correcting output codes, J. Artif. Intell. Res. 2 (January 1995),
263(cid:21)286.

8. H. Drucker and C. Cortes, Boosting decision trees, Adv. Neural Inform.

Process. Systems 8 (1996).

9. H. Drucker, R. Schapire, and P. Simard, Boosting performance in
neural networks, Int. J. Pattern Recognition Artif. Intell. 7, No. 4
(1993), 705(cid:21)719.

10. Y. Freund,

‘‘Data Filtering and Distribution Modeling Algorithms
for Machine Learning,’’ Ph.D. thesis, University of California at
Santa Cruz, 1993; retrievable from ftp.cse.ucsc.edu(cid:18)pub(cid:18)tr(cid:18)ucsc-crl-93-
37.ps.Z.

11. Y. Freund, Boosting a weak learning algorithm by majority, Inform.
and Comput. 121, No. 2 (September 1995), 256(cid:21)285; an extended
abstract appeared in ‘‘Proceedings of the Third Annual Workshop on
Computational Learning Theory, 1990.’’

12. Y. Freund and R. E. Schapire, Experiments with a new boosting algo-
rithm, in ‘‘Machine Learning: Proceedings of the Thirteenth Interna-
tional Conference, 1996,’’ pp. 148(cid:21)156.

13. Y. Freund and R. E. Schapire, Game theory, on-line prediction and
the Ninth Annual Conference on

boosting,
Computational Learning Theory, 1996,’’ pp. 325(cid:21)332.

in ‘‘Proceedings of

inf
$ # 2

sup
| # 0

*($, |)=1(cid:18)K.

Combining Eqs. (28), (29), (30), we get that

c(;)(cid:30)

ln(1(cid:18);)
K ln(1&(1&;)(cid:18)K)

.

(30)

(31)

We now show how an on-line allocation algorithm A can
be used as a subroutine for solving this decision problem.
We match each of the N experts of the decision problem
with a strategy of the allocation problem. Each iteration t of
the decision problem proceeds as follows.

1. Each of the N experts generates a decision = t
i # SK.
2. The algorithm A generates a distribution pt # SN .
3. The learner chooses the decision $t=(cid:29) N
i =t
i .
4. The outcome |t # 0 is generated.
5. The learner incurs loss $t } |t, and each expert suffers

i=1 p t

loss = t

i } |t.

6. Algorithm A receives the loss vector lt where
i == t
lt

i } |t, and incurs loss

N
pt } lt= :
i=1

i(= t
p t

i } |t)

N

=\ :

i=1

i+ } |t=$ t } |t.
i = t
p t

Observe that the loss incurved by the learner in the deci-
sion problem is equal to the loss incurred by A. Thus, if for
algorithm A we have an upper bound of the form

LA(cid:29)c min

i

Li+a ln N,

File: 571J 150420 . By:CV . Date:28:07:01 . Time:05:54 LOP8M. V8.0. Page 01:01
Codes: 8609 Signs: 4174 . Length: 56 pic 0 pts, 236 mm



<!-- pdf-page: 21 -->
A DECISION THEORETIC GENERALIZATION

139

14. J. Hannan, Approximation to Bayes risk in repeated play, ‘‘Contribu-
tions to the Theory of Games,’’ Vol. III (M. Dresher, A. W. Tucker,
and P. Wolfe, Eds.), pp. 97(cid:21)139, Princeton Univ. Press, Princeton, NJ,
1957.

15. D. Haussler, J. Kivinen, and M. K. Warmuth, Tight worst-case loss
bounds for predicting with expert advice, in ‘‘Computational Learning
Theory: Second European Conference, EuroCOLT ’95,’’ pp. 69(cid:21)83,
Springer-Verlag, New York(cid:18)Berlin, 1995.

EuroCOLT ’93,’’ pp. 109(cid:21)120, Springer-Verlag, New York(cid:18)Berlin,
1994.

20. N. Littlestone and M. K. Warmuth, The weighted majority algorithm,

Inform. and Comput. 108 (1994), 212(cid:21)261.

21. J. R. Quinlan, Bagging, boosting, and C4.5, in ‘‘Proceedings, Four-

teenth National Conference on Artificial Intelligence, 1996.’’

22. R. E. Schapire, The strength of weak learnability, Machine Learning 5,

No. 2 (1990), 197(cid:21)227.

16. J. C. Jackson and M. W. Craven, Learning sparse perceptrons, Adv.

23. V. N. Vapnik, ‘‘Estimation of Dependences Based on Empirical Data,’’

Neural Inform. Process. Systems 8 (1996).

Springer-Verlag, New York(cid:18)Berlin, 1982.

17. M. Kearns, Y. Mansour, A. Y. Ng, and D. Ron, An experimental and
theoretical comparison of model selection methods, in ‘‘Proceedings of
the Eighth Annual Conference on Computational Learning Theory,
1995.’’

18. M. J. Kearns and U. V. Vazirani, ‘‘An Introduction to Computational

Learning Theory,’’ MIT Press, Cambridge, MA, 1994.

19. J. Kivinen and M. K. Warmuth, Using experts for predicting
‘‘Computational Learning Theory:

continuous

outcomes,

in

24. V. G. Vovk, A game of prediction with expert advice, in ‘‘Proceedings
of the Eighth Annual Conference on Computational Learning Theory,
1995.’’

25. V. G. Vovk, Aggregating strategies,

in ‘‘Proceedings of the Third
Annual Workshop on Computational Learning Theory, 1990,’’
pp. 321(cid:21)383.

26. R. S. Wenocur and R. M. Dudley, Some special Vapnik(cid:21)Chervonenkis

classes, Discrete Mathematics 33 (1981), 313(cid:21)318.

File: 571J 150421 . By:CV . Date:28:07:01 . Time:06:07 LOP8M. V8.0. Page 01:01
Codes: 5332 Signs: 2008 . Length: 56 pic 0 pts, 236 mm


