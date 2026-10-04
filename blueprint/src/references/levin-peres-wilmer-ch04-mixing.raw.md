<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: 70350d84fb7f89c058d2f56d7fc677ac57c8363f8e95d8df52de4d0e00d22763 -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
CHAPTER 4

Introduction to Markov Chain Mixing

We are now ready to discuss the long-term behavior of ﬁnite Markov chains.
Since we are interested in quantifying the speed of convergence of families of Markov
chains, we need to choose an appropriate metric for measuring the distance between
distributions.

First we deﬁne total variation distance and give several characterizations
of it, all of which will be useful in our future work. Next we prove the Convergence
Theorem (Theorem 4.9), which says that for an irreducible and aperiodic chain
the distribution after many steps approaches the chain’s stationary distribution,
in the sense that the total variation distance between them approaches 0. In the
rest of the chapter we examine the eﬀects of the initial distribution on distance
from stationarity, deﬁne the mixing time of a chain, consider circumstances under
which related chains can have identical mixing, and prove a version of the Ergodic
Theorem (Theorem C.1) for Markov chains.

4.1. Total Variation Distance

The total variation distance between two probability distributions µ and ν

on X is deﬁned by

(cid:107)µ − ν(cid:107)TV = max
A⊆X
This deﬁnition is explicitly probabilistic:
the distance between µ and ν is the
maximum diﬀerence between the probabilities assigned to a single event by the
two distributions.

|µ(A) − ν(A)| .

(4.1)

Example 4.1. Recall the coin-tossing frog of Example 1.1, who has probability
p of jumping from east to west and probability q of jumping from west to east. The
(cid:17)
(cid:1) and its stationary distribution is π =
transition matrix is (cid:0) 1−p p
.
Assume the frog starts at the east pad (that is, µ0 = (1, 0)) and deﬁne

(cid:16) q
p+q , p

p+q

1−q

q

∆t = µt(e) − π(e).

Since there are only two states, there are only four possible events A ⊆ X . Hence
it is easy to check (and you should) that

(cid:107)µt − π(cid:107)TV = |∆t| = |P t(e, e) − π(e)| = |π(w) − P t(e, w)|.
We pointed out in Example 1.1 that ∆t = (1 − p − q)t∆0. Hence for this two-
state chain, the total variation distance decreases exponentially fast as t increases.
(Note that (1 − p − q) is an eigenvalue of P ; we will discuss connections between
eigenvalues and mixing in Chapter 12.)

The deﬁnition of total variation distance (4.1) is a maximum over all subsets
of X , so using this deﬁnition is not always the most convenient way to estimate

47



<!-- pdf-page: 2 -->
48

4. INTRODUCTION TO MARKOV CHAIN MIXING

Figure 4.1. Recall that B = {x : µ(x) ≥ ν(x)}. Region I has
area µ(B) − ν(B). Region II has area ν(Bc) − µ(Bc). Since the
total area under each of µ and ν is 1, regions I and II must have
the same area—and that area is (cid:107)µ − ν(cid:107)TV.

the distance. We now give three extremely useful alternative characterizations.
Proposition 4.2 reduces total variation distance to a simple sum over the state
space. Proposition 4.7 uses coupling to give another probabilistic interpretation:
(cid:107)µ − ν(cid:107)TV measures how close to identical we can force two random variables re-
alizing µ and ν to be.

Proposition 4.2. Let µ and ν be two probability distributions on X . Then

(cid:107)µ − ν(cid:107)TV =

1
2

(cid:88)

x∈X

|µ(x) − ν(x)| .

(4.2)

Proof. Let B = {x : µ(x) ≥ ν(x)} and let A ⊂ X be any event. Then

µ(A) − ν(A) ≤ µ(A ∩ B) − ν(A ∩ B) ≤ µ(B) − ν(B).

(4.3)

The ﬁrst inequality is true because any x ∈ A ∩ Bc satisﬁes µ(x) − ν(x) < 0, so the
diﬀerence in probability cannot decrease when such elements are eliminated. For
the second inequality, note that including more elements of B cannot decrease the
diﬀerence in probability.

By exactly parallel reasoning,

ν(A) − µ(A) ≤ ν(Bc) − µ(Bc).

(4.4)

Fortunately, the upper bounds on the right-hand sides of (4.3) and (4.4) are actually
the same (as can be seen by subtracting them; see Figure 4.1). Furthermore, when
we take A = B (or Bc), then |µ(A) − ν(A)| is equal to the upper bound. Thus

(cid:107)µ − ν(cid:107)TV =

1
2

[µ(B) − ν(B) + ν(Bc) − µ(Bc)] =

1
2

(cid:88)

x∈X

|µ(x) − ν(x)|.

Remark 4.3. The proof of Proposition 4.2 also shows that

(cid:107)µ − ν(cid:107)TV =

(cid:88)

[µ(x) − ν(x)],

x∈X
µ(x)≥ν(x)

(cid:4)

(4.5)

IIIBBcΜΝ

<!-- pdf-page: 3 -->
4.2. COUPLING AND TOTAL VARIATION DISTANCE

49

which is a useful identity.

Remark 4.4. From Proposition 4.2 and the triangle inequality for real num-
bers, it is easy to see that total variation distance satisﬁes the triangle inequality:
for probability distributions µ, ν and η,

(4.6)
Proposition 4.5. Let µ and ν be two probability distributions on X . Then the

(cid:107)µ − ν(cid:107)TV ≤ (cid:107)µ − η(cid:107)TV + (cid:107)η − ν(cid:107)TV .

total variation distance between them satisﬁes

(cid:107)µ − ν(cid:107)TV =

1
2

sup

(cid:40)

(cid:88)

x∈X

f (x)µ(x) −

(cid:88)

x∈X

f (x)ν(x) : max
x∈X

|f (x)| ≤ 1

.

(4.7)

(cid:41)

Proof. If maxx∈X |f (x)| ≤ 1, then
(cid:12)
(cid:12)
(cid:12)
(cid:12)
(cid:12)

f (x)µ(x) −

f (x)ν(x)

(cid:88)

(cid:88)

1
2

(cid:12)
(cid:12)
(cid:12)
(cid:12)
(cid:12)

≤

1
2

x∈X

x∈X
Thus, the right-hand side of (4.7) is at most (cid:107)µ − ν(cid:107)TV.

x∈X

(cid:88)

|µ(x) − ν(x)| = (cid:107)µ − ν(cid:107)TV .

For the other direction, deﬁne

f (cid:63)(x) =

(cid:40)
1
−1

if µ(x) ≥ ν(x),
if µ(x) < ν(x).

Then
(cid:34)

1
2

(cid:88)

f (cid:63)(x)µ(x) −

x∈X

(cid:35)
f (cid:63)(x)ν(x)

=

(cid:88)

x∈X

1
2

(cid:88)

x∈X



f (cid:63)(x)[µ(x) − ν(x)]



=

1
2





(cid:88)

[µ(x) − ν(x)] +

(cid:88)

[ν(x) − µ(x)]





.

x∈X
µ(x)≥ν(x)

x∈X
ν(x)>µ(x)

Using (4.5) shows that the right-hand side above equals (cid:107)µ − ν(cid:107)TV. Hence the
(cid:4)
right-hand side of (4.7) is at least (cid:107)µ − ν(cid:107)TV.

4.2. Coupling and Total Variation Distance

A coupling of two probability distributions µ and ν is a pair of random vari-
ables (X, Y ) deﬁned on a single probability space such that the marginal distribu-
tion of X is µ and the marginal distribution of Y is ν. That is, a coupling (X, Y )
satisﬁes P{X = x} = µ(x) and P{Y = y} = ν(y).

Coupling is a general and powerful technique; it can be applied in many diﬀer-
ent ways. Indeed, Chapters 5 and 14 use couplings of entire chain trajectories to
bound rates of convergence to stationarity. Here, we oﬀer a gentle introduction by
showing the close connection between couplings of two random variables and the
total variation distance between those variables.

Example 4.6. Let µ and ν both be the “fair coin” measure giving weight 1/2

to the elements of {0, 1}.

(i) One way to couple µ and ν is to deﬁne (X, Y ) to be a pair of independent

coins, so that P{X = x, Y = y} = 1/4 for all x, y ∈ {0, 1}.



<!-- pdf-page: 4 -->
50

4. INTRODUCTION TO MARKOV CHAIN MIXING

(ii) Another way to couple µ and ν is to let X be a fair coin toss and deﬁne
Y = X. In this case, P{X = Y = 0} = 1/2, P{X = Y = 1} = 1/2, and
P{X (cid:54)= Y } = 0.

Given a coupling (X, Y ) of µ and ν, if q is the joint distribution of (X, Y ) on

X × X , meaning that q(x, y) = P{X = x, Y = y}, then q satisﬁes

and

(cid:88)

y∈X

(cid:88)

x∈X

q(x, y) =

q(x, y) =

(cid:88)

y∈X

(cid:88)

x∈X

P{X = x, Y = y} = P{X = x} = µ(x)

P{X = x, Y = y} = P{Y = y} = ν(y).

Conversely, given a probability distribution q on the product space X × X which
satisﬁes

(cid:88)

q(x, y) = µ(x)

and

q(x, y) = ν(y),

(cid:88)

y∈X

x∈X

there is a pair of random variables (X, Y ) having q as their joint distribution – and
consequently this pair (X, Y ) is a coupling of µ and ν. In summary, a coupling
can be speciﬁed either by a pair of random variables (X, Y ) deﬁned on a common
probability space or by a distribution q on X × X .

Returning to Example 4.6, the coupling in part (i) could equivalently be spec-

iﬁed by the probability distribution q1 on {0, 1}2 given by

q1(x, y) =

1
4

for all (x, y) ∈ {0, 1}2.

Likewise, the coupling in part (ii) can be identiﬁed with the probability distribution
q2 given by

q2(x, y) =

(cid:40) 1
2
0

if (x, y) = (0, 0), (x, y) = (1, 1),
if (x, y) = (0, 1), (x, y) = (1, 0).

Any two distributions µ and ν have an independent coupling. However, when µ
and ν are not identical, it will not be possible for X and Y to always have the same
value. How close can a coupling get to having X and Y identical? Total variation
distance gives the answer.

Proposition 4.7. Let µ and ν be two probability distributions on X . Then

(cid:107)µ − ν(cid:107)TV = inf {P{X (cid:54)= Y } : (X, Y ) is a coupling of µ and ν} .

(4.8)

Remark 4.8. We will in fact show that there is a coupling (X, Y ) which attains

the inﬁmum in (4.8). We will call such a coupling optimal .

Proof. First, we note that for any coupling (X, Y ) of µ and ν and any event

A ⊂ X ,

µ(A) − ν(A) = P{X ∈ A} − P{Y ∈ A}

≤ P{X ∈ A, Y (cid:54)∈ A}
≤ P{X (cid:54)= Y }.

(4.9)

(4.10)

(4.11)

(Dropping the event {X (cid:54)∈ A, Y ∈ A} from the second term of the diﬀerence gives
the ﬁrst inequality.) It immediately follows that

(cid:107)µ − ν(cid:107)TV ≤ inf {P{X (cid:54)= Y } : (X, Y ) is a coupling of µ and ν} .

(4.12)



<!-- pdf-page: 5 -->
4.2. COUPLING AND TOTAL VARIATION DISTANCE

51

Figure 4.2. Since each of regions I and II has area (cid:107)µ − ν(cid:107)TV
and µ and ν are probability measures, region III has area 1 −
(cid:107)µ − ν(cid:107)TV.

It will suﬃce to construct a coupling for which P{X (cid:54)= Y } is exactly equal to
(cid:107)µ − ν(cid:107)TV. We will do so by forcing X and Y to be equal as often as they possibly
can be. Consider Figure 4.2. Region III, bounded by µ(x)∧ν(x) = min{µ(x), ν(x)},
can be seen as the overlap between the two distributions. Informally, our coupling
proceeds by choosing a point in the union of regions I and III, and setting X to be
the x-coordinate of this point. If the point is in III, we set Y = X and if it is in I,
then we choose independently a point at random from region II, and set Y to be
the x-coordinate of the newly selected point. In the second scenario, X (cid:54)= Y , since
the two regions are disjoint.

More formally, we use the following procedure to generate X and Y . Let

p =

(cid:88)

x∈X

µ(x) ∧ ν(x).

Write

(cid:88)

x∈X

µ(x) ∧ ν(x) =

(cid:88)

µ(x) +

(cid:88)

ν(x).

x∈X ,
µ(x)≤ν(x)

x∈X ,
µ(x)>ν(x)

Adding and subtracting (cid:80)

x : µ(x)>ν(x) µ(x) to the right-hand side above shows that

(cid:88)

x∈X

µ(x) ∧ ν(x) = 1 −

(cid:88)

[µ(x) − ν(x)].

x∈X ,
µ(x)>ν(x)

By equation (4.5) and the immediately preceding equation,

(cid:88)

x∈X

µ(x) ∧ ν(x) = 1 − (cid:107)µ − ν(cid:107)TV = p.

(4.13)

Flip a coin with probability of heads equal to p.

(i) If the coin comes up heads, then choose a value Z according to the probability

distribution

and set X = Y = Z.

γIII(x) =

µ(x) ∧ ν(x)
p

,

IIIIIIΜΝ

<!-- pdf-page: 6 -->
52

4. INTRODUCTION TO MARKOV CHAIN MIXING

(ii) If the coin comes up tails, choose X according to the probability distribution

γI(x) =

(cid:40) µ(x)−ν(x)
(cid:107)µ−ν(cid:107)TV
0

if µ(x) > ν(x),

otherwise,

and independently choose Y according to the probability distribution

γII(x) =

(cid:40) ν(x)−µ(x)
(cid:107)µ−ν(cid:107)TV
0

if ν(x) > µ(x),

otherwise.

Note that (4.5) ensures that γI and γII are probability distributions.

Clearly,

pγIII + (1 − p)γI = µ,
pγIII + (1 − p)γII = ν,

so that the distribution of X is µ and the distribution of Y is ν. Note that in the
case that the coin lands tails up, X (cid:54)= Y since γI and γII are positive on disjoint
subsets of X . Thus X = Y if and only if the coin toss is heads. We conclude that

P{X (cid:54)= Y } = (cid:107)µ − ν(cid:107)TV .

(cid:4)

4.3. The Convergence Theorem

We are now ready to prove that irreducible, aperiodic Markov chains converge
to their stationary distributions—a key step, as much of the rest of the book will be
devoted to estimating the rate at which this convergence occurs. The assumption
of aperiodicity is indeed necessary—recall the even n-cycle of Example 1.4.

As is often true of such fundamental facts, there are many proofs of the Conver-
gence Theorem. The one given here decomposes the chain into a mixture of repeated
independent sampling from the stationary distribution and another Markov chain.
See Exercise 5.1 for another proof using two coupled copies of the chain.

Theorem 4.9 (Convergence Theorem). Suppose that P is irreducible and ape-
riodic, with stationary distribution π. Then there exist constants α ∈ (0, 1) and
C > 0 such that

(cid:13)P t(x, ·) − π(cid:13)
(cid:13)

(cid:13)TV ≤ Cαt.

max
x∈X

(4.14)

Proof. Since P is irreducible and aperiodic, by Proposition 1.7 there exists
an r such that P r has strictly positive entries. Let Π be the matrix with |X | rows,
each of which is the row vector π. For suﬃciently small δ > 0, we have

for all x, y ∈ X . Let θ = 1 − δ. The equation

P r(x, y) ≥ δπ(y)

P r = (1 − θ)Π + θQ

(4.15)

deﬁnes a stochastic matrix Q.

It is a straightforward computation to check that M Π = Π for any stochastic

matrix M and that ΠM = Π for any matrix M such that πM = π.

Next, we use induction to demonstrate that

P rk = (cid:0)1 − θk(cid:1) Π + θkQk

(4.16)



<!-- pdf-page: 7 -->
4.4. STANDARDIZING DISTANCE FROM STATIONARITY

53

for k ≥ 1. If k = 1, this holds by (4.15). Assuming that (4.16) holds for k = n,

P r(n+1) = P rnP r = [(1 − θn) Π + θnQn] P r.

(4.17)

Distributing and expanding P r in the second term (using (4.15)) gives

P r(n+1) = [1 − θn] ΠP r + (1 − θ)θnQnΠ + θn+1QnQ.

(4.18)

Using that ΠP r = Π and QnΠ = Π shows that

P r(n+1) = (cid:2)1 − θn+1(cid:3) Π + θn+1Qn+1.
This establishes (4.16) for k = n + 1 (assuming it holds for k = n), and hence it
holds for all k.

(4.19)

Multiplying by P j and rearranging terms now yields
P rk+j − Π = θk (cid:0)QkP j − Π(cid:1) .
To complete the proof, sum the absolute values of the elements in row x0 on both
sides of (4.20) and divide by 2. On the right, the second factor is at most the
largest possible total variation distance between distributions, which is 1. Hence
for any x0 we have

(4.20)

Taking α = θ1/r and C = 1/θ ﬁnishes the proof.

(cid:13)P rk+j(x0, ·) − π(cid:13)
(cid:13)

(cid:13)TV ≤ θk.

(4.21)
(cid:4)

4.4. Standardizing Distance from Stationarity

Bounding the maximal distance (over x0 ∈ X ) between P t(x0, ·) and π is among

our primary objectives. It is therefore convenient to deﬁne

d(t) := max
x∈X

(cid:13)
(cid:13)P t(x, ·) − π

(cid:13)
(cid:13)TV .

(4.22)

We will see in Chapter 5 that it is often possible to bound (cid:107)P t(x, ·) − P t(y, ·)(cid:107)TV,

uniformly over all pairs of states (x, y). We therefore make the deﬁnition
(cid:13)P t(x, ·) − P t(y, ·)(cid:13)
(cid:13)

(cid:13)TV .

¯d(t) := max
x,y∈X

(4.23)

The relationship between d and ¯d is given below:
Lemma 4.10. If d(t) and ¯d(t) are as deﬁned in (4.22) and (4.23), respectively,

then

(4.24)
Proof. It is immediate from the triangle inequality for the total variation

d(t) ≤ ¯d(t) ≤ 2d(t).

distance that ¯d(t) ≤ 2d(t).

(cid:80)

To show that d(t) ≤ ¯d(t), note ﬁrst that since π is stationary, we have π(A) =
y∈X π(y)P t(y, A) for any set A. (This is the deﬁnition of stationarity if A is a
singleton {x}. To get this for arbitrary A, just sum over the elements in A.) Using
this shows that

|P t(x, A) − π(A)| =

≤

(cid:12)
(cid:12)
(cid:12)
π(y) (cid:2)P t(x, A) − P t(y, A)(cid:3)
(cid:12)
(cid:12)
(cid:12)

(cid:88)

(cid:12)
(cid:12)
(cid:12)
(cid:12)
(cid:12)
(cid:12)
y∈X
(cid:88)

π(y) (cid:13)

(cid:13)P t(x, ·) − P t(y, ·)(cid:13)

(cid:13)TV ≤ ¯d(t) ,

(4.25)

by the triangle inequality and the deﬁnition of total variation. Maximizing the
left-hand side over x and A yields d(t) ≤ ¯d(t).

y∈X



<!-- pdf-page: 8 -->
54

4. INTRODUCTION TO MARKOV CHAIN MIXING

Let P denote the collection of all probability distributions on X . Exercise 4.1

(cid:4)

asks the reader to prove the following equalities:
(cid:13)µP t − π(cid:13)
(cid:13)
(cid:13)TV ,
(cid:13)µP t − νP t(cid:13)
(cid:13)

d(t) = sup
µ∈P
¯d(t) = sup
µ,ν∈P

(cid:13)TV .

Lemma 4.11. The function ¯d is submultiplicative: ¯d(s + t) ≤ ¯d(s) ¯d(t).
Proof. Fix x, y ∈ X , and let (Xs, Ys) be the optimal coupling of P s(x, ·) and

P s(y, ·) whose existence is guaranteed by Proposition 4.7. Hence

(cid:107)P s(x, ·) − P s(y, ·)(cid:107)TV = P{Xs (cid:54)= Ys}.

We have

P s+t(x, w) =

(cid:88)

z

P{Xs = z}P t(z, w) = E (cid:0)P t(Xs, w)(cid:1) .

For a set A, summing over w ∈ A shows that

P s+t(x, A) − P s+t(y, A) = E (cid:0)P t(Xs, A) − P t(Ys, A)(cid:1)

≤ E (cid:0) ¯d(t)1{Xs(cid:54)=Ys}
By (4.26), the right-hand side is at most ¯d(s) ¯d(t).

(cid:1) = P{Xs (cid:54)= Ys} ¯d(t).

(4.26)

(4.27)

(4.28)

(cid:4)

Remark 4.12. Theorem 4.9 can be deduced from Lemma 4.11. One needs to
check that ¯d(s) < 1 for some s; this follows since P s has all positive entries for
some s.

Exercise 4.2 implies that ¯d(t) is non-increasing in t. By Lemma 4.10 and

Lemma 4.11, if c and t are positive integers, then

d(ct) ≤ ¯d(ct) ≤ ¯d(t)c.

4.5. Mixing Time

(4.29)

It is useful to introduce a parameter which measures the time required by a
Markov chain for the distance to stationarity to be small. The mixing time is
deﬁned by

and

tmix(ε) := min{t : d(t) ≤ ε}

tmix := tmix(1/4).

Lemma 4.10 and (4.29) show that when (cid:96) is a positive integer,

d( (cid:96)tmix(ε) ) ≤ ¯d( tmix(ε) )(cid:96) ≤ (2ε)(cid:96).

In particular, taking ε = 1/4 above yields
d( (cid:96)tmix ) ≤ 2−(cid:96)

and

tmix(ε) ≤ (cid:6)log2 ε−1(cid:7) tmix.

(4.30)

(4.31)

(4.32)

(4.33)

(4.34)



<!-- pdf-page: 9 -->
4.6. MIXING AND TIME REVERSAL

55

See Exercise 4.3 for a small improvement. Thus, although the choice of 1/4 is
arbitrary in the deﬁnition (4.31) of tmix, a value of ε less than 1/2 is needed to
make the inequality d( (cid:96)tmix(ε) ) ≤ (2ε)(cid:96) in (4.32) meaningful and to achieve an
inequality of the form (4.34).

Rigorous upper bounds on mixing times lend conﬁdence that simulation studies

or randomized algorithms perform as advertised.

4.6. Mixing and Time Reversal

For a distribution µ on a group G, the reversed distribution (cid:98)µ is deﬁned by
(cid:98)µ(g) := µ(g−1) for all g ∈ G. Let P be the transition matrix of the random walk
with increment distribution µ. Then the random walk with increment distribution
(cid:98)µ is exactly the time reversal (cid:98)P (deﬁned in (1.32)) of P .

In Proposition 2.14 we noted that when (cid:98)µ = µ, the random walk on G with
increment distribution µ is reversible, so that P = (cid:98)P . Even when µ is not a
symmetric distribution, however, the forward and reversed walks must be at the
same distance from stationarity; we will use this in analyzing card shuﬄing in
Chapters 6 and 8.

Lemma 4.13. Let P be the transition matrix of a random walk on a group G
with increment distribution µ and let (cid:98)P be that of the walk on G with increment
distribution (cid:98)µ. Let π be the uniform distribution on G. Then for any t ≥ 0

(cid:13)P t(id, ·) − π(cid:13)
(cid:13)

(cid:13)TV =

(cid:13)
(cid:13) (cid:98)P t(id, ·) − π
(cid:13)

(cid:13)
(cid:13)
(cid:13)TV

.

Proof. Let (Xt) = (id, X1, . . . ) be a Markov chain with transition matrix
P and initial state id. We can write Xk = gkgk−1 . . . g1, where the random ele-
ments g1, g2, · · · ∈ G are independent choices from the distribution µ. Similarly, let
(Yt) be a chain with transition matrix (cid:98)P , with increments h1, h2, · · · ∈ G chosen
independently from (cid:98)µ. For any ﬁxed elements a1, . . . , at ∈ G,

P{g1 = a1, . . . , gt = at} = P{h1 = a−1

t

, . . . , ht = a−1

1 },

by the deﬁnition of (cid:98)P . Summing over all strings such that atat−1 . . . a1 = a yields

P t(id, a) = (cid:98)P t(id, a−1).

Hence

(cid:88)

a∈G

(cid:12)
(cid:12)P t(id, a) − |G|−1(cid:12)

(cid:12) =

(cid:12)
(cid:12)

(cid:12) (cid:98)P t(id, a−1) − |G|−1(cid:12)
(cid:12)
(cid:12) =

(cid:88)

a∈G

(cid:88)

a∈G

(cid:12)
(cid:12)

(cid:12) (cid:98)P t(id, a) − |G|−1(cid:12)

(cid:12)
(cid:12)

which together with Proposition 4.2 implies the desired result.

(cid:4)

Corollary 4.14. If tmix is the mixing time of a random walk on a group and

(cid:100)tmix is the mixing time of the reversed walk, then tmix = (cid:100)tmix.

It is also possible for reversing a Markov chain to signiﬁcantly change the mixing

time. The winning streak is an example, and is discussed in Section 5.3.5.



<!-- pdf-page: 10 -->
56

4. INTRODUCTION TO MARKOV CHAIN MIXING

4.7. (cid:96)p Distance and Mixing

The material in this section is not used until Chapter 10.
Other distances between distributions are useful. Given a distribution π on X

and 1 ≤ p ≤ ∞, the (cid:96)p(π) norm of a function f : X → R is deﬁned as




(cid:104)(cid:80)

y∈X |f (y)|pπ(y)

(cid:105)1/p

(cid:107)f (cid:107)p :=


For functions f, g : X → R, deﬁne the scalar product

maxy∈X |f (y)|

1 ≤ p < ∞,

p = ∞ .

(cid:104)f, g(cid:105)π :=

(cid:88)

x∈X

f (x)g(x)π(x) .

For an irreducible transition matrix P on X with stationary distribution π, deﬁne

qt(x, y) :=

P t(x, y)
π(y)

,

and note that qt(x, y) = qt(y, x) when P is reversible with respect to π. Note also
that

(cid:104)qt(x, ·), 1(cid:105)π =

qt(x, y)π(y) = 1 .

(4.35)

(cid:88)

The (cid:96)p-distance d(p) is deﬁned as

y

d(p)(t) := max
x∈X

(cid:107)qt(x, ·) − 1(cid:107)p .

(4.36)

Proposition 4.2 shows that d(1)(t) = 2d(t). The distance d(p) is submultiplicative:
d(p)(t + s) ≤ d(p)(t)d(p)(s) .

This is proved in the Notes to this chapter (Lemma 4.18). We mostly focus in this
book on the cases p = 1, 2 and p = ∞. The (cid:96)2 distance is particularly convenient
in the reversible case due to the identity given as Lemma 12.18(i).

Since the (cid:96)p norms are non-decreasing (Exercise 4.5),
2d(t) = d(1)(t) ≤ d(2)(t) ≤ d(∞)(t) .

Finally, (cid:96)2 and (cid:96)∞ distances are related as follows for reversible chains:
Proposition 4.15. For a reversible Markov chain,

d(∞)(2t) = [d(2)(t)]2 = max
x∈X

q2t(x, x) − 1 .

(4.37)

(4.38)

Proof. First observe that

P 2t(x, y) =

(cid:88)

z∈X

P t(x, z)P t(z, y) .

Dividing both sides by π(y) and using reversibility yields

q2t(x, y) =

P t(x, z)
π(z)

P t(z, y)
π(y)

(cid:88)

z∈X

π(z) = (cid:104)qt(x, ·), qt(y, ·)(cid:105)π .

(4.39)

Using (4.35), we have

(cid:104)qt(x, ·) − 1, qt(y, ·) − 1(cid:105)π = (cid:104)qt(x, ·), qt(y, ·)(cid:105)π − (cid:104)1, qt(y, ·)(cid:105)π − (cid:104)qt(x, ·), 1(cid:105)π + 1

= q2t(x, y) − 1 .

(4.40)



<!-- pdf-page: 11 -->
EXERCISES

In particular, taking x = y shows that

(cid:107)qt(x, ·) − 1(cid:107)2

2 = q2t(x, x) − 1 .

57

(4.41)

Maximizing over x yields the right-hand equality in (4.38). By (4.40) and Cauchy-
Schwarz,

|q2t(x, y) − 1| ≤ (cid:107)qt(x, ·) − 1(cid:107)2 · (cid:107)qt(y, ·) − 1(cid:107)2

(cid:112)

=

q2t(x, x) − 1

(cid:112)

q2t(y, y) − 1 .

Thus,

d(∞)(2t) = max
x,y∈X

|q2t(x, y) − 1| ≤ max
x∈X

q2t(x, x) − 1 .

(4.42)

(4.43)

Considering x = y shows that equality holds in (4.43) and proves the proposition.
(cid:4)

We deﬁne the (cid:96)p-mixing time as

t(p)
mix(ε) := inf{t ≥ 0 : d(p)(t) ≤ ε} ,

mix = t(p)
t(p)
2 in (4.44) gives t(1)

mix

(cid:0) 1
2

(cid:1) .

(4.44)

mix = tmix.) The

(Since d(1)(t) = 2d(t), using the constant 1
parameter t(∞)

mix is often called the uniform mixing time.

Similar to tmix, since d(p)(kt(p)

mix) ≤ 2−k by submultiplicity (Lemma 4.18),

mix(ε) ≤ (cid:100)log2 ε−1(cid:101)t(p)
t(p)

mix .

Exercises

Exercise 4.1. Prove that

d(t) = sup

µ
¯d(t) = sup
µ,ν

(cid:13)µP t − π(cid:13)
(cid:13)
(cid:13)TV ,
(cid:13)µP t − νP t(cid:13)
(cid:13)

(cid:13)TV ,

where µ and ν vary over probability distributions on a ﬁnite set X .

Exercise 4.2. Let P be the transition matrix of a Markov chain with state

space X and let µ and ν be any two distributions on X . Prove that

(cid:107)µP − νP (cid:107)TV ≤ (cid:107)µ − ν(cid:107)TV .

(This in particular shows that (cid:13)
the chain can only move it closer to stationarity.)

(cid:13)µP t+1 − π(cid:13)

(cid:13)TV ≤ (cid:107)µP t − π(cid:107)TV, that is, advancing

Deduce that for any t ≥ 0,

d(t + 1) ≤ d(t),

and

¯d(t + 1) ≤ ¯d(t) .

Exercise 4.3. Prove that if t, s ≥ 0, then d(t + s) ≤ d(t) ¯d(s). Deduce that if

k ≥ 2, then tmix(2−k) ≤ (k − 1)tmix.

Exercise 4.4. For i = 1, . . . , n, let µi and νi be measures on Xi, and deﬁne

measures µ and ν on (cid:81)n

i=1 µi and ν := (cid:81)n
i=1 Xi by µ := (cid:81)n
n
(cid:88)

(cid:107)µ − ν(cid:107)TV ≤

(cid:107)µi − νi(cid:107)TV .

i=1 νi. Show that

Exercise 4.5. Show that for any f : X → R, the function p (cid:55)→ (cid:107)f (cid:107)p is non-

decreasing for p ≥ 1.

i=1



<!-- pdf-page: 12 -->
58

4. INTRODUCTION TO MARKOV CHAIN MIXING

Notes

Our exposition of the Convergence Theorem follows Aldous and Diaconis
(1986). Another approach is to study the eigenvalues of the transition matrix.
See, for instance, Seneta (2006). Eigenvalues and eigenfunctions are often useful
for bounding mixing times, particularly for reversible chains, and we will study
them in Chapters 12 and 13. For convergence theorems for chains on inﬁnite state
spaces, see Chapter 21.

Aldous (1983b, Lemma 3.5) is a version of our Lemma 4.11 and Exercise 4.2.

He says all these results “can probably be traced back to Doeblin.”

The winning streak example is taken from Lov´asz and Winkler (1998).
We emphasize (cid:96)p distances, especially for p = 1, but mixing time can be deﬁned
using other distances. The separation distance, deﬁned in Chapter 6, is often used.
The Hellinger distance dH , deﬁned as

dH (µ, ν) :=

(cid:115)

(cid:88)

(cid:16)(cid:112)

µ(x) − (cid:112)

(cid:17)2

ν(x)

,

x∈X

(4.45)

behaves well on products (cf. Exercise 20.7). This distance is used in Section 20.4
to obtain a good bound on the mixing time for continuous product chains.

Further reading. Lov´asz (1993) gives the combinatorial view of mixing.
Saloﬀ-Coste (1997) and Montenegro and Tetali (2006) emphasize analytic
tools. Aldous and Fill (1999) is indispensable. Other references include Sinclair
(1993), H¨aggstr¨om (2002), Jerrum (2003), and, for an elementary account of
the Convergence Theorem, Grinstead and Snell (1997, Chapter 11).

Complements. The result of Lemma 4.13 generalizes to transitive Markov

chains, which we deﬁned in Section 2.6.2.

Lemma 4.16. Let P be the transition matrix of a transitive Markov chain with
state space X , let (cid:98)P be its time reversal, and let π be the uniform distribution on
X . Then

(cid:13)
(cid:13) (cid:98)P t(x, ·) − π
(cid:13)

(cid:13)
(cid:13)
(cid:13)TV

= (cid:13)

(cid:13)P t(x, ·) − π(cid:13)

(cid:13)TV .

(4.46)

Proof. Since our chain is transitive, for every x, y ∈ X there exists a bijection

ϕ(x,y) : X → X that carries x to y and preserves transition probabilities.

Now, for any x, y ∈ X and any t,
(cid:88)
(cid:12)P t(x, z) − |X |−1(cid:12)
(cid:12)
(cid:12)P t(ϕ(x,y)(x), ϕ(x,y)(z)) − |X |−1(cid:12)
(cid:12)
(cid:12)

(cid:12) =

(cid:88)

z∈X

=

z∈X
(cid:88)

z∈X

(cid:12)
(cid:12)P t(y, z) − |X |−1(cid:12)
(cid:12) .

(4.47)

(4.48)

Averaging both sides over y yields
(cid:12)
(cid:12)P t(x, z) − |X |−1(cid:12)

(cid:88)

(cid:12) =

z∈X

1
|X |

(cid:88)

(cid:88)

y∈X

z∈X

(cid:12)P t(y, z) − |X |−1(cid:12)
(cid:12)
(cid:12) .

(4.49)

Because π is uniform, we have P (y, z) = (cid:98)P (z, y), and thus P t(y, z) = (cid:98)P t(z, y). It
follows that the right-hand side above is equal to

1
|X |

(cid:88)

(cid:88)

y∈X

z∈X

(cid:12)
(cid:12)

(cid:12) (cid:98)P t(z, y) − |X |−1(cid:12)
(cid:12)
(cid:12) =

1
|X |

(cid:88)

(cid:88)

z∈X

y∈X

(cid:12)
(cid:12)

(cid:12) (cid:98)P t(z, y) − |X |−1(cid:12)
(cid:12)
(cid:12) .

(4.50)



<!-- pdf-page: 13 -->
NOTES

59

By Exercise 2.8, (cid:98)P is also transitive, so (4.49) holds with (cid:98)P replacing P (and z and
y interchanging roles). We conclude that
(cid:12)P t(x, z) − |X |−1(cid:12)
(cid:12)

(cid:12) (cid:98)P t(x, y) − |X |−1(cid:12)
(cid:12)
(cid:12) .

(4.51)

(cid:12) =

(cid:88)

(cid:88)

(cid:12)
(cid:12)

z∈X

y∈X

Dividing by 2 and applying Proposition 4.2 completes the proof.

(cid:4)

Remark 4.17. The proof of Lemma 4.13 established an exact correspondence
between forward and reversed trajectories, while that of Lemma 4.16 relied on
averaging over the state space.

The distances d(p) are all submultiplicative, which diminishes the importance

of the constant 1

2 in the deﬁnition (4.44).

Lemma 4.18. The distance d(p) is submultiplicative:

(4.52)
Proof. H¨older’s Inequality implies that if p and q satisfy 1/p + 1/q = 1, then

d(p)(s + t) ≤ d(1)(s)d(p)(t) ≤ d(p)(s)d(p)(t) .

(cid:107)g(cid:107)p = max
(cid:107)f (cid:107)q≤1

(cid:88)

(cid:12)
(cid:12)
(cid:12)
(cid:12)
(cid:12)

(cid:12)
(cid:12)
(cid:12)
f (x)g(x)π(x)
(cid:12)
(cid:12)

.

(4.53)

x∈X
(See, for example, Proposition 6.13 of Folland (1999).) When p = q = 2, (4.53)
is a consequence of Cauchy-Schwarz, while for p = ∞, q = 1 and p = 1, q = ∞, this
is elementary. From (4.53) and the deﬁnition (4.36), it follows that

d(p)(t) = max
x∈X

max
(cid:107)f (cid:107)q≤1

= max
x∈X
Thus, for every function g : X → R,

max
(cid:107)f (cid:107)q≤1

(cid:88)

f (y)[qt(x, y) − 1]π(y)

(cid:12)
(cid:12)
(cid:12)
(cid:12)
(cid:12)
(cid:12)
y∈X
|P tf (x) − π(f )| = max
(cid:107)f (cid:107)q≤1

(cid:12)
(cid:12)
(cid:12)
(cid:12)
(cid:12)
(cid:12)
(cid:107)P tf − π(f )(cid:107)∞ .

(4.54)

(cid:107)P sg − π(g)(cid:107)∞ = (cid:107)P s(g/(cid:107)g(cid:107)q) − π(g/(cid:107)g(cid:107)q)(cid:107)∞ · (cid:107)g(cid:107)q ≤ d(p)(s)(cid:107)g(cid:107)q .
Suppose that (cid:107)f (cid:107)q ≤ 1. Applying this inequality with g = P tf − π(f ) and p = 1,
and then applying (4.54), yields

(cid:107)P t+sf − π(f )(cid:107)∞ ≤ d(1)(s)(cid:107)P tf − π(f )(cid:107)∞ ≤ d(1)(s)d(p)(t) .

Maximizing over such f , using (4.54) with t + s in place of t, we obtain (4.52).

(cid:4)


