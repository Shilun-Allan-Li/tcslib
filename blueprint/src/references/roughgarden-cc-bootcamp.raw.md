<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: d54d402b16e24167c171968b47b8205d6277512e5df493c123ab6240671b5f96 -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
Lecture 4

Boot Camp on Communication Complexity

4.1 Preamble

This lecture covers the most important basic facts about deterministic and randomized
communication protocols in the general two-party model, as deﬁned by Yao (1979). Some
version of this lecture would normally be the ﬁrst lecture in a course on communication
complexity. How come it’s the fourth one here?

The ﬁrst three lectures were about one-way communication complexity — communication
protocols where there is only one message, from Alice to Bob — and its applications. One
reason we started with the one-way model is that several of the “greatest hits” of algorithmic
lower bounds via communication complexity, such as space lower bounds for streaming
algorithms and row lower bounds for compressive sensing matrices, already follow from
communication lower bounds for one-way protocols. A second reason is that considering
only one-way protocols is a gentle introduction to what communication protocols look like.
There are already some non-trivial one-way protocols, like our randomized protocol for
Equality. On the other hand, proving lower bounds for one-way protocols is much easier
than proving them for general protocols, so it’s also a good introduction to lower bound
proofs.

The rest of our algorithmic applications require stronger lower bounds that apply to
more than just one-way protocols. This lecture gives a “boot camp” on the basic model.
We won’t say much about applications in this lecture, but the ﬁnal ﬁve lectures all focus
on applications. We won’t prove any hard results today, and focus instead on deﬁnitions
and vocabulary, examples, and some easy results. One point of today’s lecture is to get
a feel for what’s involved in proving a communication lower bound for general protocols.
It generally boils down to a conceptually simple, if sometimes mathematically challenging,
combinatorial problem — proving that a large number of “rectangles” of a certain type are
need to cover a matrix.1

1There are many other methods for proving communication lower bounds, some quite deep and exotic
(see e.g. Lee and Shraibman (2009)), but all of our algorithmic applications can ultimately be derived from
combinatorial covering-type arguments. For example, we’re not even going to mention the famous “rank
lower bound.” For your ediﬁcation, some other lower bound methods are discussed in the Exercises.

50



<!-- pdf-page: 2 -->
4.2 Deterministic Protocols

51

4.2 Deterministic Protocols

4.2.1 Protocols

∈

Y unknown to Alice. (Most commonly, X = Y =

We are still in the two-party model, where Alice has an input x
X unknown to Bob,
n.) A
and Bob has an input y
deterministic communication protocol speciﬁes, as function of the messages sent so far,
whose turn it is to speak. A protocol always speciﬁes when the communication has ended
and, in each end state, the value of the computed bit. Alice and Bob can coordinate in
advance to decide upon the protocol, and both are assumed to cooperative fully. The only
constraint faced by the players is that what a player says can depend only on what the
player knows — his or her own input, and the history of all messages sent so far.

0, 1
{

∈

}

Like with one-way protocols, we deﬁne the cost of a protocol as the maximum number
of bits it ever sends, ranging over all inputs. The communication complexity of a function is
then the minimum communication cost of a protocol that correctly computes it.

The key feature of general communication protocols absent from the special case of
one-way protocols is interaction between the two players. Intuitively, interaction should
allow the players to communicate much more eﬃciently. Let’s see this in a concrete example.

4.2.2 Example: Clique-Independent Set

V

The following problem might seem contrived, but it is fairly central in communication
= n that is known to both players. Alice’s
complexity. There is a graph G = (V, E) with
private input is a clique C of G — a subset of vertices such that (u, v)
E for every distinct
C. Bob’s private input is an independent set I of G — a subset of vertices such that
u, v
∈
(u, v)
I. (There is no requirement that C or I is maximal.)
Observe that C and I are either disjoint, or they intersect in a single vertex (Figure 4.1).
The players’ goal is to ﬁgure out which of these two possibilities is the case. Thus, this
problem is a special case of Disjointness, where players’ sets are not arbitrary but rather
a clique and an independent set from a known graph.

E for every distinct u, v

6∈

∈

∈

|

|

The naive communication protocol for solving the problem using Θ(n) bits — Alice can
send the characteristic vector of C to Bob, or Bob the characteristic vector of I to Alice,
and then the other player computes the correct answer. Since the number of cliques and
independent sets of a graph is generally exponential in the number n of vertices, this protocol
cannot be made signiﬁcantly more communication-eﬃcient via a smarter encoding. An
easy reduction from Index shows that one-way protocols, including randomized protocols,
require Ω(n) communication (exercise).

The players can do much better by interacting. Here is the protocol.

1. If there is a vertex v
such vertex to Bob (

∈
≈

C with deg(v) < n
log2 n bits).

2 , then Alice sends the name of an arbitrary



<!-- pdf-page: 3 -->
52

Boot Camp on Communication Complexity

C

I"

Figure 4.1 A clique C and an independent set I overlap in zero or one vertices.

a) Bob announces whether or not v

conclusion “not disjoint.”

∈

I (1 bit). If so, the protocol terminates with

b) Otherwise, Alice and Bob recurse on the subgraph H induced by v and its

neighbors.
[Note: H contains at most half the nodes of G. It contains all of C and, if I
intersects C, it contains the vertex in their intersection. C and I intersect in G
if and only if their projections to H intersect in H.]

2. Otherwise, Alice sends a “NULL” message to Bob (

log2 n bits).

≈

3. If there is a vertex v
such vertex to Bob (

∈
≈

I with deg(v)
log2 n bits).

≥

a) Alice announces whether or not v

(“not disjoint”).

n
2 , then Bob sends the name of an arbitrary

C (1 bit). If so, the protocol terminates

∈

b) If not, Alice and Bob recurse on the subgraph H induced by v and its non-

neighbors.
[Note: H contains at most half the nodes of G. It contains all of I and, if C
intersects I, it contains the vertex in their intersection. Thus the function’s
answer in H is the same as that in G.]

4. Otherwise, Bob terminates the protocol and declares “disjoint.”

[Disjointness is obvious since, at this point in the protocol, we know that deg(v) < n
2
I.]
for all v

C and deg(v)

∈

n
2 for all v

∈

≥



<!-- pdf-page: 4 -->
4.2 Deterministic Protocols

53

Since each iteration of the protocol uses O(log n) bits of communication and cuts the
number of vertices of the graph in half (or terminates), the total communication is O(log2 n).
As previously noted, such a result is impossible without interaction between the players.

4.2.3 Trees and Matrices

The Clique-Independent Set problem clearly demonstrates that we need new lower
bound techniques to handle general communication protocols — the straightforward Pi-
geonhole Principle arguments that worked for one-way protocols are not going to be good
enough. At ﬁrst blush this might seem intimidating — communication protocols can do all
sorts of crazy things, so how can we reason about them in a principled way? How can we
connect properties of a protocol to the function that it computes? Happily, we can quickly
build up some powerful machinery for answering these questions.

First, we observe that deterministic communication protocols are really just binary trees.
We’ll almost never use this fact directly, but it should build some conﬁdence that protocols
are familiar and elementary mathematical objects.

The connection is easiest to see by example; see Figure 4.2. Consider the following
protocol for solving Equality with n = 2 (i.e., f (x, y) = 1 if and only if x = y). Alice
begins by sending her ﬁrst bit. If Bob’s ﬁrst bit is diﬀerent, he terminates the protocol and
announces “not equal.” If Bob’s ﬁrst bit is the same, then he transmits the same bit back.
In this case, Alice then sends her second bit. At this point, Bob knows Alice’s whole input
and can therefore compute the correct answer.

In Figure 4.2, each node corresponds to a possible state of the protocol, and is labeled
with the player whose turn it is to speak. Thus the labels alternate with the levels, with
the root belonging to Alice.2 There are 10 leaves, representing the possible end states of
the protocol. There are two leaves for the case where Alice and Bob have diﬀerent ﬁrst
bits and the protocol terminates early, and eight leaves for the remaining cases where Alice
and Bob have the same ﬁrst bit. Note that the possible transcripts of the protocol are
in one-to-one correspondence with the root-leaf nodes of the tree — we use leaves and
transcripts interchangeably below.

We can view the leaves as a partition

Y , with Z(`) the
Z(`)
{
inputs (x, y) such that the protocol terminates in the leaf `. In our example, there are 10
leaves for the 16 possible inputs (x, y), so diﬀerent inputs can generate the same transcript
— more on this shortly.

of the input space X

×

}

Next note that we can represent a function (from (x, y) to

) a matrix. In contrast
to the visualization exercise above, we’ll use this matrix representation all the time. The
rows are labeled with the set X of possible inputs of Alice, the columns with the set Y of
possible inputs of Bob. Entry (x, y) of the matrix is f (x, y). Keep in mind that this matrix
is fully known to both Alice and Bob when they agree on a protocol.

0, 1
}
{

2In general, players need not alternate turns in a communication protocol.



<!-- pdf-page: 5 -->
54

Boot Camp on Communication Complexity

A"

0%

1%

B"

0%

1%

B"

0%

1%

A"

0%

1%

“no”%

“no”%

B"

B"

0%

1%

0%

1%

B"

0%

A"

1%

B"

0%

1%

0%

1%

“yes”%

“no”%

“no”%

“yes”%

“yes”%

“no”%

“no”%

“yes”%

Figure 4.2 The binary tree induced by a communication protocol for Equality with n = 2.

For example, suppose that X = Y =

then corresponds to the identity matrix:

2, resulting in 4

0, 1
{

}

×

4 matrices. Equality

00 01 10 11
0
1
0
0
0
0
1
0

0
0
1
0

0
1
0
0

00
01
10
11













(4.1)

If we deﬁne the Greater-Than function as 1 whenever x is at least y (where x and y
are interpreted as non-negative integers, written in binary), then we just ﬁll in the lower
triangle with 1s:

00 01 10 11
0
1
0
1
0
1
1
1

0
0
1
1

0
1
1
1







00
01
10
11









<!-- pdf-page: 6 -->
4.2 Deterministic Protocols

55

We also write out the matrix for Disjointness, which is somewhat more inscrutable:

00 01 10 11
1
1
0
1
0
1
0
1

1
1
0
0

1
0
1
0







00
01
10
11







4.2.4 Protocols and Rectangles

How can we reason about the behavior of a protocol? Just visualizing them as trees is not
directly useful. We know that simple Pigeonhole Principle-based arguments are not strong
enough, but it still feels like we want some kind of counting argument.

To see what might be true, let’s run the 2-bit Equality protocol depicted in Figure 4.2
and track its progress using the matrix in (4.1). Put yourself in the shoes of an outside
observer, who knows neither x nor y, and makes inferences about (x, y) as the protocol
proceeds. When the protocol terminates, we’ll have carved up the matrix into 10 pieces,
one for each leaf of protocol tree — the protocol transcript reveals the leaf to an outside
observer, but nothing more.

Before the protocol beings, all 16 inputs are fair game. After Alice sends her ﬁrst bit,
the outside observer can narrow down the possible inputs into a set of 8 — the top 8 if Alice
sent a 0, the bottom 8 if she sent a 1. The next bit sent gives away whether or not Bob’s ﬁrst
bit is a 0 or 1, so the outsider observer learns which quadrant the input lies in. Interestingly,
in the northeastern and southwestern quadrants, all of the entries are 0. In these cases,
even though ambiguity remains about exactly what the input (x, y) is, the function’s value
f (x, y) has been determined (it is 0, whatever the input). It’s no coincidence that these
two regions correspond to the two leaves of the protocol in Figure 4.2 that stop early, with
the correct answer. If the protocol continues further, then Alice’s second bit splits the
northwestern and southeastern quadrants into two, and Bob’s ﬁnal bit splits them again,
now into singleton regions. In these cases, an outside observer learns the entire input (x, y)
from the protocol’s transcript.3

What have we learned? We already knew that every protocol induces a partition of the
input space X
Y , with one set for each leaf or, equivalently, for each distinct transcript.
At least for the particular protocol that we just studied, each of the sets has a particularly
nice submatrix form (Figure 4.3). This is true in general, in the following sense.

×

3It’s also interesting to do an analogous thought experiment from the perspective of one of the players.
For example, consider Bob’s perspective when the input is (00,01). Initially Bob knows that the input lies
in the second column but is unsure of the row. After Alice’s ﬁrst message, Bob knows that the input is in
the second column and one of the ﬁrst two rows. Bob still cannot be sure about the correct answer, so the
protocol proceeds.



<!-- pdf-page: 7 -->
56

Boot Camp on Communication Complexity

00"01"

10"

11"

00"
01"
10"
11"

1"
0"
0"
0"

0"
0"
1"
0"
0"
1"
0"0"

0"
0"
0"
1"

Figure 4.3 The partition of the input space X
can be generated by the Equality protocol.

×

Y according to the 10 diﬀerent transcripts that

Lemma 4.1 (Rectangles) For every transcript z of a deterministic protocol P , the set of
inputs (x, y) that generate z are a rectangle, of the form A

×
A rectangle just means a subset of the input space X

Y that can be written as
a product. For example, the set
is not a rectangle, while the set
Y is a rectangle
(00, 00), (11, 00), (00, 11), (11, 11)
{
if and only if it is closed under “mix and match,” meaning that whenever (x1, y1) and
(x2, y2) are in S, so are (x1, y2) and (x2, y1) (see the Exercises).

(00, 00), (11, 11)
{
is.

In general, a subset S

X and B

B for A

Y .

X

⊆

⊆

×

⊆

×

}

}

Don’t be misled by our example (Figure 4.3), where the rectangles induced by our
protocol happen to be “contiguous.” For example, if we keep the protocol the same but
switch the order in which we write down the rows and columns corresponding to 01 and 10,
we get an analogous decomposition in which the two large rectangles are not contiguous. In
general, you shouldn’t even think of X and Y as ordered sets. Rectangles are sometimes
called combinatorial rectangles to distinguish them from “geometric” rectangles and to
emphasize this point.

Lemma 4.1 is extremely important, though its proof is straightforward — we just follow
the protocol like in our example above. Intuitively, each step of a protocol allows an outside
observer to narrow down the possibilities for x while leaving the possibilities for y unchanged
(if Alice speaks) or vice versa (if Bob speaks).

Proof of Lemma 4.1: Fix a deterministic protocol P . We proceed by induction on the number
Y begin with the empty transcript. For
of bits exchanged. For the base case, all inputs X
the inductive step, consider an arbitrary t-bit transcript-so-far z generated by P , with t
1.
Assume that Alice was the most recent player to speak; the other case is analogous. Let
z0 denote z with the ﬁnal bit b
lopped oﬀ. By the inductive hypothesis, the set of
0, 1
}
inputs that generate z0 has the form A
A denote the inputs x
A such that,
B. Let Ab
×
in the protocol P , Alice sends the bit b given the transcript z0. (Recall that the message
sent by a player is a function only of his or her private input and the history of the protocol

∈ {

×

≥

⊆

∈



<!-- pdf-page: 8 -->
4.2 Deterministic Protocols

57

so far.) Then the set of inputs that generate z are Ab

B, completing the inductive step. (cid:4)

×

Note that Lemma 4.1 makes no reference to a function f — it holds for any deterministic
protocol, whether or not it computes a function that we care about. In Figure 4.3, we can
clearly see an additional property of all of the rectangles — with respect to the matrix
in (4.1), every rectangle is monochromatic, meaning all of its entries have the same value.
This is true for any protocol that correctly computes a function f .

Lemma 4.2 If a deterministic protocol P computes a function f , then every rectangle
induced by P is monochromatic in the matrix M (f ).

Proof: Consider an arbitrary combinatorial rectangle A
in A
correctly computes f , f is also constant on A

B. (cid:4)

×

B inducing the same transcript. The output of P is constant on A

B induced by P , with all inputs
B. Since P

×

×

×

Amazingly, the minimal work we’ve invested so far already yields a powerful technique

for lower bounding the deterministic communication complexity of functions.

Theorem 4.3 Let f be a function such that every partition of M (f ) into monochromatic
rectangles requires at least t rectangles. Then the deterministic communication complexity of
f is at least log2 t.

Proof: A deterministic protocol with communication cost c can only generate 2c distinct
transcripts — equivalently, its (binary) protocol tree can only have 2c leaves. If such a
protocol computes the function f , then by Lemmas 4.1 and 4.2 it partitions M (f ) into at
most 2c monochromatic rectangles. By assumption, 2c

t and hence c

log2 t. (cid:4)

≥

≥

Rather than applying Theorem 4.3 directly, we’ll almost always be able to prove a
stronger and simpler condition. To partition a matrix, one needs to cover all of its entries
with disjoint sets. The disjointness condition is annoying. So by a covering of a 0-1 matrix,
we mean a collection of subsets of entries whose union includes all of its elements — overlaps
between these sets are allowed. See Figure 4.4.

Corollary 4.4 Let f be a function such that every covering of M (f ) by monochromatic
rectangles requires at least t rectangles. Then the deterministic communication complexity of
f is at least log2 t.

Communication complexity lower bounds proved using covers — including all of those
proved in Section 4.2.5 — automatically apply also to more general “nondeterministic”
communication protocols, as well as randomized protocols with 1-sided error. We’ll discuss
this more next lecture, when it will be relevant.



<!-- pdf-page: 9 -->
58

Boot Camp on Communication Complexity

0"
1"
1"

1"
1"
1"

1"
1"
0"

Figure 4.4 A covering by four monochromatic rectangles that is not a partition.

4.2.5 Lower Bounds for Equality and Disjointness

Armed with Corollary 4.4, we can quickly prove communication lower bounds for some
functions of interest. For example, recall that when f is the Equality function, the matrix
M (f ) is the identity. The key observation about this matrix is: a monochromatic rectangle
that includes a “1” contains only one element. The reason is simple: such a rectangle is not
allowed to contain any 0’s since it is monochromatic, and if it included a second 1 it would
pick up some 0-entries as well (recall that rectangles are closed under “mix and match”).
Since there are 2n 1’s in the matrix, every covering by monochromatic rectangles (even of
just the 1’s) has size 2n.

Corollary 4.5 The deterministic communication complexity of Equality is at least n.4

The exact same argument gives the same lower bound for the Greater-Than function.

Corollary 4.6 The deterministic communication complexity of Greater-Than is at least
n.

We can generalize this argument as follows. A fooling set for a function f is a subset

F

X

Y of inputs such that:

×

⊆
(i) f is constant on F ;

(ii) for each distinct pair (x1, y1), (x2, y2)

opposite f -value.

F , at least one of (x1, y2), (x2, y1) has the

∈

4The 0s can be covered using another 2

monochromatic rectangles, one per row (rectangles need not be
“contiguous”!). This gives a lower bound of n + 1. The trivial upper has Alice sending her input to Bob and
Bob announcing the answer, which is a (n + 1)-bit protocol. Analogous “+1” improvements are possible for
the other examples in this section.

n



<!-- pdf-page: 10 -->
4.2 Deterministic Protocols

59

Since rectangles are closed under the “mix and match” operation, (i) and (ii) imply that
every monochromatic rectangle contains at most one element of F .

0, 1
}

.

}

∈ {

Corollary 4.7 If F is a fooling set for f , then the deterministic communication complexity
of f is at least log2 |
For Equality and Greater-Than, we were eﬀectively using the fooling set F =
x

(x, x) :

F

{

n

.

|

The fooling set method is powerful enough to prove a strong lower bound on the

deterministic communication complexity of Disjointness.

Corollary 4.8 The deterministic communication complexity of Disjointness is at least
n.

Proof: Take F =

(x, 1

x) : x

— or in set notation,

(S, Sc) : S

1, 2, . . . , n
{
Disjointness, while for every S
Figure 4.5. Since

}}

F

{

⊆
. The set F is a fooling set — it obviously consists only of “yes” inputs of
T c
(or both). See

∈ {

Sc

=

=

−

}

{

or T
= T , either S
= 2n, Corollary 4.7 completes the proof. (cid:4)

∩

∅

∩

∅

n

0, 1
}

|

|

S""""Tc"U"

S"

T"

T"""""Sc"
U"

Figure 4.5 If S and T are diﬀerent sets, then either S and T c or T and Sc are not disjoint.

4.2.6 Take-Aways

A key take-away point from this section is that, using covering arguments, we can prove
the lower bounds that we want on the deterministic communication complexity of many
functions of interest. These lower bounds apply also to nondeterministic protocols (discussed
next week) and randomized protocols with 1-sided error.

As with one-way communication complexity, proving stronger lower bounds that apply
also to randomized protocols with two-sided error is more challenging. Since we’re usually

6
6
6


<!-- pdf-page: 11 -->
60

Boot Camp on Communication Complexity

perfectly happy with a good randomized algorithm — recall the F2 estimation algorithm
from Section 1.4 — such lower bounds are very relevant for algorithmic applications. They
are our next topic.

4.3 Randomized Protocols

4.3.1 Default Parameter Settings

Our discussion of randomized one-way communication protocols in Section 2.2 remains
equally relevant for general protocols. Our “default parameter settings” for such protocols
will be the same.

Public coins. By default, we work with public-coin protocols, where Alice and Bob
have shared randomness in the form of an inﬁnite sequence of perfectly random bits written
on a blackboard in public view. Such protocols are more powerful than private-coin protocols,
but not by much (Theorem 4.9). Recall that public-coin randomized protocols are equivalent
to distributions over deterministic protocols.

Two-sided error. We allow a protocol to error with constant probability ( 1

3 by default),

whether or not the correct answer is “1” or “0.” This is the most permissive error model.

Arbitrary constant error probability. Recall that all constant error probabilities in
(0, 1
2 ) are the same — changing the error changes the randomized communication complexity
by only a constant factor (by the usual “independent trials” argument, detailed in the
exercises). Thus for upper bounds, we’ll be content to achieve error 49%; for lower bounds,
it is enough to rule out low-communication protocols with error %1.

Worst-case communication. We deﬁne the communication cost of a randomized
protocol as the maximum number of bits ever communicated, over all choices of inputs and
coin ﬂips. Measuring the expected communication (over the protocol’s coin ﬂips) could
reduce the communication complexity of a problem, but only by a constant factor.

4.3.2 Newman’s Theorem: Public- vs. Private-Coin Protocols

We mentioned a few times that, for our purposes, it usually won’t matter whether we
consider public-coin or private-coin randomized protocols. What we meant is the following
result.

Theorem 4.9 (Newman’s Theorem (1991)) If there is a public-coin protocol for a func-
tion f with n-bit inputs that has two-sided error 1/3 and communication cost c, then there
is a private-coin protocol for the problem that has two-sided error 1/3 and communication
cost O(c + log n).

Thus, for problems with public-coin randomized communication complexity Ω(log n),
like most of the problems that we’ll study in this course, there is no diﬀerence between the



<!-- pdf-page: 12 -->
4.3 Randomized Protocols

61

communication complexity of the public-coin and private-coin variants (modulo constant
factors).

An interesting exception is Equality. Last lecture, we gave a public-coin protocol —
one-way, even — with constant communication complexity. Theorem 4.9 only implies an
upper bound of O(log n) communication for private-coin protocols. (One can also give such
a private-coin protocol directly, see the Exercises.) There is also a matching lower bound
of Ω(log n) for the private-coin communication complexity of Equality. (This isn’t very
hard to prove, but we won’t have an occasion to do it.) Thus public-coin protocols can save
Θ(log n) bits of communication over private-coin protocols, but no more.

0, 1

∈ {

n.
}

Proof of Theorem 4.9: Let P denote a public-coin protocol with two-sided error 1/3. We
begin with a thought experiment. Fix an input (x, y), with x, y
If we run
P on this input, a public string r1 of random bits is consumed and the output of the
protocol is correct with probability at least 2/3. If we run it again, a second (independent)
random string r2 is consumed and another (independent) answer is given, again correct
with probability at least 2/3. After t such trials and the consumption of random strings
r1, . . . , rt, P produces t answers. We expect at least 2/3 of these to be correct, and Chernoﬀ
bounds (with δ = Θ(1) and µ = Θ(t)) imply that at least 60% of these answers are correct
with probability at least 1

.
}
We continue the thought experiment by taking a Union Bound over the 2n

2n = 22n
·
choices of the input (x, y). With probability at least 1
over the choice of
r1, . . . , rt, for every input (x, y), running the protocol P with these random strings yields at
least .6t (out of t) correct answers. In this event, the single sequence r1, . . . , rt of random
strings “works” simultaneously for all inputs (x, y). Provided we take t = cn with a large
enough constant c, this probability is positive. In particular, such a set r1, . . . , rt of random
strings exist.

Θ(t)

Θ(t)

22n

exp

exp

{−

{−

−

−

}

·

Here is the private-coin protocol.

(0) Before receiving their inputs, Alice and Bob agree on a set of strings r1, . . . , rt with
the property that, for every input (x, y), running P t times with the random strings
r1, . . . , rt yields at least 60% correct answers.

(1) Alice picks an index i

1, 2, . . . , t

uniformly at random and sends it to Bob. This

log2 t = Θ(log n) bit of communication (recall t = Θ(n)).

∈ {

}

requires

≈

(2) Alice and Bob simulate the private-coin protocol P as if they had public coins given

by ri.

By the deﬁning property of the ri’s, this (private-coin) protocol has error 40%. As usual,
this can be reduced to 1/3 via a constant number of independent repetitions followed by
taking the majority answer. The resulting communication cost is O(c + log n), as claimed.
(cid:4)



<!-- pdf-page: 13 -->
62

Boot Camp on Communication Complexity

We stated and proved Theorem 4.9 for general protocols, but the exact same statement

holds (with the same proof) for the one-way protocols that we studied in Lectures 1– 3.

4.3.3 Distributional Complexity

Randomized protocols are signiﬁcantly harder to reason about than deterministic ones. For
example, we’ve seen that a deterministic protocol can be thought of as a partition of the input
space into rectangles. A randomized protocol is a distribution over such partitions. While a
deterministic protocol that computes a function f induces only monochromatic rectangles,
this does not hold for randomized protocols (which can err with some probability).

We can make our lives somewhat simpler by using Yao’s Lemma to translate distributional
lower bounds for deterministic protocols to worst-case lower bounds for randomized protocols.
Recall the lemma from Lecture 2 (Lemma 2.3).

Lemma 4.10 (Yao 1983) Let D be a distribution over the space of inputs (x, y) to a
communication problem, and (cid:15)

2 ). Suppose that every deterministic protocol P with

(0, 1

∈
(x,y)∼D[P wrong on (x, y)]

Pr

(cid:15)

≤

has communication cost at least k. Then every (public-coin) randomized protocol R with
(two-sided) error at most (cid:15) on every input has communication cost at least k.

We proved Lemma 2.3 in Lecture 2 for one-way protocols, but the same proof holds
verbatim for general communication protocols. Like in the one-way case, Lemma 2.3 is a
“complete” proof technique — whatever the true randomized communication complexity,
there is a hard distribution D over inputs that can in principle be used to prove it (recall
the Exercises).

Summarizing, proving lower bounds for randomized communication complexity reduces

to:

1. Figuring out a “hard distribution” D over inputs.

2. Proving that every low-communication deterministic protocol has large error w.r.t.

inputs drawn from D.

Of course, this is usually easier said than done.

4.3.4 Case Study: Disjointness

Overview

We now return to the Disjointness problem. In Lecture 2 we proved that the one-way
randomized communication complexity of this problem is linear (Theorem 2.2). We did this
by reducing Index to Disjointness— the former is just a special case of the latter, where



<!-- pdf-page: 14 -->
4.3 Randomized Protocols

63

one player has a singleton set (i.e., a standard basis vector). We used Yao’s Lemma (with D
the uniform distribution) and a counting argument (about the volume of small-radius balls
in the Hamming cube, remember?) to prove that the one-way randomized communication
complexity of Index is Ω(n). Unfortunately, for general communication protocols, the
communication complexity of Index is obviously O(log n) — Bob can just send his index
i to Alice using
log2 n bits, and Alice can compute the function. So, it’s back to the
drawing board.

≈

The following is a major and useful technical achievement.

Theorem 4.11 (Kalyanasundaram and Schnitger 1992; Razborov 1992) The ran-
domized communication complexity of Disjointness is Ω(n).

Theorem 4.11 was originally proved in Kalyanasundaram and Schnitger (1992); the simpliﬁed
proof in Razborov (1992) has been more inﬂuential. More recently, all the cool kids prove
Theorem 4.11 using “information complexity” arguments; see Bar-Yossef et al. (2002a).

If you only remember one result from the entire ﬁeld of communication complexity, it
should be Theorem 4.11. The primary reason is that the problem is unreasonably eﬀective for
proving lower bounds for other algorithmic problems — almost every subsequent lecture will
include a signiﬁcant example. Indeed, many algorithm designers simply use Theorem 4.11
as a “black box” to prove lower bounds for other problems, without losing sleep over its
proof.56 As a bonus, proofs of Theorem 4.11 tend to showcase techniques that are reusable
in other contexts.

For a trivial consequence of Theorem 4.11 — see future lectures for less obvious ones —
let’s return to the setting of streaming algorithms. Lectures 1 and 2 considered only one-pass
algorithms. In some contexts, like a telescope that generates an exobyte of data per day, this
is a hard constraint. In other settings, like database applications, a small constant number
of passes over the data might be feasible (as an overnight job, for example). Communication
complexity lower bounds for one-way protocols say nothing about two-pass algorithms, while
those for general protocols do. Using Theorem 4.11, all of our Ω(m) space lower bounds for
1-pass algorithms become Ω(m/p) space lower bounds for p-pass algorithms, via the same
reductions.7 For example, we proved such lower bounds for computing F∞, the highest
frequency of an element, even with randomization and approximation, and for computing
F0 or F2 exactly, even with randomization.

So how would one go about proving Theorem 4.11? Recall that Yao’s Lemma reduces
the proof to exhibiting a hard distribution D (a bit of dark art) over inputs and proving

5Similar to, for example, the PCP Theorem and the Parallel Repetition Theorem in the context of

hardness of approximation (see e.g. Arora and Lund (1997)).

6There’s no shame in this — life is short and there’s lots of theorems that need proving.
7A p-pass space-s streaming algorithm S induces a communication protocol with O(ps) communication,
where Alice and Bob turn their inputs into data streams, repeatedly feed them into S, repeatedly sending
the memory state of S back and forth to continue the simulation.



<!-- pdf-page: 15 -->
64

Boot Camp on Communication Complexity

that all low-communication deterministic protocols have large error with respect to D (a
potentially tough math problem). We next discuss each of these steps in turn.

Choosing a Hard Distribution

The uniform distribution over inputs is not a hard distribution for Disjointness. What
is the probability that a random input (x, y) satisﬁes f (x, y) = 1? Independently in each
coordinate i, there is a 25% probability that xi = yi = 1. Thus, f (x, y) = 1 with probability
(3/4)n. This means that the zero-communication protocol that always outputs “not disjoint”
has low error with respect to this distribution. The moral is that a hard distribution D must,
at the very least, have a constant probability of producing both “yes” and “no” instances.

The next idea, motivated by the Birthday Paradox, is to deﬁne D such that each of Alice
√n. Elementary calculations
and Bob receive a random subset of
show that a random instance (x, y) from D has a constant probability of satisfying each of
f (x, y) = 1 and f (x, y) = 0.

1, 2, . . . , n

of size

≈

}

{

An obvious issue with this approach is that there is a trivial deterministic protocol that
uses O(√n log n) communication and has zero error: Alice (say) just sends her whole input
to Bob by describing each of her √n elements explicitly by name (
log2 n bits each). So
there’s no way to prove a linear communication lower bound using this distribution. Babai
et al. (1986) prove that one can at least prove a Ω(√n) communication lower bound using
this distribution, which is already quite a non-trivial result (more on this below). They also
showed that for every product distribution D — meaning whenever the random choices of
x and of y are independent — there is a zero-error deterministic protocol that uses only
O(√n log n) bits of communication (see the Exercises).8

≈

Summarizing, if we believe that Disjointness really requires Ω(n) communication to
solve via randomized protocols, then we need to ﬁnd a distribution D that meets all of the
following criteria.

1. There is a constant probability that f (x, y) = 1 and that f (x, y) = 0. (Otherwise, a

constant protocol works.)

2. Alice and Bob need to usually receive inputs that correspond to sets of size Ω(n).

(Otherwise, one player can explicitly communicate his or her set.)

3. The random inputs x and y are correlated. (Otherwise, the upper bound from Babai

et al. (1986) applies.)

4. It must be mathematically tractable to prove good lower bounds on the error of all
deterministic communication protocols that use a sublinear amount of communication.

8This does not imply that a linear lower bound is impossible. The proof of the converse of Lemma 2.3 —
that a tight lower bound on the randomized communication complexity of a problem can always be proved
through a distributional lower bound for a suitable choice of D — generally makes use of distributions in
which the choices of x and y are correlated.



<!-- pdf-page: 16 -->
4.3 Randomized Protocols

65

Razborov (1992) proposed a distribution that obviously satisﬁes the ﬁrst three properties

and, less obviously, also satisﬁes the fourth. It is:

1. With probability 75%:

a) (x, y) is chosen uniformly at random subject to:

i. x, y each have exactly n/4 1’s;
ii. there is no index i

1, 2, . . . , n

∈ {

with xi = yi = 1 (so f (x, y) = 1).

}

2. With probability 25%:

a) (x, y) is chosen uniformly at random subject to:

i. x, y each have exactly n/4 1’s;
ii. there is exactly one index i

1, 2, . . . , n

with xi = yi = 1 (so f (x, y) = 0).

}

∈ {

Note that in both cases, the constraint on the number of indices i with xi = yi = 0 creates
correlation between the choices of x and y.

Proving Error Lower Bounds via Corruption Bounds

Even if you’re handed a hard distribution over inputs, there remains the challenging task of
proving a good error lower bound on low-communication deterministic protocols. There are
multiple methods for doing this, with the corruption method being the most successful one
so far. We outline this method next.

At a high level, the corruption method is a natural extension of the covering arguments
of Section 4.2 to protocols that can err. Recall that for deterministic protocols, the covering
approach argues that every covering of the matrix M (f ) of the function f by monochromatic
rectangles requires a lot of rectangles. In our examples, we only bothered to argue about
the 1-inputs of the function.9 We’ll do something similar here, weighted by the distribution
D and allowing errors — arguing that there’s signiﬁcant mass on the 1-inputs of f , and that
a lot of nearly monochromatic rectangles are required to cover them all.

Precisely, suppose you have a distribution D over the inputs of a problem so that the
“1-mass” of D, meaning Pr(x,y)∼D[f (x, y) = 1], is at least a constant, say .5. The plan is to
prove two properties.

(1) For every deterministic protocol P with error at most a suﬃciently small constant (cid:15), at
least 25% of the 1-mass of D is contained in “almost monochromatic 1-rectangles” of P
(deﬁned below). We’ll see below that this is easy to prove in general by an averaging
argument.

9Since f has only two outputs, it’s almost without loss to pick a single output z ∈ {0, 1} of f and lower

bound only the number of monochromatic rectangles needed to cover all of the z’s.



<!-- pdf-page: 17 -->
66

Boot Camp on Communication Complexity

(2) An almost monochromatic 1-rectangle contains at most 2−c mass of the distribution
D, where c is as large as possible (ideally c = Ω(n)). This is the hard step, and the
argument will be diﬀerent for diﬀerent functions f and diﬀerent input distributions D.

If we can establish (1) and (2), then we have a lower bound of Ω(2−c) on the number of
rectangles induced by P , which proves that P uses communication Ω(c).10

Here’s the formal deﬁnition of an almost monochromatic 1-rectangle (AM1R) R = A

of a matrix M (f ) with respect to an input distribution D:

B

×

Pr(x,y)∼D[(x, y)

∈

R and f (x, y) = 0]

8(cid:15)

·

≤

Pr(x,y)∼D[(x, y)

∈

R and f (x, y) = 1] . (4.2)

Here’s why property (1) is true in general. Let P be a deterministic protocol with
error at most (cid:15) with respect to D. Since P is deterministic, it partitions the matrix M (f )
into rectangles, and in each rectangle, P ’s output is constant. Let R1, . . . , R` denote the
rectangles in which P outputs “1.”

At least 50% of the 1-mass of D — and hence at least 25% of D’s overall mass — must
be contained in R1, . . . , R`. For if not, on at least 25% of the mass of D, f (x, y) = 1 while P
outputs “0”. This contradicts the assumption that P has error (cid:15) with respect to D (provided
(cid:15) < .25).

Also, at least 50% of the mass in R1, . . . , R` must lie in AM1Rs. For if not, using (4.2)
and the fact that the total mass in R1, . . . , R` is at least .25, it would follow that D places
more than 8(cid:15)
.125 = (cid:15) mass on 0-inputs in R1, . . . , R`. Since P outputs “1” on all of these
inputs, this contradicts the assumption that P has error at most (cid:15) with respect to D. This
completes the proof of step (1), which applies to every problem and every distribution D
over inputs with 1-mass at least .5.

·

Step (2) is diﬃcult and problem-speciﬁc. Babai et al. (1986), for their input distribution
D over Disjointness inputs mentioned above, gave a proof of step (2) with c = Ω(√n),
thus giving an Ω(√n) lower bound on the randomized communication complexity of the
problem. Razborov (1992) gave, for his input distribution, a proof of step (2) with c = Ω(n),
implying the desired lower bound for Disjointness. Sadly, we won’t have time to talk
about these and subsequent proofs (as in Bar-Yossef et al. (2002a)); perhaps in a future
course.

10Why call it the “corruption method”? Because the argument shows that, if a deterministic protocol has
low communication, then most of its induced rectangles that contain 1-inputs are also “corrupted” by lots of
0-inputs — its rectangles are so big that (4.2) fails. In turn, this implies large error.


