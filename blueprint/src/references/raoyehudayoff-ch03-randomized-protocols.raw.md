<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: 3eebfb23ab53af2c69ef3332811cbc6071b7afcebf95315df2460122cc6c3788 -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
3

Randomized Protocols

Access to randomness is an enabling feature in many compu-
tational processes, and it is useful in communication protocols as
well. We start with some examples of protocols where the use of
randomness gives an advantage that cannot be matched by determin-
istic protocols, before deﬁning randomized protocols formally and
proving some basic facts about them. We do not discuss any lower
bounds on randomized communication in this chapter. The lower
bounds are proved in Chapter 5 and Chapter 6.

Equality Suppose Alice and Bob are each given access to n bit strings
x, y, and want to know if these strings are the same or not (1.1).
We have shown that at least n + 1 bits of communication are
required if the communication is deterministic.

However, there is a simple randomized protocol. Alice and Bob
sample a random function h : {0, 1}n → {0, 1}k and Alice sends
h(x) to Bob. If x = y, we will have that h(x) = h(y). On the other
hand, if x 6= y, the probability that h(x) = h(y) is at most 2−k.
So the protocol can compute equality with a small probability
of failure, even if the communication is a constant number of
bits. This protocol may seem dissatisfying, because although
the communication is small, the number of shared random bits
required is very large (2nk). However, there is a slightly more
complicated protocol that uses very few random bits.
Alice and Bob agree on an error correcting code1 C : {0, 1}n →
{0, 1}m. It can be shown that a random function is a code with
high probability, but even explicit constructions of good codes
are known. Given the code, Alice can pick k random coordinates
of the code and send them to Bob. Bob will check whether these
coordinates are consistent with his input. This takes k log n bits of
communication, and now the probability of making an error is at
most 2−Ω(k).

Input: Alice knows x ∈ {0, 1}n,

Bob knows y ∈ {0, 1}n.
Output: Whether or not x = y.

Alice and Bob sample a random
function h : {0, 1}n → {0, 1}k;
Alice sends Bob h(x);
Bob announces whether
h(x) = h(y);

Figure 3.1: Public-coin Protocol for
equality.

Input: Alice knows x ∈ {0, 1}n,

Bob knows y ∈ {0, 1}n.
Output: Whether or not x = y.

Alice and Bob agree on a good
code C : {0, 1}n → {0, 1}m;
Alice picks k coordinates
i1, . . . , ik ∈ [m] at random;
Alice sends Bob
(i1, C(x)i1 ), . . . , (ik, C(x)ik );
Bob announces whether this is
equal to (i1, C(y)i1 ), . . . , (ik, C(y)ik );

Figure 3.2: Private-coin Protocol for
equality.

1 This is a function that maps n bits
to m = O(n) bits, such that if x 6= y,
then C(x) and C(y) differ in Ω(m)
coordinates.



<!-- pdf-page: 2 -->
46 communication complexity

Greater-than Suppose Alice and Bob are given numbers x, y ∈ [n]
and want to know which one is greater (1.3). We have seen that
any deterministic protocol for this problem requires log n + 1 bits
of communication. However, there is a randomized protocol that
requires only O(log log n) bits of communication.

Here we describe a protocol that requires only O(log log n ·
log log log n) communication. The inputs x, y can be encoded by
`-bit binary strings, where ` = log n. To determine whether x ≥ y,
it is enough to ﬁnd the most signiﬁcant bits in x, y where x, y are
not the same. We use the randomized protocol for equality, and
binary search, to achieve this. In the ﬁrst step, Alice and Bob will
use the protocol for equality to exchange k bits that determine
whether the `/2 most signiﬁcant bits of x and y are the same. If
they are the same, the parties continue with the remaining bits. If
not, the parties discard the second half of their strings. In this way,
after log ` steps, they ﬁnd the ﬁrst bit of difference in their inputs.
We need to set k = log log ` for this process to work.

k-Disjointness Suppose Alice and Bob are given 2 sets X, Y ⊆ [n] of
size at most k, and want to know if these sets intersect or not. We
used the rank method to argue that at least log (n
k) ≈ k log(n/k)
bits of communication are required. Here we give a randomized
protocol2 that requires only O(k) bits of communication3, which is
more efﬁcient when k (cid:28) n.

Alice and Bob sample a sequence of sets R1, R2, . . . ⊆ [n], un-
formly at random. They exchange 2 bits to announce whether or
not their sets are empty. If neither set is empty, Alice announces
the index of the ﬁrst set Ri that contains her set, and Bob an-
nounces the index of the ﬁrst set Rj that contains his set. Now
Alice can safely replace her set with X ∩ Rj, and Bob can replace
his set with Y ∩ Ri. If at any point one of the parties is left with an
empty set, they can safely conclude that the inputs were disjoint.
We will argue that if the sets are disjoint, this process terminates
after O(k) bits of communication.

Assume that X, Y are disjoint. Let us start by analyzing the
expected number of bits that will be communicated in the ﬁrst
step. We claim:

Claim 3.1. E [i] = 2|X|, E [j] = 2|Y|.

Proof. The probability that the ﬁrst set of the sequence contains
X is exactly 2−|X|. In the event that it does not contain X, we are
picking the ﬁrst set that contains X from the rest of the sequence.

The protocol requiring O(log log n)
bits of communication is described in
Exercise 3.1.

Input: Alice knows x ∈ {0, 1}`
Bob knows y ∈ {0, 1}`
.
Output: Largest i such that xi 6= yi,
if such an i exists.

,

Let J = [n];
while |J| > 1 do

Let J0 be the ﬁrst |J|/2
elements of J;
Both parties use shared
randomness to sample a
random function
h : {0, 1}|J0 | → {0, 1}2 log log `
Alice sends h evaluated on the
bits in J0, h(xJ0 );
Bob announces whether or not
h(xJ0 ) = h(yJ0 );
if h(xJ0 ) = h(yJ0 ) then

;

Alice and Bob replace
J = J \ J0;

else

Alice and Bob replace
J = J0;

end
Both parties announce xJ, yJ;

end

Figure 3.3: Public-coin protocol for
greater than.

2 Håstad and Wigderson, 2007

3 Later, we show that Ω(k) bits are
required.



<!-- pdf-page: 3 -->
randomized protocols

47

Input: Alice knows X ⊆ [n], Bob

knows Y ⊆ [n].

Output: Whether or not X ∩ Y = ∅

while |X| > 1 and |Y| > 1 and at
most 120k + 20 bits have been
communicated so far do

Alice and Bob use shared
randomness to sample
random subsets
R1, R2, . . . ⊆ [n];
Alice sends Bob the smallest i
such that X ⊆ Ri;
Bob sends Alice the smallest j
such that Y ⊆ Rj;
Alice replaces X = X ∩ Rj;
Bob replaces Y = Y ∩ Ri;

end
if X = ∅ or Y = ∅ then

Alice and Bob conclude that
the sets were disjoint;

else

end

Alice and Bob conclude that
the sets were intersecting;

Figure 3.4: Public-coin protocol for
k-disjointness.

4 since log is concave

Thus:

E [i] = 2−|X| · 1 + (1 − 2−|X|) · (E [i] + 1)

⇒ E [i] = 2|X|.

The bound on the expected value of j is the same.

Since a number of size i can be communicated with at most
2 log i bits, the number of bits communicated to transmit i, is at
most4

E [2 log i] ≤ 2 log E [i] = 2|X|
E [2 log j] ≤ 2 log E [j] = 2|Y|

(3.1)

Next we argue that when X ∩ Y = ∅, the above communication

process must terminate quickly.

Claim 3.2. If X ∩ Y = ∅, the expected number of bits communicated by
the protocol is at most 6|X| + 6|Y| + 2.

Proof. Notice that as the protocol continues, the sets X, Y can
only get smaller. So we can prove the bound by induction on
the size of the sets X, Y. For the base, case, if X or Y is empty, at
most 2 ≤ 6(|X| + |Y|) + 2 bits are communicated. If both X and
Y are non-empty, (3.1) shows that the expected number of bits
communicated in the ﬁrst step is 2 + 2|X| + 2|Y|. By induction, the
expected number of bits communicated in the rest of the protocol
is E
+ 2. But observe that since X, Y are
6(|X ∩ Rj| + |Y ∩ Ri|)
(cid:3)
assumed to be disjoint, E
= |X|/2, and E [|Y ∩ Ri|] =
|X ∩ Rj|
(cid:2)
|Y|/2. Thus the total number of bits communicated is

(cid:2)

(cid:3)

2 + 2|X| + 2|Y| + (6/2)|X| + (6/2)|Y| + 2

= 6|X| + 6|Y| + 2 − (|X| + |Y| − 2)

≤ 6|X| + 6|Y| + 2,

as required.

Claim 3.2 means that if X, Y are disjoint, the expected number
of step taken by the process above is 6|X| + 6|Y| + 2. By Markov’s
inequality, the probability that the protocol communicates more
than 10 · (6|X| + 6|Y| + 2) bits is at most 1/10. Thus if we run
this process until 120k + 20 bits have been communicated, the
probability of making an error is at most 1/10.

Variants of Randomized Protocols

A randomized protocol is a deterministic protocol where each
party has access to a random string, in addition to the inputs to



<!-- pdf-page: 4 -->
48 communication complexity

the protocol. The random string is sampled independently from
the inputs, but may have an arbitrary distribution. We say that the
protocol uses public coins if all parties have access to a common
shared random string. We say that the protocol uses private coins if
each party samples an independent random string. Every private
coin protocol can be simulated by a public coin protocol. There are at
least two ways to quantify the errors made by a protocol:

Worst-case We say that a randomized protocol has error e in the

worst-case if the probability that the protocol makes an error is at
most e on every input.

Average-case Given a distribution on inputs µ, we say that the proto-
col has error e with respect to µ if the probability that the protocol
makes an error is at most e when the inputs are sampled from µ.

When a protocol has error e < 1/2 in the worst case, we can run it
several times and take the majority output to reduce the error. If we
repeat the protocol k times, and output the most frequent output in
all of the runs, there will be an error in the output only if at least k/2
of the runs computed the wrong answer. By the Chernoff bound, the
probability of error is at most 2−Ω(k(1/2−e)2).

Worst-case and average-case errors are related by via Yao’s mini-

max principle:

Theorem 3.3. The communication complexity of computing a function
g in the worst-case with error at most e is equal to the maximum, over all
distributions µ, of the communication complexity of computing g with error
at most e with respect to µ.

Theorem 3.3 can be proved by appealing to von Neumann’s mini-

max principle5:

Theorem 3.4. Let M be an m × n matrix. Then

min
x≥0

max
y≥0

xMy = max
y≥0

min
x≥0

xMy,

where x is a 1 × m row vector with ∑i xi = 1, and y is a n × 1 column
vector with ∑j yj = 1.

Let us see how to prove Theorem 3.3. One direction is easy: if
there is a protocol that computes g with error e in the worst case,
then the same protocol must compute g with error e in the average
case, no matter what the input distribution is.

Now suppose we know that for every distribution µ, there is
a c-bit protocol that computes g with error e in the average case.
Consider the boolean matrix M where every row corresponds to a de-
terministic communication protocol, and every column corresponds

We shall soon see a partial converse:
every public coin protocol can be
simulated with private coins, with a
small increase in the communication

If a randomized protocol never makes
an error, we can ﬁx the randomness to
obtain a deterministic protocol that is
always correct.

The worst-case error is e if and only if
the error is e under every distribution
on inputs.

If a randomized protocol makes no
errors, we can ﬁx the randomness to
obtain a deterministic protocol that
comptes the function.

5 von Neumann, 1928

The minimax principle can also be seen
as a consequence of linear program-
ming duality.



<!-- pdf-page: 5 -->
randomized protocols

49

6 Newman, 1991

It is known that computing whether or
not two n-bit strings are equal requires
Ω(log n) bits of communication if only
private coins are used. This shows that
Theorem 3.5 is tight.

to an input to the protocol, such that

1 if protocol i computes g correctly on input j,

0 otherwise.

Mi,j = 




A distribution on the inputs corresponds to a choice of y ≥ 0 such
that ∑j yj = 1. Since a randomized protocol can be thought of as a
distribution on deterministic protocols, a randomized protocol corre-
sponds to a choice of x ≥ 0 such that ∑i xi = 1. The probability that
a ﬁxed randomized protocol x makes an error when the inputs come
from the distribution y is exactly xMy. Thus maxy≥0 minx≥0 xMy ≤ e.
Theorem 3.4 implies that minx≥0 maxy≥0 xMy ≤ e as well, which is
exactly what we want to prove. There is a ﬁxed randomized protocol
that has error at most e under every distribution on inputs.

Public Coins vs Private Coins

While every private coin protocol can be simulated by a public
coin protocol, can every private coin protocol be simulated by a
public coin protocol? Such a simulation is possible6, up to a small
additive loss in communication:

Theorem 3.5. If g : {0, 1}n × {0, 1}n → {0, 1} can be computed with c bits
of communication, and error e in the worst case, then it can be computed by
a private coin protocol with c + log(n/e2) + O(1) bits of communication,
and error 2e in the worst case.

Proof. We use the probabilistic method to ﬁnd the required private
coin protocol. Let us pick t independent random strings, each of
which can be used as the randomness for the given private-coin
protocol.

For any ﬁxed input, some of these t random strings lead to the
public coin protocol computing the right answer, and some of the
lead to the protocol computing the wrong answer. By the Chernoff
bound, the probability that 1 − 2e fraction of the t strings lead to the
wrong answer is at most 2−Ω(e2t). We set t = O(2n/e2) to be large
enough so that this probability is less than 2−2n. Then by the union
bound, we get that the probability that 2et of these strings give the
wrong answer for any input is less than 1. Thus there must be some
ﬁxed strings with this property.

The private coin protocol is now simple. Alice samples one of the
t strings and sends its index to Bob, which takes at most log(n/e2) +
O(1) bits. Alice and Bob then run the original public coin protocol.



<!-- pdf-page: 6 -->
50 communication complexity

Nearly Monochromatic Rectangles

Monochromatic rectangles proved to be a very useful concept
to understand deterministic protocols. A similar role is played by
nearly monochromatic rectangles when trying to understand random-
ized protocols.

Deﬁnition 3.6. Given a distribution µ on inputs, we say that a rectangle R
has bias (1 − e) under a function g if there is a constant b so that

[g(x, y) = b|(x, y) ∈ R] ≥ 1 − e.

Pr
µ

Such a rectangle is called (1 − e)-monochromatic.

We would like to claim that a protocol with small error e induces
a partition of the space into nearly monochromatic rectangles. That
is not quite true, but we can claim that the average rectangle must be
very close to being monochromatic:

Theorem 3.7. If there is a c-bit protocol that computes g with error e under
a distribution µ, then you can partition the inputs into 2c rectangles, such
that the average bias of a random rectangle from the partition is at least 1 − e.

Applying Markov’s inequality to this average gives that there must

be many large nearly monochromatic rectangles:

Theorem 3.8. If there is a c-bit protocol that computes g with error e under
µ, then for every `, there are disjoint (1 − `e)-monochromatic rectangles
R1, R2, . . . , R2c such that Prµ[(x, y) ∈ ∪iRi] ≥ 1 − 1/`.

Proof. Since we can always ﬁx the randomness of the protocol in
the best way, we can assume that the protocol is deterministic. By
Theorem 1.7, we know that the protocol induces a partition of the
space into 2c rectangles. Consider all the rectangles that are not
(1 − `e)-monochromatic. If the probability that the input lands in one
of these rectangles is bigger than 1/`, the error of the protocol will be
bigger than e. Thus the inputs must land in a (1 − `e)-monochromatic
rectangle with probability at least 1 − 1/`.

As a corollary, we get:

Corollary 3.9. If there is a c-bit protocol that computes g with error e under
µ, then for every `, there is a (1 − `e)-monochromatic rectangle of density at
least 2−c(1 − 1/`).

Theorem 3.8 will be instrumental to
prove lower bounds on randomized
protocols



<!-- pdf-page: 7 -->
randomized protocols

51

Exercise 3.1

In this exercise we will develop a randomized protocol for greater-

than that requires only O(log log n) bits of communication. Let
x, y ∈ {0, 1}`
such that xi 6= yi.

be two strings. Alice and Bob want to ﬁnd the smallest i

Exercise 3.2

In this exercise, we design a randomized protocol for ﬁnding the
ﬁrst difference between two n-bit strings. Alice and Bob are given n
bit strings x 6= y and want to ﬁnd the smallest i such that xi 6= yi. In
class we saw how to accomplish this using O(log n log log n) bits of
communication. Here we do it with O(log n) bits of communication.

Deﬁne a rooted tree as follows. Every vertex will correspond to an
interval of coordinates from [n]. The root corresponds to the interval
I = [n]. Every internal vertex corresponding to the interval I will
have two children, the left child corresponding to the ﬁrst half of I
and the right child corresponding to the right half of I. This deﬁnes
a tree of depth log n, where the leaves correspond to intervals of
size 1 (i.e. coordinates) of the input. At each leaf, attach a path of
length 3 log n. Every vertex of this path represents the same interval
of size 1. The depth of the tree is now 4 log n.

1. Fill in the details of the following protocol. Prove an upper bound
on the expected number of bits communicated and a lower bound
on the success probability.

The players use their inputs and hashing to start at the root of the
tree and try to navigate to the smallest interval that contains the
index i that they seek. In each step, the players will either move to
a parent or a child of the node that they are at. When the players
are at a vertex that corresponds to the interval I, they should ﬁrst
exchange O(1) hash bits to conﬁrm that the ﬁrst difference does
lie in I. If this hash shows that the ﬁrst difference does not lie in
I, they should move to the parent of the current node. Otherwise,
they exchange O(1) hash bits and use this to decide on which
child of the current node to move to. Once the players reach the
nodes of the tree that correspond to intervals of size 1, they use
their hashes to either move to a parent or child.

2. Argue that as long as the number of nodes where the protocol
made the right choice exceeds the number of nodes where the
players made the wrong choice by log n, the protocol you deﬁned
does succeed in computing i.

3. Use the Chernoff bound to argue that the number of hashes that
gives the right answer is high enough to ensure that the protocol



<!-- pdf-page: 8 -->
52 communication complexity

succeeds with high probability on any input.

Exercise 3.3

Show that if the inputs to greater-than are sampled uniformly
and independently, then there is a protocol that communicates only
O(log(1/e)) bits and has error at most e under this distribution.


