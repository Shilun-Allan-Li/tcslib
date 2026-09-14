<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: 043896d6545f3608f18c8cfb639513f910f8728adce9d936f568118df872e315 -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
12

Data Streams: Algorithms and Lower Bounds

1.6 Can We Do Better?

Theorem 1.1 is a fantastic result. But a good algorithm designer is never satisﬁed, and
always wants more. So what are the weaknesses of the upper bounds that we’ve proved so
far?

1. We only have interesting positive results for F0 and F2 (and maybe F1, if you want to

count that). What about for k > 2 and k =

?
∞

2. Our F0 and F2 algorithms only approximate the corresponding frequency moment.

Can we compute it exactly, possibly using a randomized algorithm?

3. Our F0 and F2 algorithms are randomized, and with probability δ fail to provide a
good approximation. (Also, they are Monte Carlo algorithms, in that we can’t tell
when they fail.) Can we compute F0 or F2 deterministically, at least approximately?

4. Our F0 and F2 algorithms use Ω(log n) space. Can we reduce the dependency of the

space on the universe size?11

5. Our F0 and F2 algorithms use Ω((cid:15)−

1 be improved?
2 dependence can be painful in practice, where you might want to take (cid:15) = .01,
1,

The (cid:15)−
resulting in an extra factor of 10,000 in the space bound. An improvement to
for example, would be really nice.

2) space. Can the dependence on (cid:15)−

(cid:15)−

≈

Unfortunately, we can’t do better — the rest of this lecture and the next (and the exercises)
explain why all of these compromises are necessary for positive results. This is kind of
amazing, and it’s also pretty amazing that we can prove it without overly heavy machinery.
Try to think of other basic computational problems where, in a couple hours of lecture
and with minimal background, you can explain complete proofs of both a non-trivial upper
bound and an unconditional (independent of P vs. N P , etc.) matching lower bound.12

1.7 One-Way Communication Complexity

We next describe a simple and clean formalism that is extremely useful for proving lower
bounds on the space required by streaming algorithms to perform various tasks. The model
will be a quite restricted form of the general communication model that we study later
— and this is good for us, because the restriction makes it easier to prove lower bounds.
Happily, even lower bounds for this restricted model typically translate to lower bounds for
streaming algorithms.

11This might seem like a long shot, but you never know. Recall our comment about reducing the space

dependency on m from O(log m) to O(log log m) via probabilistic approximate counters.

12OK, comparison-based sorting, sure. And we’ll see a couple others later in this course. But I don’t

know of that many examples!



<!-- pdf-page: 2 -->
1.8 Connection to Streaming Algorithms

13

In general, communication complexity is a sweet spot. It is a general enough concept to
capture the essential hardness lurking in many diﬀerent models of computation, as we’ll see
throughout the course. At the same time, it is possible to prove numerous diﬀerent lower
bounds in the model — some of these require a lot of work, but many of the most important
ones are easier that you might have guessed. These lower bounds are “unconditional” —
they are simply true, and don’t depend on any unproven (if widely believed) conjectures like
P
= N P . Finally, because the model is so clean and free of distractions, it naturally guides
one toward the development of the “right” mathematical techniques needed for proving new
lower bounds.

In (two-party) communication complexity, there are two parties, Alice and Bob. Alice
b. Neither one has any idea what the
has an input x
}
∈ {
other’s input is. Alice and Bob want to cooperate to compute a Boolean function (i.e., a
predicate) f :
that is deﬁned on their joint input. We’ll discuss
several examples of such functions shortly.

a, Bob an input y

0, 1
{

0, 1
}

→ {

a
}

∈ {

× {

0, 1

0, 1

0, 1

}

}

b

For this lecture and the next, we can get away with restricting attention to one-way

communication protocols. All that is allowed here is the following:

1. Alice sends Bob a message z, which is a function of her input x only.

2. Bob declares the output f (x, y), as a function of Alice’s message z and his input y

only.

Since we’re interested in both deterministic and randomized algorithms, we’ll discuss both
deterministic and randomized one-way communication protocols.

The one-way communication complexity of a Boolean function f is the minimum worst-
case number of bits used by any one-way protocol that correctly decides the function. (Or
for randomized protocols, that correctly decides it with probability at least 2/3.) That is, it
is

min
P

max
x,y {

length (in bits) of Alice’s message z when Alice’s input is x

,

}

where the minimum ranges over all correct protocols.

Note that the one-way communication complexity of a function f is always at most a,
since Alice can just send her entire a-bit input x to Bob, who can then certainly correctly
compute f . The question is to understand when one can do better. This will depend on
the speciﬁc function f . For example, if f is the parity function (i.e., decide whether the
total number of 1s in (x, y) is even or odd), then the one-way communication complexity of
f is 1 (Alice just sends the parity of x to Bob, who’s then in a position to ﬁgure out the
parity of (x, y)).

6


<!-- pdf-page: 3 -->
14

Data Streams: Algorithms and Lower Bounds

1.8 Connection to Streaming Algorithms

If you care about streaming algorithms, then you should also care about one-way communi-
cation complexity. Why? Because of the unreasonable eﬀectiveness of the following two-step
plan to proving lower bounds on the space usage of streaming algorithms.

1. Small-space streaming algorithms imply low-communication one-way protocols.

2. The latter don’t exist.

Both steps of this plan are quite doable in many cases.

Does the connection in the ﬁrst step above surprise you? It’s the best kind of statement
— genius and near-trivial at the same time. We’ll be formal about it shortly, but it’s worth
remembering a cartoon meta-version of the connection, illustrated in Figure 1.2. Consider
a problem that can be solved using a streaming algorithm S that uses space only s. How
can we use it to deﬁne a low-communication protocol? The idea is for Alice and Bob to
treat their inputs as a stream (x, y), with all of x arriving before all of y. Alice can feed
x into S without communicating with Bob (she knows x and S). After processing x, S’s
state is completely summarized by the s bits in its memory. Alice sends these bits to Bob.
Bob can then simply restart the streaming algorithm S seeded with this initial memory,
and then feed his input y to the algorithm. The algorithm S winds up computing some
function of (x, y), and Alice only needs to communicate s bits to Bob to make it happen.
The communication cost of the induced protocol is exactly the same as the space used by
the streaming algorithm.

Alice&
input&=&x&

Q(x)&

Bob&
input&=&y&

Q(x;&y)&

Figure 1.2 Why a small-space streaming algorithm induces a low-communication one-way protocol.
Alice runs the streaming algorithm on her input, sends the memory contents of the algorithm to
Bob, and Bob resumes the execution of the algorithm where Alice left oﬀ on his input.

1.9 The Disjointness Problem

To execute the two-step plan above to prove lower bounds on the space usage of streaming
algorithms, we need to come up with a Boolean function that (i) can be reduced to a



<!-- pdf-page: 4 -->
1.9 The Disjointness Problem

15

streaming problem that we care about and (ii) does not admit a low-communication one-way
protocol.

1.9.1 Disjointness Is Hard for One-Way Communication

If you only remember one problem that is hard for communication protocols, it should
be the Disjointness problem. This is the canonical hard problem in communication
complexity, analogous to satisﬁability (SAT) in the theory of N P -completeness. We’ll see
more reductions from the Disjointness problem than from any other in this course.

In an instance of Disjointness, both Alice and Bob hold n-bit vectors x and y. We
interpret these as characteristic vectors of two subsets of the universe
, with the
}
subsets corresponding to the “1” coordinates. We then deﬁne the Boolean function DISJ in
the obvious way, with DISJ(x, y) = 0 if there is an index i
with xi = yi = 1,
and DISJ(x, y) = 1 otherwise.

1, 2, . . . , n

1, 2, . . . , n

∈ {

{

}

To warm up, let’s start with an easy result.

Proposition 1.8 Every deterministic one-way communication protocol that computes the
function DISJ uses at least n bits of communication in the worst case.

That is, the trivial protocol is optimal among deterministic protocols.13 The proof follows
pretty straightforwardly from the Pigeonhole Principle — you might want to think it through
before reading the proof below.

−

−

Formally, consider any one-way communication protocol where Alice always sends at
1 bits. This means that, ranging over the 2n possible inputs x that Alice might
most n
have, she only sends 2n
1 distinct messages. By the Pigeonhole Principle, there are distinct
messages x1 and x2 where Alice sends the same message z to Bob. Poor Bob, then, has
to compute DISJ(x, y) knowing only z and y and not knowing x — x could be x1, or it
could be x2. Letting i denote an index in which x1 and x2 diﬀer (there must be one), Bob is
really in trouble if his input y happens to be the ith basis vector (all zeroes except yi = 1).
For then, whatever Bob says upon receiving the message z, he will be wrong for exactly one
of the cases x = x1 or x = x2. We conclude that the protocol is not correct.

A stronger, and more useful, lower bound also holds.

Theorem 1.9 Every randomized one-way protocol14 that, for every input (x, y), correctly
decides the function DISJ with probability at least 2
3 , uses Ω(n) communication in the worst
case.

13We’ll see later that the communication complexity remains n even when we allow general communication

protocols.

14There are diﬀerent ﬂavors of randomized protocols, such as “public-coin” vs. “private-coin” versions.

These distinctions won’t matter until next lecture, and we elaborate on them then.



<!-- pdf-page: 5 -->
16

Data Streams: Algorithms and Lower Bounds

The probability in Theorem 1.9 is over the coin ﬂips performed by the protocol (there is no
randomness in the input, which is “worst-case”). There’s nothing special about the constant
2
3 in the statement of Theorem 1.9 — it can be replaced by any constant strictly larger than
1
2 .

Theorem 1.9 is certainly harder to prove than Proposition 1.8, but it’s not too bad —
we’ll kick oﬀ next lecture with a proof.15 For the rest of this lecture, we’ll take Theorem 1.9
on faith and use it to derive lower bounds on the space needed by streaming algorithms.

1.9.2 Space Lower Bound for F

(even with Randomization and

∞

Approximation)

Recall from Section 1.6 that the ﬁrst weakness of Theorem 1.1 is that it applies only to F0
and F2 (and F1 is easy). The next result shows that, assuming Theorem 1.9, there is no
sublinear-space algorithm for computing F

, even probabilistically and approximately.

∞

Theorem 1.10 (Alon et al. 1999) Every randomized streaming algorithm that, for every
data stream of length m, computes F
.2) factor with probability at least
2/3 uses space Ω(min

to within a (1

±

∞

).
m, n
}

{

Theorem 1.10 rules out, in a strong sense, extending our upper bounds for F0, F1, F2 to
all Fk. Thus, the diﬀerent frequency moments vary widely in tractability in the streaming
model.16

Proof of Theorem 1.10: The proof simply implements the cartoon in Figure 1.2, with the
problems of computing F
(in the streaming model) and Disjointness (in the one-way
communication model). In more detail, let S be a space-s streaming algorithm that for
every data stream, with probability at least 2/3, outputs an estimate in (1
. Now
for solving the Disjointness
consider the following one-way communication protocol
problem (given an input (x, y)):

.2)F

±

P

∞

∞

1. Alice feeds into S the indices i for which xi = 1; the order can be arbitrary. Since

Alice knows S and x, this step requires no communication.

2. Alice sends S’s current memory state σ to Bob. Since S uses space s, this can be

communicated using s bits.

3. Bob resumes the streaming algorithm S with the memory state σ, and feeds into S

the indices i for which yi = 1 (in arbitrary order).

15A more diﬃcult and important result is that the communication complexity of Disjointness remains
Ω(n) even if we allow arbitrary (not necessarily one-way) randomized protocols. We’ll use this stronger
result several times later in the course. We’ll also brieﬂy discuss the proof in Section 4.3.4 of Lecture 4.

16For ﬁnite k strictly larger than 2, the optimal space of a randomized (1 ± (cid:15))-approximate streaming
1−1/2k) (Bar-Yossef et al., 2002a; Chakrabarti et al., 2003; Indyk and

algorithm turns out to be roughly Θ(n
Woodruﬀ, 2005). See the exercises for a bit more about these problems.



<!-- pdf-page: 6 -->
1.9 The Disjointness Problem

17

4. Bob declares “disjoint” if and only if S’s ﬁnal answer is at most 4/3.

∞

To analyze this reduction, observe that the frequency of an index i

in
the data stream induced by (x, y) is 0 if xi = yi = 0, 1 if exactly one of xi, yi is 1, and 2 if
of this data stream is 2 if (x, y) is a “no” instance of Disjointness, and
xi = yi = 2. Thus, F
is at most 1 otherwise. By assumption, for every “yes” (respectively, “no”) input (x, y), with
probability at least 2/3 the algorithm S outputs an estimate that is at most 1.2 (respectively,
is a
at least 2/1.2); in this case, the protocol
one-way protocol using s bits of communication, Theorem 1.9 implies that s = Ω(n). Since
the data stream length m is n, this reduction also rules out o(m)-space streaming algorithms
for the problem. (cid:4)

correctly decides the input (x, y). Since

1, 2, . . . , n

∈ {

P

P

}

Remark 1.11 (The Heavy Hitters Problem) Theorem 1.10 implies that computing
the maximum frequency is a hard problem in the streaming model, at least for worst-case
inputs. As mentioned, the problem is nevertheless practically quite important, so it’s
important to make progress on it despite this lower bound. For example, consider the
following relaxed version, known as the “heavy hitters” problem: for a parameter k, if there
are any elements with frequency bigger than m/k, then ﬁnd one or all such elements. When k
is constant, there are good solutions to this problem: the exercises outline the “Mishra-Gries”
algorithm, and the “Count-Min Sketch” and its variants also give good solutions (Charikar
et al., 2004; Cormode and Muthukrishnan, 2005).17 The heavy hitters problem captures
many of the applications that motivated the problem of computing F

.

∞

1.9.3 Space Lower Bound for Randomized Exact Computation of F0 and F2

In Section 1.6 we also criticized our positive results for F0 and F2 — to achieve them, we
had to make two compromises, allowing approximation and a non-zero chance of failure.
The reduction in the proof of Theorem 1.10 also implies that merely allowing randomization
is not enough.

Theorem 1.12 (Alon et al. 1999) For every non-negative integer k
ized streaming algorithm that, for every data stream, computes F
n, m
at least 2/3 uses space Ω(min
}
{

).

∞

= 1, every random-
exactly with probability

The proof of Theorem 1.12 is almost identical to that of Theorem 1.9. The reason the

proof of Theorem 1.9 rules out approximation (even with randomization) is because F
∞
diﬀers by a factor of 2 in the two diﬀerent cases (“yes” and “no” instances of Disjointness).

17This does not contradict Theorem 1.9 — in the hard instances of F∞ produced by that proof, all

frequencies are in {0, 1, 2} and hence there are no heavy hitters.

6


<!-- pdf-page: 7 -->
18

Data Streams: Algorithms and Lower Bounds

For ﬁnite k, the correct value of Fk will be at least slightly diﬀerent in the two cases, which
is enough to rule out a randomized algorithm that is exact at least two-thirds of the time.18
The upshot of Theorem 1.12 is that, even for F0 and F2, approximation is essential
to obtain a sublinear-space algorithm. It turns out that randomization is also essential —
(cid:15))-estimate of Fk (for
every deterministic streaming algorithm that always outputs a (1
any k
= 1) uses linear space Alon et al. (1999). The argument is not overly diﬃcult — see
the Exercises for the details.

±

1.10 Looking Backward and Forward

Assuming that randomized one-way communication protocols require Ω(n) communication
to solve the Disjointness problem (Theorem 1.9), we proved that some frequency moments
(in particular, F
) cannot be computed in sublinear space, even allowing randomization
and approximation. Also, both randomization and approximation are essential for our
sublinear-space streaming algorithms for F0 and F2.

∞

The next action items are:

1. Prove Theorem 1.9.

2. Revisit the ﬁve compromises we made to obtain positive results (Section 1.6). We’ve
showed senses in which the ﬁrst three compromises are necessary. Next lecture we’ll
see why the last two are needed, as well.

18Actually, this is not quite true (why?). But if Bob also knows the number of 1’s in Alice’s input (which
Alice can communicate in log2 n bits, a drop in the bucket), then the exact computation of Fk allows Bob
to distinguish “yes” and “no” inputs of Disjointness (for any k 6= 1).

6


<!-- pdf-page: 8 -->
Lecture 2

Lower Bounds for One-Way Communication: Disjointness, Index, and
Gap-Hamming

2.1 The Story So Far

0, 1
}
∈ {
0, 1
}
{

a, Bob has an input y
b
a
0, 1
}

Recall from last lecture the simple but useful model of one-way communication complexity.
b, and the goal is to compute
Alice has an input x
}
of the joint input (x, y). The players
a Boolean function f :
communicate as in Figure 2.1: Alice sends a message z to Bob as a function of x only (she
doesn’t know Bob’s input y), and Bob has to decide the function f knowing only z and
y (he doesn’t know Alice’s input x). The one-way communication complexity of f is the
smallest number of bits communicated (in the worst case over (x, y)) of any protocol that
computes f . We’ll sometimes consider deterministic protocols but are interested mostly in
randomized protocols, which we’ll deﬁne more formally shortly.

0, 1
}

→ {

× {

∈ {

0, 1

Alice&
input&=&x&

message&z&

Bob&
input&=&y&

decide&f&

Figure 2.1 A one-way communication protocol. Alice sends a message to Bob that depends only
on her input; Bob makes a decision based on his input and Alice’s message.

|

U

We motivated the one-way communication model through applications to streaming
U of elements
algorithms. Recall the data stream model, where a data stream x1, . . . , xm ∈
from a universe of n =
elements arrive one by one. The assumption is that there is
insuﬃcient space to store all of the data, but we’d still like to compute useful statistics
of it via a one-pass computation. Last lecture, we showed that very cool and non-trivial
2(log n +
positive results are possible in this model. We presented a slick and low-space (O((cid:15)−
log m) log 1
(cid:15))-
approximation of F2 =
0, 1, 2, . . . , m
}
is the number of times that j appears in the stream.) We also mentioned the main idea

j , the skew of the data. (Recall that fj ∈ {

δ )) streaming algorithm that, with probability at least 1

δ, computes a (1

U f 2

−

±

∈

|

j

P

19



<!-- pdf-page: 9 -->
20

Lower Bounds for One-Way Communication

(details in the homework) for an analogous low-space streaming algorithm that estimates
F0, the number of distinct elements in a data stream.

Low-space streaming algorithms S induce low-communication one-way protocols P , with
the communication used by P equal to the space used by S. Such reductions typically have
the following form. Alice converts her input x to a data stream and feeds it into the assumed
space-s streaming algorithm S. She then sends the memory of S (after processing x) to
Bob; this requires only s bits of communication. Bob then resumes S’s execution at the
point that Alice left oﬀ, and feeds a suitable representation of his input y into S. When
S terminates, it has computed some kind of useful function of (x, y) with only s bits of
communication. The point is that lower bounds for one-way communication protocols —
which, as we’ll see, we can actually prove in many cases — imply lower bounds on the space
needed by streaming algorithms.

Last lecture we used without proof the following result (Theorem 1.9).1

Theorem 2.1 The one-way communication complexity of the Disjointness problem is
Ω(n), even for randomized protocols.

We’ll be more precise about the randomized protocols that we consider in the next section.
n, which we view as
Recall that an input of Disjointness is deﬁned by x, y
, and the output should be “0” is there is
characteristic vectors of two subsets of
}
an index i with xi = yi = 1 and “1” otherwise.

1, 2, . . . , n
{

0, 1
}

∈ {

n, m
}
{

We used Theorem 1.9 to prove a few lower bounds on the space required by streaming
,
algorithms. A simple reduction showed that every streaming algorithm that computes F
∞
the maximum frequency, even approximately and with probability 2/3, needs linear (i.e.,
Ω(min
)) space. This is in sharp contrast to our algorithms for approximating F0 and
F2, which required only logarithmic space. The same reduction proves that, for F0 and F2,
exact computation requires linear space, even if randomization is allowed. A diﬀerent simple
argument (see the homework) shows that randomization is also essential for our positive
results: every deterministic streaming algorithm that approximates F0 or F2 up to a small
constant factor requires linear space.

In today’s lecture we’ll prove Theorem 1.9, introduce and prove lower bounds for a
couple of other problems that are hard for one-way communication, and prove via reductions
some further space lower bounds for streaming algorithms.

2.2 Randomized Protocols

There are many diﬀerent ﬂavors of randomized communication protocols. Before proving
any lower bounds, we need to be crystal clear about exactly which protocols we’re talking
about. The good news is that, for algorithmic applications, we can almost always focus

1Though we did prove it for the special case of deterministic protocols, using a simple Pigeonhole

Principle argument.



<!-- pdf-page: 10 -->
2.2 Randomized Protocols

21

on a particular type of randomized protocols. By default, we adopt the following four
assumptions and rules of thumb. The common theme behind them is we want to allow as
permissible a class of randomized protocols as possible, to maximize the strength of our
lower bounds and the consequent algorithmic applications.

Public coins. First, unless otherwise noted, we consider public-coin protocols. This
means that, before Alice and Bob ever show up, a deity writes an inﬁnite sequence of
perfectly random bits on a blackboard visible to both Alice and Bob. Alice and Bob
can freely use as many of these random bits as they want — it doesn’t contribute to the
communication cost of the protocol.

The private coins model might seem more natural to the algorithm designer — here,
Alice and Bob just ﬂip their own random coins as needed. Coins ﬂipped by one player are
unknown to the other player unless they are explicitly communicated.2 Note that every
private-coins protocol can be simulated with no loss by a public-coins protocol: for example,
Alice uses the shared random bits 1, 3, 5, etc. as needed, while Bob used the random bits 2,
4, 6, etc.

It turns out that while public-coin protocols are strictly more powerful than private-coin
protocols, for the purposes of this course, the two models have essentially the same behavior.
In any case, our lower bounds will generally apply to public-coin (and hence also private-coin)
protocols.

A second convenient fact about public-coin randomized protocols is that they are
equivalent to distributions over deterministic protocols. Once the random bits on the
blackboard have been ﬁxed, the protocol proceeds deterministically. Conversely, every
distribution over deterministic protocols (with rational probabilities) can be implemented
via a public-coin protocol — just use the public coins to choose from the distribution.

Two-sided error. We consider randomized algorithms that are allowed to error with
some probability on every input (x, y), whether f (x, y) = 0 or f (x, y) = 1. A stronger
requirement would be one-sided error — here there are two ﬂavors, one that forbids false
positives (but allows false negatives) and one the forbids false negatives (but allows false
positives). Clearly, lower bounds that apply to protocols with two-sided error are at least
as strong as those for protocols with one-sided error — indeed, the latter lower bounds
are often much easier to prove (at least for one of the two sides). Note that the one-way
protocols induces by the streaming algorithms in the last lecture are randomized protocols
with two-sided error. There are other problems for which the natural randomized solutions
have only one-sided error.3

constant error probabilities (cid:15)

Arbitrary constant error probability. A simple but important fact is that all
2 ) yield the same communication complexity, up to a
2Observe that the one-way communication protocols induced by streaming algorithms are private-coin
protocols — random coins ﬂipped during the ﬁrst half of the data stream are only available to the second
half if they are explicitly stored in memory.

(0, 1

3One can also consider “zero-error” randomized protocols, which always output the correct answer but

∈

use a random amount of communication. We won’t need to discuss such protocols in this course.



<!-- pdf-page: 11 -->
22

Lower Bounds for One-Way Communication

constant factor. The reason is simple: the success probability of a protocol can be boosted
through ampliﬁcation (i.e., repeated trials).4 In more detail, suppose P uses k bits on
communication and has success at least 51% on every input. Imagine repeating P 10000
times. To preserve one-way-ness of the protocol, all of the repeated trials need to happen in
parallel, with the public coins providing the necessary 10000 independent random strings.
Alice sends 10000 messages to Bob, Bob imagines answering each one — some answers will
be “1,” others “0” — and concludes by reporting the majority vote of the 10000 answers. In
expectation 5100 of the trials give the correct answer, and the probability that more than
5000 of them are correct is big (at least 90%, say). In general, a constant number of trials,
followed by a majority vote, boosts the success probability of a protocol from any constant
bigger than 1
2 to any other constant less than 1. These repeated trials increase the amount
of communication by only a constant factor. See the exercises and the separate notes on
Chernoﬀ bounds for further details.

This argument justiﬁes being sloppy about the exact (constant) error of a two-sided
protocol. For upper bounds, we’ll be content to achieve error 49% — it can be reduced to
an arbitrarily small constant with a constant blow-up in communication. For lower bounds,
we’ll be content to rule out protocols with error %1 — the same communication lower
bounds hold, modulo a constant factor, even for protocols with error 49%.

Worst-case communication. When we speak of the communication used by a ran-
domized protocol, we take the worst case over inputs (x, y) and over the coin ﬂips of the
protocol. So if a protocol uses communication at most k, then Alice always sends at most k
bits to Bob.

This deﬁnition seems to go against our guiding rule of being as permissive as possible.
Why not measure only the expected communication used by a protocol, with respect to its
coin ﬂips? This objection is conceptually justiﬁed but technically moot — for protocols that
can err, passing to the technically more convenient worst-case measure can only increase
the communication complexity of a problem by a constant factor.

To see this, consider a protocol R that, for every input (x, y), has two-sided error at
most 1/3 (say) and uses at most k bits of communication on average over its coin ﬂips. This
protocol uses at most 10k bits of communication at least 90% of the time — if it used more
than 10k bits more than 10% of the time, its expected communication cost would be more
than k. Now consider the following protocol R0: simulate R for up to 10k steps; if R fails to
terminate, then abort and output an arbitrary answer. The protocol R0 always sends at
43%).
most 10k bits of communication and has error at most that of R, plus 10% (here,
This error probability of R0 can be reduced back down (to 1
3 , or whatever) through repeated
trials, as before.

≈

In light of these four standing assumptions and rules, we can restate Theorem 1.9 as

follows.

4We mentioned a similar “median of means” idea last lecture (developed further in the homework), when
δ factor in the space usage of our streaming algorithms to a factor oflog 1
δ .

we discussed how to reduce the 1



<!-- pdf-page: 12 -->
2.3 Distributional Complexity

23

Theorem 2.2 Every public-coin randomized one-way protocol for Disjointness that has
two-sided error at most a constant (cid:15)
) communication in the worst
case (over inputs and coin ﬂips).

2 ) uses Ω(min

n, m
}
{

(0, 1

∈

Now that we are clear on the formal statement of our lower bound, how do we prove it?

2.3 Distributional Complexity

Randomized protocols are much more of a pain to reason about than deterministic protocols.
For example, recall our Pigeonhole Principle-based argument last lecture for deterministic
protocols: if Alice holds an n-bit input and always sends at most n
1 bits, then there are
distinct inputs x, x0 such that Alice sends the same message z. (For Disjointness, this
ambiguity left Bob in a lurch.) In a randomized protocol where Alice always sends at most
1)-bit messages for each of her 2n
n
inputs x, and the naive argument breaks down. While Pigeonhole Proof-type arguments can
sometimes be pushed through for randomized protocols, this section introduces a diﬀerent
approach.

1 bits, Alice can use a diﬀerent distribution over (n

−

−

−

Distributional complexity is the main methodology by which one proves lower bounds on
the communication complexity of randomized algorithms. The point is to reduce the goal
to proving lower bounds for deterministic protocols only, with respect to a suitably chosen
input distribution.

Lemma 2.3 (Yao 1983) Let D be a distribution over the space of inputs (x, y) to a
communication problem, and (cid:15)
2 ). Suppose that every deterministic one-way protocol
P with

(0, 1

∈

Pr

(x,y)

∼

D[P wrong on (x, y)]

(cid:15)

≤

has communication cost at least k. Then every (public-coin) randomized one-way protocol R
with (two-sided) error at most (cid:15) on every input has communication cost at least k.

In the hypothesis of Lemma 2.3, all of the randomness is in the input — P is deterministic,
(x, y) is random. In the conclusion, all of the randomness is in the protocol R — the input
is arbitrary but ﬁxed, while the protocol can ﬂip coins. Not only is Lemma 2.3 extremely
useful, but it is easy to prove.

Proof of Lemma 2.3: Let R be a randomized protocol with communication cost less than k.
Recall that such an R can be written as a distribution over deterministic protocols, call them
P1, P2, . . . , Ps. Recalling that the communication cost of a randomized protocol is deﬁned as
the worst-case communication (over both inputs and coin ﬂips), each deterministic protocol
Pi always uses less than k bits of communication. By assumption,

Pr(x,y)

∼

D[Pi wrong on (x, y)] > (cid:15)



<!-- pdf-page: 13 -->
24

Lower Bounds for One-Way Communication

for i = 1, 2, . . . , s. Averaging over the Pi’s, we have

Pr(x,y)

∼

D;R[R wrong on (x, y)] > (cid:15).

Since the maximum of a set of numbers is at least is average, there exists an input (x, y)
such that

PrR[R wrong on (x, y)] > (cid:15),

which completes the proof. (cid:4)

The converse of Lemma 2.3 also holds — whatever the true randomized communication
complexity of a problem, there exists a bad distribution D over inputs that proves it (Yao,
1983). The proof is by strong linear programming duality or, equivalently, von Neumann’s
Minimax Theorem for zero-sum games (see the exercises for details). Thus, the distributional
methodology is “complete” for proving lower bounds — one “only” needs to ﬁnd the right
distribution D over inputs. In general this is a bit of a dark art, though in today’s application
D will just be the uniform distribution.

2.4 The Index Problem

We prove Theorem 2.2 in two steps. The ﬁrst step is to prove a linear lower bound on the
randomized communication complexity of a problem called Index, which is widely useful
for proving one-way communication complexity lower bounds. The second step, which is
easy, reduces Index to Disjointness.

In an instance of Index, Alice gets an n-bit string x
1, 2, . . . , n

n and Bob gets an integer
log2 n bits. The goal is simply to compute xi,

0, 1
}

∈ {

i
the ith bit of Alice’s input.

, encoded in binary using
}

∈ {

≈

Intuitively, since Alice has no idea which of her bits Bob is interested in, she has to send
Bob her entire input. This intuition is easy to make precise for deterministic protocols, by a
Pigeonhole Principle argument. The intuition also holds for randomized protocols, but the
proof takes more work.

Theorem 2.4 (Kremer et al. 1999) The randomized one-way communication complexity
of Index is Ω(n).

With a general communication protocol, where Bob can also send information to Alice,
Index is trivial to solve using only
log2 n bits of information — Bob just sends i to Alice.
Thus Index nicely captures the diﬃculty of designing non-trivial one-way communication
protocols, above and beyond the lower bounds that already apply to general protocols.

≈

Theorem 2.4 easily implies Theorem 2.2.

Proof of Theorem 2.2: We show that Disjointness reduces to Index. Given an input (x, i)
of Index, Alice forms the input x0 = x while Bob forms the input y0 = ei; here ei is the



<!-- pdf-page: 14 -->
2.4 The Index Problem

25

standard basis vector, with a “1” in the ith coordinate and “0”s in all other coordinates.
Then, (x0, y0) is a “yes” instance of Disjointness if and only if xi = 0. Thus, every one-way
protocol for Index induces one for Disjointness, with the same communication cost and
error probability. (cid:4)

We now prove Theorem 2.4. While some computations are required, the proof is

conceptually pretty straightforward.

Proof of Theorem 2.4: We apply the distributional complexity methodology. This requires
positing a distribution D over inputs. Sometimes this takes creativity. Here, the ﬁrst thing
you’d try — the uniform distribution D, where x and i are chosen independently and
uniformly at random — works.

Let c be a suﬃciently small constant (like .1 or less) and assume that n is suﬃciently
large (like 300 or more). We’ll show that every deterministic one-way protocol that uses
at most cn bits of communication has error (w.r.t. D) at least 1
8 . By Lemma 2.3, this
implies that every randomized protocol has error at least 1
8 on some input. Recalling the
discussion about error probabilities in Section 2.2, this implies that for every error (cid:15)0 > 0,
there is a constant c0 > 0 such that every randomized protocol that uses at most c0n bits of
communication has error bigger than (cid:15)0.

Fix a deterministic one-way protocol P that uses at most cn bits of communication.
Since P is deterministic, there are only 2cn distinct messages z that Alice ever sends to
Bob (ranging over the 2n possible inputs x). We need to formalize the intuition that Bob
typically (over x) doesn’t learn very much about x, and hence typically (over i) doesn’t
know what xi is.

Suppose Bob gets a message z from Alice, and his input is i. Since P is deterministic,
Bob has to announce a bit, “0” or “1,” as a function of z and i only. (Recall Figure 2.1).
Holding z ﬁxed and considering Bob’s answers for each of his possible inputs i = 1, 2, . . . , n,
we get an n-bit vector — Bob’s answer vector a(z) when he receives message z from Alice.
Since there are at most 2cn possible messages z, there are at most 2cn possible answer
vectors a(z).

Answer vectors are a convenient way to express the error of the protocol P , with respect
to the randomness in Bob’s input. Fix Alice’s input x, which results in the message z. The
protocol is correct if Bob holds an input i with a(z)i = xi, and incorrect otherwise. Since
Bob’s index i is chosen uniformly at random, and independently of x, we have

Pri[P is incorrect

x, z] =

dH (x, a(z))
n

,

|
where dH (x, a(z)) denotes the Hamming distance between the vectors x and a(z) (i.e.,
the number of coordinates in which they diﬀer). Our goal is to show that, with constant
probability over the choice of x, the expression (2.1) is bounded below by a constant.

Let A =
P . Recall that

{

a(z(x)) : x

2cn. Call Alice’s input x good if there exists an answer vector a

denote the set of all answer vectors used by the protocol
A

0, 1
}

∈ {

}

n

(2.1)

∈

A

| ≤

|



<!-- pdf-page: 15 -->
26

Lower Bounds for One-Way Communication

with dH (x, a) < n
4 , and bad otherwise. Geometrically, you should think of each answer
vector a as the center of a ball of radius n
n equipped
}
with the Hamming metric. See Figure 2.2. The next claim states that, because there aren’t
too many balls (only 2cn for a small constant c) and their radii aren’t too big (only n
4 ), the
union of all of the balls is less than half of the Hamming cube.5

4 in the Hamming cube — the set

0, 1

{

a2#

n/4#

a1#

n/4#

n/4#

a3#

Figure 2.2 Balls of radius n/4 in the Hamming metric, centered at the answer vectors used by the
protocol P .

Claim: Provided c is suﬃciently small and n is suﬃciently large, there are at least 2n
bad inputs x.

1

−

5More generally, the following is good intuition about the Hamming cube for large n: as you blow up a
ball of radius r around a point, the ball includes very few points until r is almost equal to n/2; the ball
includes roughly half the points for r ≈ n/2; and for r even modestly larger than r, the ball contains almost
all of the points.



<!-- pdf-page: 16 -->
2.5 Where We’re Going

27

Before proving the claim, let’s see why it implies the theorem. We can write

Pr(x,y)

∼

D[D wrong on (x, y)] = Pr[x is good]

Pr[D wrong on (x, y)

x is good]

|

·

+ Pr[x is bad]
|

·

Pr[D wrong on (x, y)

0

≥
{z

x is bad] .
}

|

Recalling (2.1) and the deﬁnition of a bad input x, we have

1/2 by Claim

{z

}

≥
|

Pr(x,y)[D wrong on (x, y)

x is bad] = Ex

|

dH (x, a(z(x)))
n

|

(cid:20)

x is bad

(cid:21)

dH (x, a)
n

|

min
a
A
∈

1/4 since x is bad

{z

}

Ex





1
4

.

≥

≥

≥
|

x is bad





We conclude that the protocol P errs on the distribution D with probability at last 1
implies the theorem. We conclude by proving the claim.

8 , which

Proof of Claim: Fix some answer vector a
distance at most n
4 from a is

∈

A. The number of inputs x with Hamming

+

1
a

n
1

(cid:18)

(cid:19)

+

n
2

(cid:18)

(cid:19)

+

· · ·

+

n
n/4

(cid:19)

(cid:18)

.

(2.2)

Recalling the inequality

|{z}

dH (x,a)=1

dH (x,a)=2

dH (x,a)=n/2

| {z }

| {z }

| {z }

(cid:16)
which follows easily from Stirling’s approximation of the factorial function (see the exercises),
we can crudely bound (2.2) above by

(cid:17)

n
k

≤

(cid:18)

(cid:19)

k

,

en
k

n(4e)n/4 = n2log2(4e)

n
4

≤

n2.861n.

The total number of good inputs x — the union of all the balls — is at most
2(.861+c)n, which is at most 2n
least 300, say). (cid:4)

≤
1 for c suﬃciently small (say .1) and n suﬃciently large (at

A

−

|

|

2.861n



<!-- pdf-page: 17 -->
28

Lower Bounds for One-Way Communication

2.5 Where We’re Going

Theorem 2.4 completes our ﬁrst approach to proving lower bounds on the space required
by streaming algorithms to compute certain statistics. To review, we proved from scratch
that Index is hard for one-way communication protocols (Theorem 2.4), reduced Index
to Disjointness to extend the lower bound to the latter problem (Theorem 2.2), and
reduced Disjointness to various streaming computations (last lecture). See also Figure 2.3.
Speciﬁcally, we showed that linear space is necessary to compute the highest frequency in
a data stream (F
), even when randomization and approximation are allowed, and that
linear space is necessary to compute exactly F0 or F2 by a randomized streaming algorithm
with success probability 2/3.

∞

Index
Theorem 2.4

Theorem 2.2
−−−−−−−→

Disjointness

Lecture 1
−−−−−−→

Streaming

Figure 2.3 Review of the proof structure of linear (in min
algorithms. Lower bounds travel from left to right.

| {z }

) space lower bounds for streaming
n, m
}
{

We next focus on the dependence on the approximation parameter (cid:15) required by a
(cid:15))-approximation of a frequency moment. Recall that
streaming algorithm to compute a (1
1.
the streaming algorithms that we’ve seen for F0 and F2 have quadratic dependence on (cid:15)−
Thus an approximation of 1% would require a blowup of 10,000 in the space. Obviously, it
1. We next prove that
would be useful to have algorithms with a smaller dependence on (cid:15)−
1 is necessary, even allowing randomization and even for F0 and F2, to
space quadratic in (cid:15)−
achieve a (1

(cid:15))-approximation.

±

Happily, we’ll prove this via reductions, and won’t need to prove from scratch any new
communication lower bounds. We’ll follow the path in Figure 2.4. First we introduce
a new problem, also very useful for proving lower bounds, called the Gap-Hamming
problem. Second, we give a quite clever reduction from Index to Gap-Hamming. Finally,
it is straightforward to show that one-way protocols for Gap-Hamming with sublinear
communication induce streaming algorithms that can compute a (1
(cid:15))-approximation of
F0 or F2 in o((cid:15)−

2) space.

±

±

Index
Theorem 2.4

Theorem 2.5
−−−−−−−→

Gap-Hamming

Section 2.6.2
−−−−−−−−→

Streaming

Figure 2.4 Proof plan for Ω((cid:15)−2) space lower bounds for (randomized) streaming algorithms that
| {z }
approximate F0 or F2 up to a 1

(cid:15) factor. Lower bounds travel from left to right.

±



<!-- pdf-page: 18 -->
2.6 The Gap-Hamming Problem

29

2.6 The Gap-Hamming Problem

(cid:15))-
Our current goal is to prove that every streaming algorithm that computes a (1
2) space. Note that we’re not going to prove this when
approximation of F0 or F2 needs Ω((cid:15)−
1/√n, since we can always compute a frequency moment exactly in linear or near-linear
(cid:15)
1
space. So the extreme case of what we’re trying to prove is that a (1
√n )-approximation
requires Ω(n) space. This special case already requires all of the ideas needed to prove a
lower bound of Ω((cid:15)−

2) for all larger (cid:15) as well.

(cid:28)

±

±

2.6.1 Why Disjointness Doesn’t Work

Our goal is also to prove this lower bound through reductions, rather than from scratch.
We don’t know too many hard problems yet, and we’ll need a new one. To motivate it, let’s
see why Disjointness is not good enough for our purposes.
Suppose we have a streaming algorithm S that gives a (1

1
√n )-approximation to F0 —
how could we use it to solve Disjointness? The obvious idea is to follow the reduction
. Alice converts her input x of Disjointness and converts it to
used last lecture for F
a stream, feeds this stream into S, sends the ﬁnal memory state of S to Bob, and Bob
converts his input y of Disjointness into a stream and resumes S’s computation on it.
1
With healthy probability, S returns a (1
√n )-approximation of F0 of the stream induced
by (x, y). But is this good for anything?

±

±

∞

|

|

|

|

y

+

| · |

, where

Suppose (x, y) is a “yes” instance to Disjointness. Then, F0 of the corresponding stream
denotes the number of 1’s in a bit vector. If (x, y) is a “no” instance of
x
is
y
Disjointness, then F0 is somewhere between max
1. A particularly
and
= n/2 and x, y are either disjoint or overlap in exactly one
hard case is when
=
|
1
element — F0 is then either n or n
√n )-approximation of F0
translates to additive error √n, which is nowhere near enough resolution to distinguish
between “yes” and “no” instances of Disjointness.

1. In this case, a (1

| −

|}

−

±

{|

+

x

x

x

y

y

|

|

|

|

,

|

|

|

|

2.6.2 Reducing Gap-Hamming to F0 Estimation

±

1
A (1
√n )-approximation of F0 is insuﬃcient to solve Disjointness— but perhaps there
is some other hard problem that it does solve? The answer is yes, and the problem is
estimating the Hamming distance between two vectors x, y — the number of coordinates in
which x, y diﬀer.

To see the connection between F0 and Hamming distance, consider x, y

n and the
) induced by them. As usual, we can
usual data stream (with elements in U =
}
interpret x, y as characteristic vectors of subsets A, B of U (Figure 2.5). Observe that the
Hamming distance dH (x, y) is the just the size of the symmetric diﬀerence,
B
.
A
B
|
|
, and hence
A
Observe also that F0 =

1, 2, . . . , n
{

0, 1
}

and

, so

∈ {

+

B

B

B

B

A

A

\

|

= F0 − |

|

|

|

\

|

A
|
= F0 − |

\
A
|

|

∪

|

|

\



<!-- pdf-page: 19 -->
30

Lower Bounds for One-Way Communication

dH (x, y) = 2F0 − |
log2 n bits.

x

y

|

| − |

. Finally, Bob knows

, and Alice can send

y

|

|

to Bob using

x

|

|

x"

y"

indices'with'xi'='1'

Figure 2.5 The Hamming distance between two bit vectors equals the size of the symmetric
diﬀerence of the corresponding subsets of 1-coordinates.

The point is that a one-way protocol that computes F0 with communication c yields a
one-way protocol that computes dH (x, y) with communication c + log2 n. More generally, a
2√n
(1
additive error, with log2 n extra communication.

1
√n )-approximation of F0 yields a protocol that estimates dH (x, y) up to 2F0/√n

≤

±

This reduction from Hamming distance estimation to F0 estimation is only useful to us
if the former problem has large communication complexity. It’s technically convenient to
convert Hamming distance estimation into a decision problem. We do this using a “promise
problem” — intuitively, a problem where we only care about a protocol’s correctness when
the input satisﬁes some conditions (a “promise”). Formally, for a parameter t, we say that a
protocol correctly solves Gap-Hamming(t) if it outputs “1” whenever dH (x, y) < t
c√n
and outputs “0” whenever dH (x, y) > t + c√n, where c is a suﬃciently small constant.
Note that the protocol can output whatever it wants, without penalty, on inputs for which
dH (x, y) = t

c√n.

−

Our reduction above shows that, for every t, Gap-Hamming(t) reduces to the (1

c
√n )-
approximation of F0. Does it matter how we pick t? Remember we still need to prove
that the Gap-Hamming(t) problem does not admit low-communication one-way protocols.
If we pick t = 0, then the problem becomes a special case of the Equality problem
(where f (x, y) = 1 if and only x = y). We’ll see next lecture that the one-way randomized
communication complexity of Equality is shockingly low — only O(1) for public-coin
protocols. Picking t = n has the same issue. Picking t = n
2 seems more promising. For
example, it’s easy to certify a “no” instance of Equality— just exhibit an index where x
and y diﬀer. How would you succinctly certify that dH (x, y) is either at least n
2 + √n or at

±

±



<!-- pdf-page: 20 -->
2.7

Lower Bound for Gap-Hamming

31

most n
n chosen uniformly
√n? For more intuition, think about two vectors x, y
2 −
at random. The expected Hamming distance between them is n
2 , with a standard deviation
√n. Thus deciding an instance of Gap-Hamming( n
of
2 ) has the ﬂavor of learning an
unpredictable fact about two random strings, and it seems diﬃcult to do this without
learning detailed information about the particular strings at hand.

0, 1
}

∈ {

≈

2.7 ]

Lower Bound on the One-Way Communication Complexity of Gap-Hamming

This section dispenses with the hand-waving and formally proves that every protocol that
2 and c suﬃciently small — requires linear communication.

solves Gap-Hamming— with t = n

Theorem 2.5 (Jayram et al. 2008; Woodruﬀ 2004, 2007) The randomized one-way
communication complexity of Gap-Hamming is Ω(n).

Proof: The proof is a randomized reduction from Index, and is more clever than the other
reductions that we’ve seen so far. Consider an input to Index, where Alice holds an n-bit
string x and Bob holds an index i
. We assume, without loss of generality,
}
that n is odd and suﬃciently large.

1, 2, . . . , n

∈ {

Alice and Bob generate, without any communication, an input (x0, y0) to Gap-Hamming.
They do this one bit at a time, using the publicly available randomness. To generate the
ﬁrst bit of the Gap-Hamming input, Alice and Bob interpret the ﬁrst n public coins as a
random string r. Bob forms the bit b = ri, the ith bit of the random string. Intuitively, Bob
says “I’m going to pretend that r is actually Alice’s input, and report the corresponding
answer ri.” Meanwhile, Alice checks whether dH (x, r) < n
2 . (Since n is odd,
one of these holds.) In the former case, Alice forms the bit a = 1 to indicate that r is a
decent proxy for her input x. Otherwise, she forms the bit a = 0 to indicate that 1
r
would have been a better approximation of reality (i.e., of x).

2 or dH (x, r) > n

−

−

The key and clever point of the proof is that a and b are correlated — positively if xi = 1
and negatively if xi = 0, where x and i are the given input to Index. To see this, condition
1 bits of r other than i. There are two cases. In the ﬁrst case, x and r agree
on the n
on strictly less than or strictly greater than (n
1)/2 of the bits so-far. In this case, a is
already determined (to 0 or 1, respectively). Thus, in this case, Pr[a = b] = Pr[a = ri] = 1
2 ,
using that ri is independent of all the other bits. In the second case, amongst the n
1
bits of r other than ri, exactly half of them agree with x. In this case, a = 1 if and only
if xi = ri. Hence, if xi = 1, then a and b always agree (if ri = 1 then a = b = 1, if ri = 0
then a = b = 0). If xi = 0, then a and b always disagree (if ri = 1, then a = 0 and b = 1, if
ri = 0, then a = 1 and b = 0).

−

−

The probability of the second case is the probability of getting (n

1)/2 “heads” out
. Applying Stirling’s approximation of the factorial

−

of n

−

1 coin ﬂips, which is

n

1
−
1)/2

−

(n

(cid:0)

(cid:1)



<!-- pdf-page: 21 -->
32

Lower Bounds for One-Way Communication

function shows that this probability is bigger than you might have expected, namely
for a constant c0 (see Exercises for details). We therefore have

≈

c0
√n

·

Pr[a = b] = Pr[Case 1]

1

c0
√n
−
{z
}
c0
1
2 −
√n
2 + c0
1

√n

=

|

(

=

|
1
2
{z

|
if xi = 1
if xi = 0.

Pr[a = b

Case 1]

+ Pr[Case 2]

Pr[a = b

Case 2]

c0
√n
{z

}

|

·

|
1 or 0

}

|

{z

}

This is pretty amazing when you think about it — Alice and Bob have no knowledge of
each other’s inputs and yet, with shared randomness but no explicit communication, can
generate bits correlated with xi!6

The randomized reduction from Index to Gap-Hamming now proceeds as one would
expect. Alice and Bob repeat the bit-generating experiment above m independent times to
generate m-bit inputs x0 and y0 of Gap-Hamming. Here m = qn for a suﬃciently large
constant q. The expected Hamming distance between x0 and y0 is at most m
c0√m (if
xi = 1) or at least m
2 + c0√m (if xi = 0). A routine application of the Chernoﬀ bound
(see Exercises) implies that, for a suﬃciently small constant c and large constant q, with
probability at least 8
2 + c√m
2 −
(if xi = 0). When this event holds, Alice and Bob can correctly compute the answer to the
original input (x, i) to Index by simply invoking any protocol P for Gap-Hamming on the
input (x0, y0). The communication cost is that of P on inputs of length m = Θ(n). The
error is at most the combined error of the randomized reduction and of the protocol P —
whenever the reduction and P both proceed as intended, the correct answer to the Index
input (x, i) is computed.

c√m (if xi = 1) and dH (x0, y0) > m

9 (say), dH (x0, y0) < m

2 −

Summarizing, our randomized reduction implies that, if there is a (public-coin) random-
3 and sublinear communication,
9 . Since we’ve ruled out the latter,

ized protocol for Gap-Hamming with (two-sided) error 1
then there is a randomized protocol for Index with error 4
the former does not exist. (cid:4)

Combining Theorem 2.5 with our reduction from Gap-Hamming to estimating F

we’ve proved the following.

,

∞

Theorem 2.6 There is a constant c > 0 such that the following statement holds: There is
no sublinear-space randomized streaming algorithm that, for every data stream, computes F0
to within a 1

c
√n factor with probability at least 2/3.

±

A variation on the same reduction proves the same lower bound for approximating F2;

see the Exercises.

6This would clearly not be possible with a private-coin protocol. But we’ll see later than the (additive)
diﬀerence between the private-coin and public-coin communication complexity of a problem is O(log n), so a
linear communication lower bound for one type automatically carries over to the other type.



<!-- pdf-page: 22 -->
2.7

Lower Bound for Gap-Hamming

33

1

≥

≥

±

2), when (cid:15)

Our original goal was to prove that the (1

√n . Theorem 2.6 proves this in the special case where (cid:15) = Θ( 1

(cid:15))-approximate computation of F0 requires
space Ω((cid:15)−
√n ).
This can be extended to larger (cid:15) by a simple “padding” trick. Fix your favorite values of n
1
√n and modify the proof of Theorem 2.6 as follows. Reduce from Gap-Hamming
and (cid:15)
2). Given an input (x, y) of Gap-Hamming, form (x0, y0) by
on inputs of length m = Θ((cid:15)−
m zeroes to x and y. A streaming algorithm with space s that estimates F0
appending n
on the induced data stream up to a (1
(cid:15)) factor induces a randomized protocol that solves
this special case of Gap-Hamming with communication s. Theorem 2.5 implies that every
2), so this lower bound
randomized protocol for the latter problem uses communication Ω((cid:15)−
carries over to the space used by the streaming algorithm.

±

−



<!-- pdf-page: 23 -->
Lecture 3

Lower Bounds for Compressive Sensing

3.1 An Appetizer: Randomized Communication Complexity of Equality

We begin with an appetizer before starting the lecture proper — an example that demon-
strates that randomized one-way communication protocols can sometimes exhibit surprising
power.

It won’t surprise you that the Equality function — with f (x, y) = 1 if and only if
x = y — is a central problem in communication complexity. It’s easy to prove, by the
Pigeonhole Principle, that its deterministic one-way communication complexity is n, where n
is the length of the inputs x and y.1 What about its randomized communication complexity?
Recall from last lecture that by default, our randomized protocols can use public coins2 and
can have two-sided error (cid:15), where (cid:15) is any constant less than 1
2 .

Theorem 3.1 (Yao 1979) The (public-coin) randomized one-way communication com-
plexity of Equality is O(1).

Thus, the randomized communication complexity of a problem can be radically smaller
than its deterministic communication complexity. A similar statement follows from our
upper and lower bound results for estimating the frequency moments F0 and F2 using
small-space streaming algorithms, but Theorem 3.1 illustrates this point in a starker and
clearer way.

Theorem 3.1 provides a cautionary tale: sometimes we expect a problem to be hard
for a class of protocols and are proved wrong by a clever protocol; other times, clever
protocols don’t provide non-trivial solutions to a problem but still make proving strong
lower bounds technically diﬃcult. Theorem 3.1 also suggests that, if we want to prove strong
communication lower bounds for randomized protocols via a reduction, there might not be
too many natural problems out there to reduce from.3

1We’ll see later that this lower bound applies to general deterministic protocols, not just to one-way

protocols.

2Recall the public-coin model: when Alice and Bob show up there is already an inﬁnite stream of random
bits written on a blackboard, which both of them can see. Using shared randomness does not count toward
the communication cost of the protocol.

3Recall our discussion about Gap-Hamming last lecture: for the problem to be hard, it is important to
2 . With t too close to 0 or n, the problem is a special case of Equality and is

choose the midpoint t to be n
therefore easy for randomized protocols.

34



<!-- pdf-page: 24 -->
3.1 Randomized Communication Complexity of the Equality Function

Proof of Theorem 3.1: The protocol is as follows.

1. Alice and Bob interpret the ﬁrst 2n public coins as random strings r1, r2 ∈ {

0, 1

This requires no communication.

35

n.
}

2. Alice sends the two random inner products
This requires two bits of communication.

x, r1i

h

mod 2 and

x, r2i

h

mod 2 to Bob.

3. Bob reports “1” if and only if his random inner products match those of Alice:
mod 2 for i = 1, 2. Note that Bob has all of the information needed

=

x, rii
y, rii
h
to perform this computation.

h

h

and

y, rii

We claim that the error of this protocol is at most 25% on every input. The protocol’s
error is one-sided: when x = y the protocol always accepts, so there are no false negatives.
= y. We use the Principle of Deferred Decisions to argue that, for each
Suppose that x
i = 1, 2, the inner products
are diﬀerent (mod 2) with probability exactly
= yi and condition on all of the bits of a random
50%. To see this, pick an index i where xi 6
string except for the ith one. Let a and b denote the values of the inner products-so-far of x
and y (modulo 2) with the random string. If the ith random bit is a 0, then the ﬁnal inner
products are also a and b. If the ith random bit is a 1, then one inner product stays the
same while the other ﬂips its value (since exactly one of xi, yi is a 1). Thus, whether a = b
or a
= b, exactly one of the two random bit values (50% probability) results in the ﬁnal two
inner products having diﬀerent values (modulo 2). The probability that two unequal strings
have equal inner products (modulo 2) in two independent experiments is 25%. (cid:4)

x, rii

h

The proof of Theorem 3.1 gives a 2-bit protocol with (1-sided) error 25%. As usual,
executing many parallel copies of the protocol reduces the error to an arbitrarily small
constant, with a constant blow-up in the communication complexity.

The protocol used to prove Theorem 3.1 makes crucial use of public coins. We’ll see later
that the private-coin one-way randomized communication complexity is Θ(log n), which is
worse than public-coin protocols but still radically better than deterministic protocols. More
generally, next lecture we’ll prove Newman’s theorem, which states that the private-coin
randomized communication complexity of a problem is at most O(log n) more than its
public-coin randomized communication complexity.

The protocol in the proof of Theorem 3.1 eﬀectively gives each of the two strings x, y
a 2-bit “sketch” or “ﬁngerprint” such that the property of distinctness is approximately
preserved. Clearly, this is the same basic idea as hashing. This is a useful idea in both
theory and practice, and we’ll use it again shortly.

Remark 3.2 The computational model studied in communication complexity is potentially
very powerful — for example, Alice and Bob have unlimited computational power — and
the primary point of the model is to prove lower bounds. Thus, whenever you see an upper
bound result in communication complexity, like Theorem 3.1, it’s worth asking what the

6
6

