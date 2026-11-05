<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: 26d95080dbde050d736933aacc8a97ed1f204cbb37b868dfa35d5d8b7125d0ae -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
Chapter 7

Randomized Computation

“We do not assume anything about the distribution of the instances of the problem
to be solved. Instead we incorporate randomization into the algorithm itself... It may
seem at ﬁrst surprising that employing randomization leads to eﬃcient algorithm.
This claim is substantiated by two examples. The ﬁrst has to do with ﬁnding the
nearest pair in a set of n points in Rk. The second example is an extremely eﬃcient
algorithm for determining whether a number is prime.”
Michael Rabin, 1976

Thus far our standard model of computation has been the deterministic Turing Machine. But
everybody who is even a little familiar with computation knows that that real-life computers need
not be deterministic since they have built-in ”random number generators.” In fact these generators
are very useful for computer simulation of ”random” processes such as nuclear ﬁssion or molecular
motion in gases or the stock market. This chapter formally studies probablistic computation, and
complexity classes associated with it.

We should mention right away that it is an open question whether or not the universe has any
randomness in it (though quantum mechanics seems to guarantee that it does). Indeed, the output
of current ”random number generators” is not guaranteed to be truly random, and we will revisit
this limitation in Section 7.4.3. For now, assume that true random number generators exist. Then
arguably, a realistic model for a real-life computer is a Turing machine with a random number
generator, which we call a Probabilistic Turing Machine (PTM). It is natural to wonder whether
diﬃcult problems like 3SAT are eﬃciently solvable using a PTM.

We will formally deﬁne the class BPP of languages decidable by polynomial-time PTMs and
discuss its relation to previously studied classes such as P/poly and PH. One consequence is that
if PH does not collapse, then 3SAT does not have eﬃcient probabilistic algorithms.

We also show that probabilistic algorithms can be very practical by presenting ways to greatly
reduce their error to absolutely minuscule quantities. Thus the class BPP (and its sister classes
RP, coRP and ZPP) introduced in this chapter are arguably as important as P in capturing
eﬃcient computation. We will also introduce some related notions such as probabilistic logspace
algorithms and probabilistic reductions.

DRAFT

Web draft 2007-01-08 21:59
p7.1 (115)
Complexity Theory: A Modern Approach. © 2006 Sanjeev Arora and Boaz Barak. References and attributions are
still incomplete.

<!-- pdf-page: 2 -->
p7.2 (116)

7.1. PROBABILISTIC TURING MACHINES

Though at ﬁrst randomization seems merely a tool to allow simulations of randomized physical
processes, the surprising fact is that in the past three decades randomization has led to more eﬃcient
—and often simpler—algorithms for problems in a host of other ﬁelds—such as combinatorial
optimization, algebraic computation, machine learning, and network routing.

In complexity theory too, the role of randomness extends far beyond a study of randomized
algorithms and classes such as BPP. Entire areas such as cryptography and interactive and prob-
abilistically checkable proofs rely on randomness in an essential way, sometimes to prove results
whose statement did not call for randomness at all. The groundwork for studying those areas will
be laid in this chapter.

In a later chapter, we will learn something intriguing: to some extent, the power of randomness
may be a mirage. If a certain plausible complexity-theoretic conjecture is true (see Chapters 16
and 17), then every probabilistic algorithm can be simulated by a deterministic algorithm (one that
does not use any randomness whatsoever) with only polynomial overhead.

Throughout this chapter and the rest of the book, we will use some notions from elementary

probability on ﬁnite sample spaces; see Appendix A for a quick review.

7.1 Probabilistic Turing machines

We now deﬁne probabilistic Turing machines (PTMs). Syntactically, a PTM is no diﬀerent from a
nondeterministic TM: it is a TM with two transition functions δ0, δ1. The diﬀerence lies in how we
interpret the graph of all possible computations: instead of asking whether there exists a sequence
of choices that makes the TM accept, we ask how large is the fraction of choices for which this
happens. More precisely, if M is a PTM, then we envision that in every step in the computation,
M chooses randomly which one of its transition functions to apply (with probability half applying
δ0 and with probability half applying δ1). We say that M decides a language if it outputs the right
answer with probability at least 2/3.

Notice, the ability to pick (with equal probability) one of δ0, δ1 to apply at each step is equivalent
to the machine having a ”fair coin”, which, each time it is tossed, comes up ”Heads” or ”Tails”
with equal probability regardless of the past history of Heads/Tails. As mentioned, whether or not
such a coin exists is a deep philosophical (or scientiﬁc) question.

Definition 7.1 (The classes BPTIME and BPP)
For T : N → N and L ⊆ {0, 1}∗, we say that a PTM M decides L in time T (n), if
for every x ∈ {0, 1}∗, M halts in T (|x|) steps regardless of its random choices, and
Pr[M (x) = L(x)] ≥ 2/3, where we denote L(x) = 1 if x ∈ L and L(x) = 0 if x 6∈ L.
We let BPTIME(T (n)) denote the class of languages decided by PTMs in O(T (n))
time and let BPP = ∪cBPTIME(nc).

Remark 7.2
We will see in Section 7.4 that this deﬁnition is quite robust. For instance, the ”coin” need not
be fair. The constant 2/3 is arbitrary in the sense that it can be replaced with any other constant

Web draft 2007-01-08 21:59

DRAFT

<!-- pdf-page: 3 -->
7.2. SOME EXAMPLES OF PTMS

p7.3 (117)

greater than half without changing the classes BPTIME(T (n)) and BPP. Instead of requiring
the machine to always halt in polynomial time, we could allow it to halt in expected polynomial
time.

Remark 7.3
While Deﬁnition 7.1 allows the PTM M , given input x, to output a value diﬀerent from L(x)
with positive probability, this probability is only over the random choices that M makes in the
computation. In particular for every input x, M (x) will output the right value L(x) with probability
at least 2/3. Thus BPP, like P, is still a class capturing worst-case computation.

Since a deterministic TM is a special case of a PTM (where both transition functions are equal),
the class BPP clearly contains P. As alluded above, under plausible complexity assumptions it
holds that BPP = P. Nonetheless, as far as we know it may even be that BPP = EXP. (Note
that BPP ⊆ EXP, since given a polynomial-time PTM M and input x ∈ {0, 1}n in time 2poly(n)
it is possible to enumerate all possible random choices and compute precisely the probability that
M (x) = 1.)

An alternative deﬁnition. As we did with NP, we can deﬁne BPP using deterministic TMs
where the ”probabilistic choices” to apply at each step can be provided to the TM as an additional
input:

Definition 7.4 (BPP, alternative definition)
BPP contains a language L if there exists a polynomial-time TM M and a polynomial p : N → N
such that for every x ∈ {0, 1}∗, Prr∈R{0,1}p(|x|)[M (x, r) = L(x)] ≥ 2/3.

7.2 Some examples of PTMs

The following examples demonstrate how randomness can be a useful tool in computation. We will
see many more examples in the rest of this book.

7.2.1 Probabilistic Primality Testing

In primality testing we are given an integer N and wish to determine whether or not it is prime.
Generations of mathematicians have learnt about prime numbers and —before the advent of
computers— needed to do primality testing to test various conjectures1.
Ideally, we want eﬃ-
cient algorithms, which run in time polynomial in the size of N ’s representation, in other words,
poly(log n). We knew of no such eﬃcient algorithms2 until the 1970s, when an eﬀﬁcient proba-
bilistic algorithm was discovered. This was one of the ﬁrst to demonstrate the power of proba-
bilistic algorithms. In a recent breakthrough, Agrawal, Kayal and Saxena [?] gave a deterministic
polynomial-time algorithm for primality testing.

1Though a very fast human computer himself, Gauss used the help of a human supercomputer –an autistic person

who excelled at fast calculations—to do primality testing.

2In fact, in his letter to von Neumann quoted in Chapter 2, G¨odel explicitly mentioned this problem as an example

for an interesting problem in NP but not known to be eﬃciently solvable.

DRAFT

Web draft 2007-01-08 21:59

<!-- pdf-page: 4 -->
p7.4 (118)

7.2. SOME EXAMPLES OF PTMS

Formally, primality testing consists of checking membership in the language PRIMES = { xNy : N is a prime number}.

Notice, the corresponding search problem of ﬁnding the factorization of a given composite number
N seems very diﬀerent and much more diﬃcult. It is the famous FACTORING problem, whose
conjectured hardness underlies many current cryptosystems. Chapter 20 describes Shor’s algorithm
to factors integers in polynomial time in the model of quantum computers.

We sketch an algorithm showing that PRIMES is in BPP (and in fact in coRP). For every

number N , and A ∈ [N − 1], deﬁne

QRN (A) =

+1


0




−1

gcd(A, N ) 6= 1

A is a quadratic residue modulo N
That is, A = B2

(mod N ) for some B with gcd(B, N ) = 1

otherwise

We use the following facts that can be proven using elementary number theory:

• For every odd prime N and A ∈ [N − 1], QRN (A) = A(N −1)/2 (mod N ).
• For every odd N, A deﬁne the Jacobi symbol ( N

A ) as Qk

the (not necessarily distinct) prime factors of N (i.e., N = Qk
is computable in time O(log A · log N ).

i=1 QRPi(A) where P1, . . . , Pk are all
i=1 Pi). Then, the Jacobi symbol

• For every odd composite N , (cid:12)
[N − 1] : gcd(N, A) = 1}(cid:12)
(cid:12)

(cid:12){A ∈ [N − 1] : gcd(N, A) = 1 and ( N

A ) = A(N −1)/2}(cid:12)

(cid:12) ≤ 1
2

(cid:12)
(cid:12){A ∈

Together these facts imply a simple algorithm for testing primality of N (which we can assume
without loss of generality is odd): choose a random 1 ≤ A < N , if gcd(N, A) > 1 or ( N
A ) 6= A(N −1)/2
(mod N ) then output “composite”, otherwise output “prime”. This algorithm will always output
“prime” is N is prime, but if N is composite will output “composite” with probability at least 1/2.
(Of course this probability can be ampliﬁed by repeating the test a constant number of times.)

7.2.2 Polynomial identity testing

So far we described probabilistic algorithms solving problems that have known deterministic poly-
nomial time algorithms. We now describe a problem for which no such deterministic algorithm is
known:

We are given a polynomial with integer coeﬃcients in an implicit form, and we want to decide
whether this polynomial is in fact identically zero. We will assume we get the polynomial in the
form of an arithmetic circuit. This is analogous to the notion of a Boolean circuit, but instead of the
operators ∧, ∨ and ¬, we have the operators +, − and ×. Formally, an n-variable arithmetic circuit
is a directed acyclic graph with the sources labeled by a variable name from the set x1, . . . , xn,
and each non-source node has in-degree two and is labeled by an operator from the set {+, −, ×}.
There is a single sink in the graph which we call the output node. The arithmetic circuit deﬁnes
a polynomial from Zn to Z by placing the inputs on the sources and computing the value of
each node using the appropriate operator. We deﬁne ZEROP to be the set of arithmetic circuits
that compute the identically zero polynomial. Determining membership in ZEROP is also called

Web draft 2007-01-08 21:59

DRAFT

<!-- pdf-page: 5 -->
7.2. SOME EXAMPLES OF PTMS

p7.5 (119)

polynomial identity testing, since we can reduce the problem of deciding whether two circuits C, C0
compute the same polynomial to ZEROP by constructing the circuit D such that D(x1, . . . , xn) =
C(x1, . . . , xn) − C0(x1, . . . , xn).

Since expanding all the terms of a given arithmetic circuit can result in a polynomial with
exponentially many monomials, it seems hard to decide membership in ZEROP. Surprisingly, there
is in fact a simple and eﬃcient probabilistic algorithm for testing membership in ZEROP. At the
heart of this algorithm is the following fact, typically known as the Schwartz-Zippel Lemma, whose
proof appears in Appendix A (see Lemma A.25):

Lemma 7.5
Let p(x1, x2, . . . , xm) be a polynomial of total degree at most d and S is any ﬁnite set of integers.
When a1, a2, . . . , am are randomly chosen with replacement from S, then

Pr[p(a1, a2, . . . , am) 6= 0] ≥ 1 −

d
|S|

.

Now it is not hard to see that given a size m circuit C on n variables, it deﬁnes a polynomial of
degree at most 2m. This suggests the following simple probabilistic algorithm: choose n numbers
x1, . . . , xn from 1 to 10·2m (this requires O(n·m) random bits), evaluate the circuit C on x1, . . . , xn
to obtain an output y and then accept if y = 0, and reject otherwise. Clearly if C ∈ ZEROP then
we always accept. By the lemma, if C 6∈ ZEROP then we will reject with probability at least 9/10.
However, there is a problem with this algorithm. Since the degree of the polynomial represented
by the circuit can be as high as 2m, the output y and other intermediate values arising in the
computation may be as large as (10 · 2m)2m — this is a value that requires exponentially many bits
just to describe!

We solve this problem using the technique of ﬁngerprinting. The idea is to perform the evalu-
ation of C on x1, . . . , xn modulo a number k that is chosen at random in [22m]. Thus, instead of
computing y = C(x1, . . . , xn), we compute the value y (mod k). Clearly, if y = 0 then y (mod k) is
also equal to 0. On the other hand, we claim that if y 6= 0, then with probability at least δ = 1
10m ,
k does not divide y. (This will suﬃce because we can repeat this procedure O(1/δ) times to ensure
that if y 6= 0 then we ﬁnd this out with probability at lest 9/10.) Indeed, assume that y 6= 0 and
let S = {p1, . . . , p‘} denote set of the distinct prime factors of y. It is suﬃcient to show that with
probability at δ, the number k will be a prime number not in S. Yet, by the prime number theorem,
1
5m = 2δ. Also, since y can have at most log y ≤ 5m2m
the probability that k is prime is at least
distinct factors, the probability that k is in S is less than 5m2m
10m = δ. Hence by the union
bound, with probability at least δ, k will not divide y.

22m (cid:28) 1

7.2.3 Testing for perfect matching in a bipartite graph.

If G = (V1, V2, E) is the bipartite graph where |V1| = |V2| and E ⊆ V1 × V2 then a perfect matching
is some E0 ⊆ E such that every node appears exactly once among the edges of E0. Alternatively,
we may think of it as a permutation σ on the set {1, 2, . . . , n} (where n = |V1|) such that for
each i ∈ {1, 2, . . . , n}, the pair (i, σ(i)) is an edge. Several deterministic algorithms are known for
detecting if a perfect matching exists. Here we describe a very simple randomized algorithm (due
to Lov´asz) using the Schwartz-Zippel lemma.

DRAFT

Web draft 2007-01-08 21:59

<!-- pdf-page: 6 -->
p7.6 (120)

7.3. ONE-SIDED AND ZERO-SIDED ERROR: RP, CORP, ZPP

Consider the n × n matrix X (where n = |V1| = |V2|) whose (i, j) entry Xij is the variable xij

if (i, j) ∈ E and 0 otherwise. Recall that the determinant of matrix det(X) is

det(X) =

(−1)sign(σ)

X

σ∈Sn

n
Y

i=1

Xi,σ(i),

(1)

where Sn is the set of all permutations of {1, 2, . . . , n}. Note that every permutation is a potential
perfect matching, and the corresponding monomial in det(X) is nonzero iﬀ this perfect matching
exists in G. Thus the graph has a perfect matching iﬀ det(X) 6= 0.

Now observe two things. First, the polynomial in (1) has |E| variables and total degree at most
n. Second, even though this polynomial may be of exponential size, for every setting of values to
the Xij variables it can be eﬃciently evaluated, since computing the determinant of a matrix with
integer entries is a simple polynomial-time computation (actually, even in NC2).

This leads us to Lov´asz’s randomized algorithm: pick random values for Xij’s from [1, . . . , 2n],
substitute them in X and compute the determinant. If the determinant is nonzero, output “accept”
else output “reject.” The advantage of the above algorithm over classical algorithms is that it can
be implemented by a randomized NC circuit, which means (by the ideas of Section 6.5.1) that it
has a fast implementation on parallel computers.

7.3 One-sided and zero-sided error: RP, coRP, ZPP

The class BPP captured what we call probabilistic algorithms with two sided error. That is, it
allows the machine M to output (with some small probability) both 0 when x ∈ L and 1 when
x 6∈ L. However, many probabilistic algorithms have the property of one sided error. For example
if x 6∈ L they will never output 1, although they may output 0 when x ∈ L. This is captured by
the deﬁnition of RP.
Definition 7.6
RTIME(t(n)) contains every language L for which there is a is a probabilistic TM M running in
t(n) time such that

x ∈ L ⇒ Pr[M accepts x] ≥

2
3
x 6∈ L ⇒ Pr[M accepts x] = 0

We deﬁne RP = ∪c>0RTIME(nc).

Note that RP ⊆ NP, since every accepting branch is a “certiﬁcate” that the input is in the
language. In contrast, we do not know if BPP ⊆ NP. The class coRP = {L | L ∈ RP} captures
one-sided error algorithms with the error in the “other direction” (i.e., may output 1 when x 6∈ L
but will never output 0 if x ∈ L).

For a PTM M , and input x, we deﬁne the random variable TM,x to be the running time of M
on input x. That is, Pr[TM,x = T ] = p if with probability p over the random choices of M on input
x, it will halt within T steps. We say that M has expected running time T (n) if the expectation
E[TM,x] is at most T (|x|) for every x ∈ {0, 1}∗. We now deﬁne PTMs that never err (also called
“zero error” machines):

Web draft 2007-01-08 21:59

DRAFT

<!-- pdf-page: 7 -->
7.4. THE ROBUSTNESS OF OUR DEFINITIONS
Definition 7.7
The class ZTIME(T (n)) contains all the languages L for which there is an expected-time O(T (n))
machine that never errs. That is,

p7.7 (121)

x ∈ L ⇒ Pr[M accepts x] = 1

x 6∈ L ⇒ Pr[M halts without accepting on x] = 1

We deﬁne ZPP = ∪c>0ZTIME(nc).

The next theorem ought to be slightly surprising, since the corresponding statement for nonde-

terminism is open; i.e., whether or not P = NP ∩ coNP.

Theorem 7.8
ZPP = RP ∩ coRP.

We leave the proof of this theorem to the reader (see Exercise 4). To summarize, we have the

following relations between the probabilistic complexity classes:

ZPP =RP ∩ coRP

RP ⊆BPP

coRP ⊆BPP

7.4 The robustness of our deﬁnitions

When we deﬁned P and NP, we argued that our deﬁnitions are robust and were likely to be the
same for an alien studying the same concepts in a faraway galaxy. Now we address similar issues
for probabilistic computation.

7.4.1 Role of precise constants, error reduction.

The choice of the constant 2/3 seemed pretty arbitrary. We now show that we can replace 2/3 with
any constant larger than 1/2 and in fact even with 1/2 + n−c for a constant c > 0.

Lemma 7.9
For c > 0, let BPPn−c denote the class of languages L for which there is a polynomial-time PTM
M satisfying Pr[M (x) = L(x)] ≥ 1/2 + |x|−c for every x ∈ {0, 1}∗. Then BPPn−c = BPP.

Since clearly BPP ⊆ BPPn−c, to prove this lemma we need to show that we can transform a
machine with success probability 1/2 + n−c into a machine with success probability 2/3. We do this
by proving a much stronger result: we can transform such a machine into a machine with success
probability exponentially close to one!

DRAFT

Web draft 2007-01-08 21:59

<!-- pdf-page: 8 -->
p7.8 (122)

7.4. THE ROBUSTNESS OF OUR DEFINITIONS

Theorem 7.10 (Error reduction)
Let L ⊆ {0, 1}∗ be a language and suppose that there exists a polynomial-time PTM
M such that for every x ∈ {0, 1}∗, Pr[M (x) = L(x) ≥ 1
Then for every constant d > 0 there exists a polynomial-time PTM M 0 such that
for every x ∈ {0, 1}∗, Pr[M 0(x) = L(x)] ≥ 1 − 2−|x|d.

2 + |x|−c.

for every input x ∈ {0, 1}∗, run M (x) for k times
Proof: The machine M 0 is quite simple:
obtaining k outputs y1, . . . , yk ∈ {0, 1}, where k = 8|x|2d+c. If the majority of these values are 1
then accept, otherwise reject.

To analyze this machine, deﬁne for every i ∈ [k] the random variable Xi to equal 1 if yi = L(x)
and to equal 0 otherwise. Note that X1, . . . , Xk are independent Boolean random variables with
E[Xi] = Pr[Xi = 1] ≥ 1/2 + n−c (where n = |x|). The Chernoﬀ bound (see Theorem A.18 in
Appendix A) implies the following corollary:
Corollary 7.11
Let X1, . . . , Xk be independent identically distributed Boolean random variables, with Pr[Xi =
1] = p for every 1 ≤ i ≤ k. Let δ ∈ (0, 1). Then,

(cid:12)
(cid:12)
Pr(cid:2)
(cid:12)
(cid:12)
(cid:12)

1
k

k
X

i=1

Xi − p

(cid:12)
(cid:12)
(cid:12)
(cid:12)
(cid:12)

> δ(cid:3) < e−

δ2
4 pk

In our case p = 1/2+n−c, and plugging in δ = n−c/2, the probability we output a wrong answer

is bounded by

(cid:4)

Pr[ 1
n

k
X

i=1

Xi ≤ 1/2 + n−c/2] ≤ e−

1
4n−2c

1
2 8n2c+d

≤ 2−nd

A similar result holds for the class RP. In fact, there we can replace the constant 2/3 with
every positive constant, and even with values as low as n−c. That is, we have the following result:
Theorem 7.12
Let L ⊆ {0, 1}∗ such that there exists a polynomial-time PTM M satisfying for every x ∈ {0, 1}∗:
(1) If x ∈ L then Pr[M (x) = 1)] ≥ n−c and (2) if x 6∈ L, then Pr[M (x) = 1] = 0.

Then for every d > 0 there exists a polynomial-time PTM M 0 such that for every x ∈ {0, 1}∗,

(1) if x ∈ L then Pr[M 0(x) = 1] ≥ 1 − 2−nd and (2) if x 6∈ L then Pr[M 0(x) = 1] = 0.

These results imply that we can take a probabilistic algorithm that succeeds with quite modest
probability and transform it into an algorithm that succeeds with overwhelming probability. In
fact, even for moderate values of n an error probability that is of the order of 2−n is so small that
for all practical purposes, probabilistic algorithms are just as good as deterministic algorithms.

If the original probabilistic algorithm used m coins, then the error reduction procedure we use
(run k independent trials and output the majority answer) takes O(m · k) random coins to reduce
the error to a value exponentially small in k. It is somewhat surprising that we can in fact do
better, and reduce the error to the same level using only O(m + k) random bits (see Section 7.5).

Web draft 2007-01-08 21:59

DRAFT

<!-- pdf-page: 9 -->
7.4. THE ROBUSTNESS OF OUR DEFINITIONS

p7.9 (123)

Note 7.13 (The Chernoff Bound)
The Chernoﬀ bound is extensively used (sometimes under diﬀerent names)
in many areas of computer science and other sciences. A typical scenario is
the following: there is a universe U of objects, a fraction µ of them have a
certain property, and we wish to estimate µ. For example, in the proof of
Theorem 7.10 the universe was the set of 2m possible coin tosses of some
probabilistic algorithm and we wanted to know how many of them cause the
algorithm to accept its input. Another example is that U may be the set of
all the citizens of the United States, and we wish to ﬁnd out how many of
them approve of the current president.
A natural approach to compute the fraction µ is to sample n members of the
universe independently at random, ﬁnd out the number k of the sample’s
members that have the property and to estimate that µ is k/n. Of course,
it may be quite possible that 10% of the population supports the president,
but in a sample of 1000 we will ﬁnd 101 and not 100 such people, and so
we set our goal only to estimate µ up to an error of ±(cid:15) for some (cid:15) > 0.
Similarly, even if only 10% of the population have a certain property, we
may be extremely unlucky and select only people having it for our sample,
and so we allow a small probability of failure δ that our estimate will be
oﬀ by more than (cid:15). The natural question is how many samples do we need
to estimate µ up to an error of ±(cid:15) with probability at least 1 − δ? The
Chernoﬀ bound tells us that (considering µ as a constant) this number is
O(log(1/δ)/(cid:15)2).
This implies that if we sample n elements, then the probability that the
number k having the property is ρ
n far from µn decays exponentially with
ρ: that is, this probability has the famous “bell curve” shape:

√

We will use this exponential decay phenomena several times in this book,
starting with the proof of Theorem 7.17, showing that BPP ⊆ P/poly.

DRAFT

Web draft 2007-01-08 21:59

kPr[]0n01mnmn+rn1/2mn-rn1/2khaveproperty

<!-- pdf-page: 10 -->
p7.10 (124)

7.4. THE ROBUSTNESS OF OUR DEFINITIONS

7.4.2 Expected running time versus worst-case running time.

When deﬁning RTIME(T (n)) and BPTIME(T (n)) we required the machine to halt in T (n) time
regardless of its random choices. We could have used expected running time instead, as in the
deﬁnition of ZPP (Deﬁnition 7.7). It turns out this yields an equivalent deﬁnition: we can add a
time counter to a PTM M whose expected running time is T (n) and ensure it always halts after
at most 100T (n) steps. By Markov’s inequality (see Lemma A.10), the probability that M runs
for more than this time is at most 1/100. Thus by halting after 100T (n) steps, the acceptance
probability is changed by at most 1/100.

7.4.3 Allowing more general random choices than a fair random coin.

One could conceive of real-life computers that have a “coin” that comes up heads with probability
ρ that is not 1/2. We call such a coin a ρ-coin. Indeed it is conceivable that for a random source
based upon quantum mechanics, ρ is an irrational number, such as 1/e. Could such a coin give
probabilistic algorithms new power? The following claim shows that it will not.

Lemma 7.14
A coin with Pr[Heads] = ρ can be simulated by a PTM in expected time O(1) provided the ith bit
of ρ is computable in poly(i) time.

Proof: Let the binary expansion of ρ be 0.p1p2p3 . . .. The PTM generates a sequence of random
bits b1, b2, . . . , one by one, where bi is generated at step i. If bi < pi then the machine outputs
“heads” and stops; if bi > pi the machine outputs “tails” and halts; otherwise the machine goes
to step i + 1. Clearly, the machine reaches step i + 1 iﬀ bj = pj for all j ≤ i, which happens with
probability 1/2i. Thus the probability of “heads” is P
1
2i , which is exactly ρ. Furthermore, the
expected running time is P
i ic · 1
2i . For every constant c this inﬁnite sum is upperbounded by
another constant (see Exercise 1). (cid:4)

i pi

Conversely, probabilistic algorithms that only have access to ρ-coins do not have less power

than standard probabilistic algorithms:

Lemma 7.15 (Von-Neumann)
A coin with Pr[Heads] = 1/2 can be simulated by a probabilistic TM with access to a stream of
ρ-biased coins in expected time O(

1
ρ(1−ρ) ).

Proof: We construct a TM M that given the ability to toss ρ-coins, outputs a 1/2-coin. The
machine M tosses pairs of coins until the ﬁrst time it gets two diﬀerent results one after the other.
If these two results were ﬁrst “heads” and then “tails”, M outputs “heads”. If these two results
were ﬁrst “tails” and then “heads”, M outputs “tails”. For each pair, the probability we get two
“heads” is ρ2, the probability we get two “tails” is (1 − ρ)2, the probability we get “head” and
then“tails” is ρ(1 − ρ), and the probability we get “tails” and then “head” is (1 − ρ)ρ. We see that
the probability we halt and output in each step is 2ρ(1 − ρ), and that conditioned on this, we do
indeed output either “heads” or “tails” with the same probability. Note that we did not need to
know ρ to run this simulation. (cid:4)

Web draft 2007-01-08 21:59

DRAFT

<!-- pdf-page: 11 -->
7.5. RANDOMNESS EFFICIENT ERROR REDUCTION.

p7.11 (125)

Weak random sources. Physicists (and philosophers) are still not completely certain that ran-
domness exists in the world, and even if it does, it is not clear that our computers have access to
an endless stream of independent coins. Conceivably, it may be the case that we only have access
to a source of imperfect randomness, that although unpredictable, does not consist of independent
coins. As we will see in Chapter 16, we do know how to simulate probabilistic algorithms designed
for perfect independent 1/2-coins even using such a weak random source.

7.5 Randomness eﬃcient error reduction.

In Section 7.4.1 we saw how we can reduce error of probabilistic algorithms by running them
several time using independent random bits each time. Ideally, one would like to be frugal with
using randomness, because good quality random number generators tend to be slower than the rest
of the computer. Surprisingly, the error reduction can be done just as eﬀectively without using
truly independent runs, and “recycling” the random bits. Now we outline this idea; a much more
general theory will be later presented in Chapter 16.

The main tool we use is expander graphs. Expander graphs have played a crucial role in nu-
merous computer science applications, including routing networks, error correcting codes, hardness
of approximation and the PCP theorem, derandomization, and more. Expanders can be deﬁned
in several roughly equivalent ways. One is that these are graphs where every set of vertices has a
very large boundary. That is, for every subset S of vertices, the number of S’s neighbors outside
S is (up to a constant factor) roughly equal to the number of vertices inside S. (Of course this
condition cannot hold if S is too big and already contains almost all of the vertices in the graph.)
For example, the n by n grid (where a vertex is a pair (i, j) and is connected to the four neighbors
(i ± 1, j ± 1)) is not an expander, as any k by k square (which is a set of size k2) in this graph only
has a boundary of size O(k) (see Figure 7.1).

Figure 7.1:
In a combinatorial expander, every subset S of the vertices that is not too big has at least Ω(|S|)
neighbors outside the set. The grid (and every other planar graph) is not a combinatorial expander as a k × k square
in the grid has only O(k) neighbors outside it.

We will not precisely deﬁne expanders now (but see Section 7.B at the end of the chapter).
However, an expander graph family is a sequence of graphs {GN }N ∈N such for every N , GN is an
N -vertex D-degree graph for some constant D. Deep mathematics (and more recently, simpler
mathematics) has been used to construct expander graphs. These constructions yield algorithms

DRAFT

Web draft 2007-01-08 21:59

Expander:no.ofS’sneighbors=Omega(|S|)Gridisnotanexpander:no.ofS’sneighbors=O(|S|1/2)

<!-- pdf-page: 12 -->
p7.12 (126)

7.6. BPP ⊆ P/POLY

that, given the binary representation of N and an index of a node in GN , can produce the indices
of the D neighbors of this node in poly(log N ) time.

We illustrate the error reduction procedure by showing how we transform an RP algorithm that
outputs the right answer with probability 1/2into an algorithm that outputs the right answer with
probability 1 − 2−Ω(k). The idea is simple: let x be an input, and suppose we have an algorithm M
using m coins such that if x ∈ L then Prr∈R{0,1}m[M (x, r) = 1] ≥ 1/2 and if x 6∈ L then M (x, r) = 0
for every r. Let N = 2m and let GN be an N -vertex expander family. We use m coins to select a
random vertex v from GN , and then use log Dk coins to take a k − 1-step random walk from v on
GN . That is, at each step we choose a random number i in [D] and move from the current vertex
to its ith neighbor. Let v1, . . . , vk be the vertices we encounter along this walk (where v1 = v). We
can treat these vertices as elements of {0, 1}m and run the machine M on input x with all of these
coins. If even one of these runs outputs 1, then output 1. Otherwise, output 0. It can be shown
that if less than half of the r’s cause M to output 0, then the probability that the walk is fully
contained in these “bad” r’s is exponentially small in k.

We see that what we need to prove is the following theorem:

Theorem 7.16
Let G be an expander graph of N vertices and B a subset of G’s vertices of size at most βN , where
β < 1. Then, the probability that a k-vertex random walk is fully contained in B is at most ρk,
where ρ < 1 is a constant depending only on β (and independent of k).

Theorem 7.16 makes intuitive sense, as in an expander graph a constant fraction of the edges
adjacent to vertices of B will have the other vertex in B’s complement, and so it seems that at each
step we will have a constant probability to leave B. However, its precise formulation and analysis
takes some care, and is done at the end of the chapter in Section 7.B.

Intuitively, We postpone the full description of the error reduction procedure and its analysis

to Section 7.B.

7.6 BPP ⊆ P/poly

Now we show that all BPP languages have polynomial sized circuits. Together with Theorem ??
this implies that if 3SAT ∈ BPP then PH = Σp
2.

Theorem 7.17 (Adleman)
BPP ⊆ P/poly.

Proof: Sup-

pose L ∈ BPP, then by the alternative deﬁnition of BPP and the error reduction procedure of
Theorem 7.10, there exists a TM M that on inputs of size n uses m random bits and satisﬁes

x ∈ L ⇒ Prr [M (x, r) accepts ] ≥ 1 − 2−(n+2)
x 6∈ L ⇒ Prr [M (x, r) accepts ] ≤ 2−(n+2)

Web draft 2007-01-08 21:59

DRAFT

<!-- pdf-page: 13 -->
7.7. BPP IS IN PH

p7.13 (127)

(Such a machine exists by the error reduction arguments mentioned earlier.)

Say that an r ∈ {0, 1}m is bad for an input x ∈ {0, 1}n if M (x, r) is an incorrect answer,
otherwise we say its good for x. For every x, at most 2 · 2m/2(n+2) values of r are bad for x. Adding
over all x ∈ {0, 1}n, we conclude that at most 2n × 2m/2(n+1) = 2m/2 strings r are bad for some
x. In other words, at least 2m − 2m/2 choices of r are good for every x ∈ {0, 1}n. Given a string
r0 that is good for every x ∈ {0, 1}n, we can hardwire it to obtain a circuit C (of size at most
quadratic in the running time of M ) that on input x outputs M (x, r0). The circuit C will satisfy
C(x) = L(x) for every x ∈ {0, 1}n. (cid:4)

7.7 BPP is in PH

At ﬁrst glance, BPP seems to have nothing to do with the polynomial hierarchy, so the next
theorem is somewhat surprising.

Theorem 7.18 (Sipser-G´acs)
BPP ⊆ Σp

2 ∩ Πp

2

Proof: It is enough to prove that BPP ⊆ Σp
BPP = coBPP).

2 because BPP is closed under complementation (i.e.,

Suppose L ∈ BPP. Then by the alternative deﬁnition of BPP and the error reduction proce-
dure of Theorem 7.10 there exists a polynomial-time deterministic TM M for L that on inputs of
length n uses m = poly(n) random bits and satisﬁes

x ∈ L ⇒ Prr [M (x, r) accepts ] ≥ 1 − 2−n
x 6∈ L ⇒ Prr [M (x, r) accepts ] ≤ 2−n

For x ∈ {0, 1}n, let Sx denote the set of r’s for which M accepts the input pair (x, r). Then
either |Sx| ≥ (1 − 2−n)2m or |Sx| ≤ 2−n2m, depending on whether or not x ∈ L. We will show how
to check, using two alternations, which of the two cases is true.

Figure 7.2: There are only two possible sizes for the set of r’s such that M (x, r) =Accept: either this set is almost
all of {0, 1}m or a tiny fraction of {0, 1}m. In the former case, a few random “shifts” of this set are quite likely to
cover all of {0, 1}m. In the latter case the set’s size is so small that a few shifts cannot cover {0, 1}m

For k = m

n + 1, let U = {u1, . . . , uk} be a set of k strings in {0, 1}m. We deﬁne GU to be a
graph with vertex set {0, 1}m and edges (r, s) for every r, s such that r = s + ui for some i ∈ [k]

DRAFT

Web draft 2007-01-08 21:59

<!-- pdf-page: 14 -->
p7.14 (128)

7.8. STATE OF OUR KNOWLEDGE ABOUT BPP

(where + denotes vector addition modulo 2, or equivalently, bitwise XOR). Note that the degree
of GU is k. For a set S ⊆ {0, 1}m, deﬁne ΓU (S) to be all the neighbors of S in the graph GU . That
is, r ∈ ΓU (S) if there is an s ∈ S and i ∈ [k] such that r = s + ui.
Claim 1: For every set S ⊆ {0, 1}m with |S| ≤ 2m−n and every set U of size k, it holds that
ΓU (S) 6= {0, 1}m. Indeed, since ΓU has degree k, it holds that |ΓU (S)| ≤ k|S| < 2m.
Claim 2: For every set S ⊆ {0, 1}m with |S| ≥ (1 − 2−n)2m there exists a set U of size k such that
ΓU (S) = {0, 1}m. We show this by the probabilistic method, by proving that for every S, if we
choose U at random by taking k random strings u1, . . . , uk, then Pr[ΓU (S) = {0, 1}m] > 0. Indeed,
for r ∈ {0, 1}m, let Br denote the “bad event” that r is not in ΓU (S). Then, Br = ∩i∈[k]Bi
r where
Bi
r is the event that r 6∈ S + ui, or equivalently, that r + ui 6∈ S (using the fact that modulo 2,
a + b = c ⇔ a = c + b). Yet, r + ui is a uniform element in {0, 1}m, and so it will be in S with
probability at least 1 − 2−n. Since B1
r are independent, the probability that Br happens is
at most (1 − 2−n)k < 2−m. By the union bound, the probability that ΓU (S) 6= {0, 1}m is bounded
by P

r , . . . , Bk

r∈{0,1}m Pr[Br] < 1.

Together Claims 1 and 2 show x ∈ L if and only if the following statement is true

∃u1, . . . , uk ∈ {0, 1}m ∀r ∈ {0, 1}m

k
_

i=1

M (x, r ⊕ ui)accepts

thus showing L ∈ Σ2. (cid:4)

7.8 State of our knowledge about BPP

We know that P ⊆ BPP ⊆ P/poly, and furthermore, that BPP ⊆ Σp
2 and so if NP = p
then BPP = P. As mentioned above, there are complexity-theoretic reasons to strongly believe
that BPP ⊆ DTIME(2(cid:15)) for every (cid:15) > 0, and in fact to reasonably suspect that BPP = P (see
Chapters 16 and 17). However, currently we are not even able to rule out that BPP = NEXP!

2 ∩ Πp

Complete problems for BPP?

Though a very natural class, BPP behaves diﬀerently in some ways from other classes we have
seen. For example, we know of no complete languages for it (under deterministic polynomial time
reductions). One reason for this diﬃculty is that the deﬁning property of BPTIME machines is
semantic, namely, that for every string they either accept with probability at least 2/3 or reject
with probability at least 1/3. Given the description of a Turing machine M , testing whether it has
this property is undecidable. By contrast, the deﬁning property of an NDTM is syntactic: given a
string it is easy to determine if it is a valid encoding of an NDTM. Completeness seems easier to
deﬁne for syntactically deﬁned classes than for semantically deﬁned ones. For example, consider
the following natural attempt at a BPP-complete language: L = {hM, xi : Pr[M (x) = 1] ≥ 2/3}.
This language is indeed BPP-hard but is not known to be in BPP. In fact, it is not in any level
of the polynomial hierarchy unless the hierarchy collapses. We note that if, as believed, BPP = P,
then BPP does have a complete problem. (One can sidestep some of the above issues by using
promise problems instead of languages, but we will not explore this.)

Web draft 2007-01-08 21:59

DRAFT

<!-- pdf-page: 15 -->
7.9. RANDOMIZED REDUCTIONS

p7.15 (129)

Does BPTIME have a hierarchy theorem?

Is BPTIME(nc) contained in BPTIME(n) for some c > 1? One would imagine not, and this
seems as the kind of result we should be able to prove using the tools of Chapter 3. However
currently we are even unable to show that BPTIME(nlog2 n) (say) is not in BPTIME(n). The
standard diagonalization techniques fail, for similar reasons as the ones above. However, recently
there has been some progress on obtaining hierarchy theorem for some closely related classes (see
notes).

7.9 Randomized reductions

Since we have deﬁned randomized algorithms, it also makes sense to deﬁne a notion of random-
ized reduction between two languages. This proves useful in some complexity settings (e.g., see
Chapters 9 and 8).

Definition 7.19
Language A reduces to language B under a randomized polynomial time reduction, denoted A ≤r B,
if there is a probabilistic TM M such that for every x ∈ {0, 1}∗, Pr[B(M (x)) = A(x)] ≥ 2/3.

We note that if A ≤r B and B ∈ BPP then A ∈ BPP. This alerts us to the possibility that we
could have deﬁned NP-completeness using randomized reductions instead of deterministic reduc-
tions, since arguably BPP is as good as P as a formalization of the notion of eﬃcient computation.
Recall that the Cook-Levin theorem shows that NP may be deﬁned as the set {L : L ≤p 3SAT}.
The following deﬁnition is analogous.

Definition 7.20 (BP · NP)
BP · NP = {L : L ≤r 3SAT}.

We explore the properties of BP·NP in the exercises, including whether or not 3SAT ∈ BP·NP.
One interesting application of randomized reductions will be shown in Chapter 9, where we
present a (variant of a) randomized reduction from 3SAT to the solving special case of 3SAT
where we are guaranteed that the formula is either unsatisﬁable or has a single unique satisfying
assignment.

7.10 Randomized space-bounded computation

A PTM is said to work in space S(n) if every branch requires space O(S(n)) on inputs of size n and
terminates in 2O(S(n)) time. Recall that the machine has a read-only input tape, and the work space
only cell refers only to its read/write work tapes. As a PTM it has two transition functions that
are applied with equal probability. The most interesting case is when the work tape has O(log n)
size. The classes BPL and RL are the two-sided error and one-sided error probabilistic analogs of
the class L deﬁned in Chapter 4.

DRAFT

Web draft 2007-01-08 21:59

<!-- pdf-page: 16 -->
p7.16 (130)

7.10. RANDOMIZED SPACE-BOUNDED COMPUTATION

Definition 7.21 ([)
The classes BPL and RL] A language L is in BPL if there is an O(log n)-space
probabilistic TM M such that Pr[M (x) = L(x)] ≥ 2/3.
A language L is in RL if there is an O(log n)-space probabilistic TM M such that
if x ∈ L then Pr[M (x) = 1] ≥ 2/3 and if x 6∈ L then Pr[M (x) = 1] = 0.

The reader can verify that the error reduction procedure described in Chapter 7 can be imple-
mented with only logarithmic space overhead, and hence also in these deﬁnitions the choice of the
precise constant is not signiﬁcant. We note that RL ⊆ NL, and thus RL ⊆ P. The exercises ask
you to show that BPL ⊆ P as well.

One famous RL-algorithm is the algorithm to solve UPATH: the restriction of the NL-complete
PATH problem (see Chapter 4) to undirected graphs. That is, given an n-vertex undirected graph
G and two vertices s and t, determine whether s is connected to t in G.

Theorem 7.22 ([AKL+79])
UPATH ∈ RL.

The algorithm for UPATH is actually very simple: take a random walk of length n3 starting
from s. That is, initialize the variable v to the vertex s and in each step choose a random neighbor
u of v, and set v ← u. Accept iﬀ the walk reaches t within n3 steps. Clearly, if s is not connected to
t then the algorithm will never accept. It can be shown that if s is connected to t then the expected
number of steps it takes for a walk from s to hit t is at most 4
27 n3 and hence our algorithm will accept
with probability at least 3
4 . We defer the analysis of this algorithm to the end of the chapter at
Section 7.A, where we will prove that a somewhat larger walk suﬃces to hit t with good probability
(see also Exercise 9).

In Chapter 16 we show a recent deterministic logspace algorithm for the same problem. It is
known that BPL (and hence also RL) is contained in SPACE(log3/2 n). In Chapter 16 we will
see a somewhat weaker result: a simulation of BPL in log2 n space and polynomial time.

Web draft 2007-01-08 21:59

DRAFT

<!-- pdf-page: 17 -->
7.10. RANDOMIZED SPACE-BOUNDED COMPUTATION

p7.17 (131)

What have we learned?

• The class BPP consists of languages that can be solved by a probabilistic
polynomial-time algorithm. The probability is only over the algorithm’s coins
and not the choice of input. It is arguably a better formalization of eﬃcient
computation than P.

• RP, coRP and ZPP are subclasses of BPP corresponding to probabilistic

algorithms with one-sided and “zero-sided” error.

• Using repetition, we can considerably amplify the success probability of prob-

abilistic algorithms.

• We only know that P ⊆ BPP ⊆ EXP, but we suspect that BPP = P.

• BPP is a subset of both P/poly and PH. In particular, the latter implies

that if NP = P then BPP = P.

• Randomness is used in complexity theory in many contexts beyond BPP. Two
examples are randomized reductions and randomized logspace algorithms, but
we will see many more later.

Chapter notes and history

Early researchers realized the power of randomization since their computations —e.g., for design
of nuclear weapons— used probabilistic tools such as Monte Carlo simulations. Papers by von
Neumann [von61] and de Leeuw et al. [LMSS56] describe probabilistic Turing machines. The
deﬁnitions of BPP, RP and ZPP are from Gill [Gil77]. (In an earlier conference paper [Gil74],
Gill studies similar issues but seems to miss the point that a practical algorithm for deciding a
language must feature a gap between the acceptance probability in the two cases.)

The algorithm used to show PRIMES is in coRP is due to Solovay and Strassen [SS77]. Another
primality test from the same era is due to Rabin [Rab80]. Over the years, better tests were proposed.
In a recent breakthrough, Agrawal, Kayal and Saxena ﬁnally proved that PRIMES ∈ P. Both the
probabilistic and deterministic primality testing algorithms are described in Shoup’s book [?].

Lov´asz’s randomized NC algorithm [Lov79] for deciding the existence of perfect matchings is
unsatisfying in the sense that when it outputs “Accept,” it gives no clue how to ﬁnd a matching!
Subsequent probabilistic NC algorithms can ﬁnd a perfect matching as well; see [KUW86, MVV87].
BPP ⊆ P/poly is from Adelman [Adl78]. BPP ⊆ PH is due to Sipser [Sip83], and the stronger
2 is due to P. G´acs. Recent work [] shows that BPP is contained in classes

2 ∩ Πp

form BPP ⊆ Σp
that are seemingly weaker than Σp

2 ∩ Πp
2.

Even though a hierarchy theorem for BPP seems beyond our reach, there has been some success
in showing hierarchy theorems for the seemingly related class BPP/1 (i.e., BPP with a single bit
of nonuniform advice) [Bar02, ?, ?].

DRAFT

Web draft 2007-01-08 21:59

<!-- pdf-page: 18 -->
p7.18 (132)

7.10. RANDOMIZED SPACE-BOUNDED COMPUTATION

Readers interested in randomized algorithms are referred to the books by Mitzenmacher and

Upfal [MU05] and Motwani and Raghavan [MR95].

still a lot missing
Expanders were well-studied for a variety of reasons in the 1970s but their application to
pseudorandomness was ﬁrst described by Ajtai, Komlos, and Szemeredi [AKS87]. Then Cohen-
Wigderson [CW89] and Impagliazzo-Zuckerman (1989) showed how to use them to “recycle” ran-
dom bits as described in Section 7.B.3. The upcoming book by Hoory, Linial and Wigderson (draft
available from their web pages) provides an excellent introduction to expander graphs and their
applications.

The explicit construction of expanders is due to Reingold, Vadhan and Wigderson [RVW00],
although we chose to present it using the replacement product as opposed to the closely related
zig-zag product used there. The deterministic logspace algorithm for undirected connectivity is due
to Reingold [?].

Exercises

§1 Show that for every c > 0, the following inﬁnite sum is ﬁnite:

ic
2i .

X

i≥1

§2 Show, given input the numbers a, n, p (in binary representation), how to compute an(modp)

in polynomial time.

Hint:usethebinaryrepresentationofnandrepeatedsquaring.

§3 Let us study to what extent Claim ?? truly needs the assumption that ρ is eﬃciently com-
putable. Describe a real number ρ such that given a random coin that comes up “Heads”
with probability ρ, a Turing machine can decide an undecidable language in polynomial time.

bitsberecovered?
Hint:thinkoftherealnumberρasanadvicestring.Howcanits

§4 Show that ZPP = RP ∩ coRP.

§5 A nondeterministic circuit has two inputs x, y. We say that it accepts x iﬀ there exists y
such that C(x, y) = 1. The size of the circuit is measured as a function of |x|. Let NP/poly
be the languages that are decided by polynomial size nondeterministic circuits. Show that
BP · NP ⊆ NP/poly.

§6 Show using ideas similar to the Karp-Lipton theorem that if 3SAT ∈ BP · NP then PH

collapses to Σp

3. (Combined with above, this shows it is unlikely that 3SAT ≤r 3SAT.)

§7 Show that BPL ⊆ P

DRAFT

Web draft 2007-01-08 21:59

<!-- pdf-page: 19 -->
7.10. RANDOMIZED SPACE-BOUNDED COMPUTATION

p7.19 (133)

matrixmultiplication.
intheacceptconﬁgurationusingeitherdynamicprogrammingor
Hint:trytocomputetheprobabilitythatthemachineendsup

§8 Show that the random walk idea for solving connectivity does not work for directed graphs.
In other words, describe a directed graph on n vertices and a starting point s such that the
expected time to reach t is Ω(2n) even though there is a directed path from s to t.

§9 Let G be an n vertex graph where all vertices have the same degree.

(a) We say that a distribution p over the vertices of G (where pi denotes the probability
that vertex i is picked by p) is stable if when we choose a vertex i according to p and
take a random step from i (i.e., move to a random neighbor j or i) then the resulting
distribution is p. Prove that the uniform distribution on G’s vertices is stable.

(b) For p be a distribution over the vertices of G, let ∆(p) = maxi{pi − 1/n}. For every
k, denote by pk the distribution obtained by choosing a vertex i at random from p and
taking k random steps on G. Prove that if G is connected then there exists k such that
∆(pk) ≤ (1 − n−10n)∆(p). Conclude that

i. The uniform distribution is the only stable distribution for G.
ii. For every vertices u, v of G, if we take a suﬃciently long random walk starting from
u, then with high probability the fraction of times we hit the vertex v is roughly
1/n. That is, for every (cid:15) > 0, there exists k such that the k-step random walk from
u hits v between (1 − (cid:15))k/n and (1 + (cid:15))k/n times with probability at least 1 − (cid:15).

(c) For a vertex u in G, denote by Eu the expected number of steps it takes for a random

walk starting from u to reach back u. Show that Eu ≤ 10n2.

fractionoftheplacesinthiswalk.
Kthenbystandardtailbounds,uappearsinlessthana2/K
Hint:considertheinﬁniterandomwalkstartingfromu.IfEu>

(d) For every two vertices u, v denote by Eu,v the expected number of steps it takes for
a random walk starting from u to reach v. Show that if u and v are connected by a
path of length at most k then Eu,v ≤ 100kn2. Conclude that for every s and t that are
connected in a graph G, the probability that an 1000n3 random walk from s does not
hit t is at most 1/10.

vdecaysexponentiallywith‘.
theprobabilitythatan‘n2-steprandomwalkfromudoesnothit
m∈NPr[X≥m]andsoitsuﬃcestoshowthat
overNisequaltoP
ofexpectation.NotethattheexpectationofarandomvariableX
anedge),thecaseofk>1canbereducedtothisusinglinearity
Hint:Startwiththecasek=1(i.e.,uandvareconnectedby

(e) Let G be an n-vertex graph that is not necessarily regular (i.e., each vertex may have
diﬀerent degree). Let G0 be the graph obtained by adding a suﬃcient number of parallel
self-loops to each vertex to make G regular. Prove that if a k-step random walk in G0
from a vertex s hits a vertex t with probability at least 0.9, then a 10n2k-step random
walk from s will hit t with probability at least 1/2.

DRAFT

Web draft 2007-01-08 21:59

<!-- pdf-page: 20 -->
p7.20 (134)

7.10. RANDOMIZED SPACE-BOUNDED COMPUTATION

The following exercises are based on Sections 7.A and 7.B.

§10 Let A be a symmetric stochastic matrix: A = A† and every row and column of A has non-

negative entries summing up to one. Prove that kAk ≤ 1.

equalityhw,Bzi=hB†w,ziandtheinequalityhw,zi≤kwk2kzk2.
everyk≥1,AkisalsostochasticandkA2kvk2≥kAkvk2
usingthe
Hint:ﬁrstshowthatkAkisatmostsayn2.Then,provethatfor

2

§11 Let A, B be two symmetric stochastic matrices. Prove that λ(A + B) ≤ λ(A) + λ(B).

§12 Let a n, d random graph be an n-vertex graph chosen as follows: choose d random permuta-
tions π1, ldots, πd from [n] to [n]. Let the the graph G contains an edge (u, v) for every pair
u, v such that v = πi(u) for some 1 ≤ i ≤ d. Prove that a random n, d graph is an (n, 2d, 2
3 d)
combinatorial expander with probability 1 − o(1) (i.e., tending to one with n).

everyi.
3d)|S|,trytoboundtheprobabilitythatπi(S)⊆Tfor
|T|≤(1+2
Hint:foreverysetS⊆nwith|S|≤n/2andsetT⊆[n]with

DRAFT

Web draft 2007-01-08 21:59

<!-- pdf-page: 21 -->
7.A. RANDOM WALKS AND EIGENVALUES

p7.21 (135)

The following two section assume some knowledge of elementary linear algebra (vector spaces and
Hilbert spaces); see Appendix A for a quick review.

7.A Random walks and eigenvalues

In this section we study random walks on (undirected regular) graphs, introducing several important
notions such as the spectral gap of a graph’s adjacency matrix. As a corollary we obtain the proof
of correctness for the random-walk space-eﬃcient algorithm for UPATH of Theorem 7.22. We will
see that we can use elementary linear algebra to relate parameters of the graph’s adjacency matrix
to the behavior of the random walk on that graph.

Remark 7.23
In this section, we restrict ourselves to regular graphs, in which every vertex have the same degree,
although the deﬁnitions and results can be suitably generalized to general (non-regular) graphs.

7.A.1 Distributions as vectors and the parameter λ(G).

Let G be a d-regular n-vertex graph. Let p be some probability distribution over the vertices of G.
We can think of p as a (column) vector in Rn where pi is the probability that vertex i is obtained
by the distribution. Note that the L1-norm of p (see Note 7.24), deﬁned as |p|1 = Pn
i=1 |pi|, is
equal to 1. (In this case the absolute value is redundant since pi is always between 0 and 1.)

Now let q represent the distribution of the following random variable: choose a vertex i in G
according to p, then take a random neighbor of i in G. We can compute q as a function of p: the
probability qj that j is chosen is equal to the sum over all j’s neighbors i of the probability pi that
i is chosen times 1/d (where 1/d is the probability that, conditioned on i being chosen, the walk
moves to q). Thus q = Ap, where A = A(G) which is the normalized adjacency matrix of G. That
is, for every two vertices i, j, Ai,j is equal to the number of edges between i and j divided by d.
Note that A is a symmetric matrix,3 where each entry is between 0 and 1, and the sum of entries
in each row and column is exactly one (such a matrix is called a symmetric stochastic matrix).

Let {ei}n

i=1 be the standard basis of Rn (i.e. ei has 1 in the ith coordinate and zero everywhere
else). Then, AT es represents the distribution XT of taking a T -step random walk from the vertex
s. This already suggests that considering the adjacency matrix of a graph G could be very useful
in analyzing random walks on G.

Definition 7.25 (The parameter λ(G).)
Denote by 1 the vector (1/n, 1/n, . . . , 1/n) corresponding to the uniform distri-
bution. Denote by 1⊥ the set of vectors perpendicular to 1 (i.e., v ∈ 1⊥ if
hv, 1i = (1/n) P
The parameter λ(A), denoted also as λ(G), is the maximum value of kAvk2 over all
vectors v ∈ 1⊥ with kvk2 = 1.

i vi = 0).

3A matrix A is symmetric if A = A†, where A† denotes the transpose of A. That is, (A†)i,j = Aj,i for every i, j.

DRAFT

Web draft 2007-01-08 21:59

<!-- pdf-page: 22 -->
p7.22 (136)

7.A. RANDOM WALKS AND EIGENVALUES

Note 7.24 (Lp Norms)
A norm is a function mapping a vector v into a real number kvk satisfying
(1) kvk ≥ 0 with kvk = 0 if and only v is the all zero vector, (2) kαvk =
|α| · kvk for every α ∈ R, and (3) kv + uk ≤ kvk + kuk for every vector u.
The third inequality implies that for every norm, if we deﬁne the distance
between two vectors u,v as ku − vk then this notion of distance satisﬁes the
triangle inequality.
For every v ∈ Rn and number p ≥ 1, the Lp norm of v, denoted kvkp, is equal
to (Pn
i=1 |vi|p)1/p. One particularly interesting case is p = 2, the so-called
i = phv, vi. Another interesting
i=1 v2
Euclidean norm, in which kvk2 =
case is p = 1, where we use the single bar notation and denote |v|1 =
Pn
i=1 |vi|. Another case is p = ∞, where we denote kvk∞ = limp→∞ kvkp =

qPn

p + 1

maxi∈[n] |vi|.
The H¨older inequality says that for every p, q with 1
Pn

q = 1, kukpkvkq ≥
i=1 |uivi|. To prove it, note that by simple scaling, it suﬃces to con-
sider norm one vectors, and so it enough to show that if kukp = kvkq = 1
then Pn
i=1 |ui|p(1/p)|vi|q(1/q) ≤
Pn
q = 1, where the last inequality uses the fact
that for every a, b > 0 and α ∈ [0, 1], aαb1−α ≤ αa + (1 − α)b. This fact is
due to the log function being concave— having negative second derivative,
implying that α log a + (1 − α) log b ≤ log(αa + (1 − α)b).
Setting p = 1 and q = ∞, the H¨older inequality implies that

i=1 |ui||vi| ≤ 1. But Pn

i=1 |ui||vi| = Pn

q |vi|q = 1

p |ui|p + 1

p + 1

i=1

1

kvk2 ≤ |v|1kvk∞

Setting p = q = 2,
Schwartz Inequality stating that Pn
(1/
n), we get that

n, . . . , 1/

n, 1/

√

√

√

the H¨older inequality becomes the Cauchy-
i=1 |uivi| ≤ kuk2kvk2. Setting u =

√

|v|1/

n =

n
X

i=1

1√
n |vi| ≤ kvk2

DRAFT

Web draft 2007-01-08 21:59

<!-- pdf-page: 23 -->
p7.23 (137)

7.A. RANDOM WALKS AND EIGENVALUES
Remark 7.26
The value λ(G) is often called the second largest eigenvalue of G. The reason is that since A is a
symmetric matrix, we can ﬁnd an orthogonal basis of eigenvectors v1, . . . , vn with corresponding
eigenvalues λ1, . . . , λn which we can sort to ensure |λ1| ≥ |λ2| . . . ≥ |λn|. Note that A1 = 1.
Indeed, for every i, (A1)i is equal to the inner product of the ith row of A and the vector 1 which
(since the sum of entries in the row is one) is equal to 1/n. Thus, 1 is an eigenvector of A with
the corresponding eigenvalue equal to 1. One can show that a symmetric stochastic matrix has
all eigenvalues with absolute value at most 1 (see Exercise 10) and hence we can assume λ1 = 1
and v1 = 1. Also, because 1⊥ = Span{v2, . . . , vn}, the value λ above will be maximized by (the
normalized version of) v2, and hence λ(G) = |λ2|. The quantity 1 − λ(G) is called the spectral gap
of the graph. We note that some texts use un-normalized adjacency matrices, in which case λ(G)
is a number between 0 and d and the spectral gap is deﬁned to be d − λ(G).

One reason that λ(G) is an important parameter is the following lemma:

Lemma 7.27
For every regular n vertex graph G = (V, E) let p be any probability distribution over V , then

kAT p − 1k2 ≤ λT

Proof: By the deﬁnition of λ(G), kAvk2 ≤ λkvk2 for every v ⊥ 1. Note that if v ⊥ 1 then
Av ⊥ 1 since h1, Avi = hA†1, vi = h1, vi = 0 (as A = A† and A1 = 1). Thus A maps the space
1⊥ to itself and since it shrinks any member of this space by at least λ, λ(AT ) ≤ λ(A)T . (In fact,
using the eigenvalue deﬁnition of λ, it can be shown that λ(AT ) = λ(A).)

Let p be some vector. We can break p into its components in the spaces parallel and orthogonal
to 1 and express it as p = α1 + p0 where p0 ⊥ 1 and α is some number. If p is a probability
distribution then α = 1 since the sum of coordinates in p0 is zero. Therefore,

AT p = AT (1 + p0) = 1 + AT p0

Since 1 and p0 are orthogonal, kpk2

2 = k1k2

2 + kp0k2

2 and in particular kp0k2 ≤ kpk2. Since p is

a probability vector, kpk2 ≤ |p|1 · 1 ≤ 1 (see Note 7.24). Hence kp0k2 ≤ 1 and

kAT p − 1k2 = kAT p0k2 ≤ λT

(cid:4)

It turns out that every connected graph has a noticeable spectral gap:

Lemma 7.28
For every d-regular connected G with self-loops at each vertex, λ(G) ≤ 1 − 1

8dn3 .

Proof: Let u ⊥ 1 be a unit vector and let v = Au. We’ll show that 1 − kvk2
kvk2

2 ≥ 1

d4n3 which implies

2 ≤ 1 − 1

d4n3 and hence kvk2 ≤ 1 − 1

DRAFT

Web draft 2007-01-08 21:59

d8n3 .

<!-- pdf-page: 24 -->
p7.24 (138)

7.A. RANDOM WALKS AND EIGENVALUES

Since kuk2 = 1, 1 − kvk2

2 = kuk2
where i, j range from 1 to n. Indeed,

2 − kvk2

2. We claim that this is equal to P

i,j Ai,j(ui − vj)2

Ai,j(ui − vj)2 =

X

i,j

X

i,j

Ai,ju2

i − 2

X

i,j

Ai,juivj +

X

Ai,jv2

j =

i,j
2 − 2hAu, vi + kvk2

kuk2

2 = kuk2

2 − 2kvk2

2 + kvk2
2 ,

where these equalities are due to the sum of each row and column in A equalling one, and because
kvk2

2 = hv, vi = hAu, vi = P
Thus it suﬃces to show P

i,j Ai,juivj.
i,j Ai,j(ui − vj)2 ≥ 1
suﬃces to show that for some i, j, Ai,j(ui − vj)2 ≥ 1
Ai,i ≥ 1/d for all i, and so we can assume |ui − vi| < 1
done.

d4n3 . This is a sum of non-negative terms so it
d4n3 . First, because we have all the self-loops,
2n1.5 for every i ∈ [n], as otherwise we’d be

√

n and so u1 −un ≥ 1/

Now sort the coordinates of u from the largest to the smallest, ensuring that u1 ≥ u2 ≥ · · · un.
Since P
i ui = 0 it must hold that u1 ≥ 0 ≥ un. In fact, since u is a unit vector, either u1 ≥ 1/
n
n. One of the n−1 diﬀerences between consecutive coordinates
or un ≤ 1/
ui − ui+1 must be at least 1/n1.5 and so there must be an i0 such that if we let S = {1, . . . , i0}
and S = [n] \ Si, then for every i ∈ S and j ∈ S, ui − uj ≥ 1/n1.5. Since G is connected there
exists an edge (i, j) between S and S. Since |vj − uj| ≤ 1
2n1.5 , for this choice of i, j, |ui − vj| ≥
|ui − uj| − 1

2n1.5 . Thus Ai,j(ui − vj)2 ≥ 1

2n1.5 ≥ 1

4n3 . (cid:4)

√

√

d

1

Remark 7.29
The proof can be strengthened to show a similar result for every connected non-bipartite graph
if A is the
(not just those with self-loops at every vertex). Note that this condition is essential:
adjacency matrix of a bipartite graph then one can ﬁnd a vector v such that Av = −v.

7.A.2 Analysis of the randomized algorithm for undirected connectivity.

Together, Lemmas 7.27 and 7.28 imply that, at least for regular graphs, if s is connected to t then
a suﬃciently long random walk from s will hit t in polynomial time with high probability.

Corollary 7.30
Let G be a d-regular n-vertex graph with all vertices having a self-loop. Let s be a vertex in G.
Let T > 10dn3 log n and let XT denote the distribution of the vertex of the T th step in a random
walk from s. Then, for every j connected to s, Pr[XT = j] > 1
2n .

Proof: By these Lemmas, if we consider the restriction of an n-vertex graph G to the connected
component of s, then for every probability vector p over this component and T ≥ 10dn3 log n,
kAT p − 1k2 < 1
2n1.5 (where 1 here is the uniform distribution over this component). Using the
relations between the L1 and L2 norms (see Note 7.24), |AT p − 1|1 < 1
2n and hence every element
in the connected component appears in AT p with at least 1/n − 1/(2n) ≥ 1/(2n) probability. (cid:4)

Note that Corollary 7.30 implies that if we repeat the 10dn3 log n walk for 10n times (or equiv-

alently, if we take a walk of length 100dn4 log n) then we will hit t with probability at least 3/4.

Web draft 2007-01-08 21:59

DRAFT

<!-- pdf-page: 25 -->
7.B. EXPANDER GRAPHS.
7.B Expander graphs.

p7.25 (139)

Expander graphs are extremely useful combinatorial objects, which we will encounter several times
in the book. They can be deﬁned in two equivalent ways. At a high level, these two equivalent
deﬁnitions can be described as follows:

• Combinatorial deﬁnition: A constant-degree regular graph G is an expander if for every subset
S of less than half of G’s vertices, a constant fraction of the edges touching S are from S to
its complement in G. This is the deﬁnition alluded to in Section 7.5 (see Figure 7.1).4

• Algebraic expansion: A constant-degree regular graph G is an expander if its parameter λ(G)
bounded away from 1 by some constant. That is, λ(G) ≤ 1 − (cid:15) for some constant (cid:15) > 0¿

What do we mean by a constant? By constant we refer to a number that is independent of the size
of the graph. We will typically talk about graphs that are part of an inﬁnite family of graphs, and
so by constant we mean a value that is the same for all graphs in the family, regardless of their
size.

Below we make the deﬁnitions more precise, and show their equivalence. We will then complete

the analysis of the randomness eﬃcient error reduction procedure described in Section 7.5.

7.B.1 The Algebraic Deﬁnition

.

The Algebraic deﬁnition of expanders is as follows:

Definition 7.31 ((n, d, λ)-graphs.)
If G is an n-vertex d-regular G with λ(G) ≤ λ for some number λ < 1 then we say
that G is an (n, d, λ)-graph.
A family of graphs {Gn}n∈N is an expander graph family if there are some constants
d ∈ N and λ < 1 such that for every n, Gn is an (n, d, λ)-graph.

Explicit constructions. We say that an expander family {Gn}n∈N is explicit if there is a
polynomial-time algorithm that on input 1n with n ∈ I outputs the adjacency matrix of Gn.
We say that the family is strongly explicit if there is a polynomial-time algorithm that for every
n ∈ I on inputs hn, v, ii where 1 ≤ v ≤ n0 and 1 ≤ i ≤ d outputs the ith neighbor of v. (Note that
the algorithm runs in time polynomial in the its input length which is polylogarithmic in n.)

As we will see below it is not hard to show that expander families exist using the probabilistic
method. But this does not yield explicit (or very explicit) constructions of such graphs (which, as
we saw in Section 7.4.1 are often needed for applications). In fact, there are also several explicit and

4The careful reader might note that there we said that a graph is an expander if a constant fraction of S’s

neighboring vertices are outside S. However, for constant-degree graphs these two notions are equivalent.

DRAFT

Web draft 2007-01-08 21:59

<!-- pdf-page: 26 -->
p7.26 (140)

7.B. EXPANDER GRAPHS.

Note 7.33 (Explicit construction of pseudorandom objects)
Expanders are one instance of a recurring theme in complexity theory (and
other areas of math and computer science): it is often the case that a ran-
dom object can be easily proven to satisfy some nice property, but the ap-
In our case,
plications require an explicit object satisfying this property.
a random d-regular graph is an expander, but to use it for, say, reducing
the error of probabilistic algorithms, we need an explicit construction of an
expander family, with an eﬃcient deterministic algorithm to compute the
neighborhood relations. Such explicit constructions can be sometimes hard
to come by, but are often surprisingly useful. For example, in our case the
explicit construction of expander graphs turns out to yield a deterministic
logspace algorithm for undirected connectivity.
We will see another instance of this theme in Chapter 17, which discusses
error correcting codes.

√

d−1
d

strongly explicit constructions of expander graphs known. The smallest λ can be for a d-regular
n-vertex graph is Ω( 1√
) and there are constructions meeting this bound (speciﬁcally the bound
d
is (1 − o(1)) 2
where by o(1) we mean a function that tends to 0 as the number of vertices
grows; graphs meeting this bound are called Ramanujan graphs). However, for most applications in
Computer Science, any family with constant d and λ < 1 will suﬃce (see also Remark 7.32 below).
Some of these constructions are very simple and eﬃcient, but their analysis is highly non-trivial
and uses relatively deep mathematics.5 In Chapter 16 we will see a strongly explicit construction
of expanders with elementary analysis. This construction also introduces a tool that is useful to
derandomize the random-walk algorithm for UPATH.

Remark 7.32
One reason that the particular constants of an expander family are not extremely crucial is that we
can improve the constant λ (make it arbitrarily smaller) at the expense of increasing the degree:
this follows from the fact, observed above in the proof of Lemma 7.27, that λ(GT ) = λ(G)T , where
GT denotes the graph obtained by taking the adjacency matrix to the T th power, or equivalently,
having an edge for every length-T path in G. Thus, we can transform an (n, d, λ) graph into an
(n, dT , λT )-graph for every T ≥ 1.
In Chapter 16 we will see a diﬀerent transformation called
the replacement product to decrease the degree at the expense of increasing λ somewhat (and also
increasing the number of vertices).

5An example for such an expander is the following 3-regular graph: the vertices are the numbers 1 to p − 1 for

some prime p, and each number x is connected to x + 1,x − 1 and x−1

(mod p).

Web draft 2007-01-08 21:59

DRAFT

<!-- pdf-page: 27 -->
7.B. EXPANDER GRAPHS.

p7.27 (141)

7.B.2 Combinatorial expansion and existence of expanders.

We describe now a combinatorial criteria that is roughly equivalent to Deﬁnition 7.31. One ad-
vantage of this criteria is that it makes it easy to prove that a non-explicit expander family exists
using the probabilistic method. It is also quite useful in several applications.

Definition 7.34 ([)
Combinatorial (edge) expansion] An n-vertex d-regular graph G = (V, E) is called
an (n, d, ρ)-combinatorial expander if for every subset S ⊆ V with |S| ≤ n/2,
|E(S, S)| ≥ ρd|S|, where for subsets S, T of V , E(S, T ) denotes the set of edges
(s, t) with s ∈ S and t ∈ T .

Note that in this case the bigger ρ is the better the expander. We’ll loosely use the term expander
for any (n, d, ρ)-combinatorial expander with c a positive constant. Using the probabilistic method,
one can prove the following theorem: (Exercise 12 asks you to prove a slightly weaker version)
Theorem 7.35 (Existence of expanders)
Let (cid:15) > 0 be some constant. Then there exists d = d((cid:15)) and N ∈ N such that for every n > N
there exists an (n, d, 1 − (cid:15))-combinatorial expander.

The following theorem related combinatorial expansion with our previous Deﬁnition 7.31

Theorem 7.36 (Combinatorial and algebraic expansion)

1. If G is an (n, d, λ)-graph then it is an (n, d, (1 − λ)/2)-combinatorial expander.

2. If G is an (n, d, ρ)-combinatorial expander then it is an (n, d, 1 − ρ2

2 )-graph.

The ﬁrst part of Theorem 7.36 follows by plugging T = S into the following lemma:

Lemma 7.37 (Expander Mixing Lemma)
Let G = (V, E) be an (n, d, λ)-graph. Let S, T ⊆ V , then

(cid:12)
(cid:12)
(cid:12)
(cid:12)

|E(S, T )| −

(cid:12)
(cid:12)
|S||T |
(cid:12)
(cid:12)

d
n

≤ λdp|S||T |

Proof: Let s denote the vector such that si is equal to 1 if i ∈ S and equal to 0 otherwise, and let
t denote the corresponding vector for the set S. Thinking of s as a row vector and of t as a column
vector, the Lemma’s statement is equivalent to
(cid:12)
(cid:12)sAt − |S||T |
(cid:12)

(cid:12)
(cid:12) ≤ λp|S||T | ,
(cid:12)

(2)

n

where A is G’s normalized adjacency matrix. Yet by Lemma 7.40, we can write A as (1 − λ)J + λC,
where J is the matrix with all entries equal to 1/n and C has norm at most one. Hence,

sAt = (1 − λ)sJt + λsCt ≤ |S||T |

n + λp|S||T | ,

DRAFT

Web draft 2007-01-08 21:59

<!-- pdf-page: 28 -->
7.B. EXPANDER GRAPHS.
p7.28 (142)
where the last inequality follows from sJt = |S||T |/n and sCt = hs, Cti ≤ ksk2ktk2 = p|S||T |. (cid:4)
Proof of second part of Theorem 7.36.: We prove a slightly relaxed version, replacing
the constant 2 with 8. Let G = (V, E) be an n-vertex d-regular graph such that for every subset
S ⊆ V with |S| ≤ n/2, there are ρ|S| edges between S and S = V \ S, and let A be G’s normalized
adjacency matrix.

Let λ = λ(G). We need to prove that λ ≤ 1 − ρ2/8. Using the fact that λ is the second
eigenvalue of A, there exists a vector u ⊥ 1 such that Au = λu. Write u = v + w where v is equal
to u on the coordinates on which u is positive and equal to 0 otherwise, and w is equal to u on the
coordinates on which u is negative, and equal to 0 otherwise. Note that, since u ⊥ 1, both v and
w are nonzero. We can assume that u is nonzero on at most n/2 of its coordinates (as otherwise
we can take −u instead of u).

Since Au = λu and hv, wi = 0,

hAv, vi + hAw, vi = hA(v + w), vi = hAu, vi = hλ(v + w), vi = λkvk2
2 .

Since hAw, vi is negative, we get that hAv, vi/kvk2

2 ≥ λ or

1 − λ ≥ 1 −

hAv, vi
kvk2
2

=

kvk2

2 − hAv, vi
kvk2
2

=

P

i,j Ai,j(vi − vj)2
2kvk2
2
i − 2 P

,

where the last equality is due to P
2kvk2
both numerator and denominator by P
can bound the new numerator as follows:

j =
2 − 2hAv, vi. (We use here the fact that each row and column of A sums to one.) Multiply
i + v2
j ). By the Cauchy-Schwartz inequality,6 we

i,j Ai,j(vi − vj)2 = P

i,j Ai,jvivj + P

i,j Ai,j(v2

i,j Ai,jv2

i,j Ai,jv2





X

i,j









Ai,j(vi − vj)2



X



i,j

Ai,j(vi + vj)2

 ≤

X



i,j



2

Ai,j(vi − vj)(vi + vj)



.

Hence, using (a − b)(a + b) = a2 − b2,

1 − λ ≥

(cid:16)P

2kvk2
2

(cid:17)2

i,j Ai,j(v2
P

i − v2
j )
i,j Ai,j(vi + vj)2 =

(cid:16)P

2kvk2
2

i,j Ai,jv2

(cid:16)P

(cid:17)2

i,j Ai,j(v2
i + 2 P

i − v2
j )
i,j Ai,jvivj + P
(cid:17)2

(cid:16)P

(cid:17) =

i,j Ai,jv2
j

(cid:16)P

2kvk2
2

i,j Ai,j(v2
(cid:0)2kvk2

i − v2
j )
2 + 2hAv, vi(cid:1) ≥

(cid:17)2

i − v2
j )

,

i,j Ai,j(v2
8kvk4
2

where the last inequality is due to A having matrix norm at most 1, implying hAv, vi ≤ kvk2
conclude the proof by showing that

2. We

Ai,j(v2

i − v2

j ) ≥ ρkvk2
2 ,

X

i,j

(3)

6The Cauchy-Schwartz inequality is typically stated as saying that for x, y ∈ Rn, P

i µixiyi ≤ p(P
However, it is easily generalized to show that for every non-negative µ1, . . . , µn, P
(this can be proven from the standard Cauchy-Schwartz by multiplying each coordinate of x and y by
variant that we use here with the Ai,j’s playing the role of µ1, . . . , µn.

i xiyi ≤ p(P
i µix2
√

i )(P
i x2
i y2
i ).
i )(P
i µiy2
i )
µi. It is this

Web draft 2007-01-08 21:59

DRAFT

<!-- pdf-page: 29 -->
7.B. EXPANDER GRAPHS.

which indeed implies that 1 − λ ≥

= ρ2
8 .

p7.29 (143)

ρ2kvk4
2
8kvk4
2

To prove (3) sort the coordinates of v so that v1 ≥ v2 ≥ · · · ≥ vn (with vi = 0 for i > n/2).

Then

X

Ai,j(v2

i − v2

j ) ≥

n/2
X

n
X

Ai,j(v2

i − v2

i+1) =

n/2
X

ci(v2

i − v2

i+1) ,

i,j
where ci denotes P
j>i Ai,j. But ci is equal to the number of edges in G from the set {k : k ≤ i} to
its complement, divided by d. Hence, by the expansion of G, ci ≥ ρi, implying (using the fact that
vi = 0 for i ≥ n/2):

j=i+1

i=1

i=1

Ai,j(v2

i − v2

j ) ≥

X

i,j

n/2
X

i=1

ρi(v2

i − v2

i+1) =

n/2
X

i=1

(ρiv2

i − ρ · (i − 1)v2

i ) = ρkvk2
2 ,

establishing (3). (cid:4)

7.B.3 Error reduction using expanders.

We now complete the analysis of the randomness eﬃcient error reduction procedure described in
Section 7.5. Recall, that this procedure was the following: let N = 2m where m is the number of
coins the randomized algorithm uses. We use m + O(k) random coins to select a k-vertex random
walk in an expander graph GN , and then output 1 if and only if the algorithm outputs 1 when given
one of the vertices in the walk as random coins. To show this procedure works we need to show
that if the probabilistic algorithm outputs 1 for at least half of the coins, then the probability that
all the vertices of the walk correspond to coins on which the algorithm outputs 0 is exponentially
small in k. This will be a direct consequence of the following theorem: (think of the set B below
as the set of vertices corresponding to coins on which the algorithm outputs 0)

Theorem 7.38 (Expander walks)
Let G be an (N, d, λ) graph, and let B ⊆ [N ] be a set with |B| ≤ βN . Let X1, . . . , Xk
be random variables denoting a k −1-step random walk from X1, where X1 is chosen
uniformly in [N ]. Then,

Pr[∀1≤i≤kXi ∈ B]
(∗)

≤ ((1 − λ)pβ + λ)k−1

Note that if λ and β are both constants smaller than 1 then so is the expression (1 − λ)

β + λ.
Proof: For 1 ≤ i ≤ k, let Bi be the event that Xi ∈ B. Note that the probability (∗) we’re trying
to bound is Pr[B1] Pr[B2|B1] · · · Pr[Bk|B1, . . . , Bk−1]. Let pi ∈ RN be the vector representing
the distribution of Xi, conditioned on the events B1, . . . , Bi. Denote by ˆB the following linear
transformation from Rn to Rn: for every u ∈ RN , and j ∈ [N ], ( ˆBu)j = uj if j ∈ B and ( ˆBu)j = 0
ˆB1 (recall that 1 = (1/N, . . . , 1/N ) is the
otherwise.

It’s not hard to verify that p1 = 1

Pr[B1]

√

DRAFT

Web draft 2007-01-08 21:59

<!-- pdf-page: 30 -->
p7.30 (144)

7.B. EXPANDER GRAPHS.

vector representing the uniform distribution over [N ]). Similarly, p2 =
A = A(G) is the adjacency matrix of G. Since every probability vector p satisﬁes |p|1 = 1,

1
Pr[B2|B1]

1
Pr[B1]

ˆBA ˆB1 where

We bound this norm by showing that

(∗) = |( ˆBA)k−1 ˆB1|1

k( ˆBA)k−1 ˆB1k2 ≤ ((1−λ)
√

√
√

β+λ)k−1
N

(4)

which suﬃces since for every v ∈ RN , |v|1 ≤

N kvk2 (see Note 7.24).

To prove (4), we use the following deﬁnition and lemma:

Definition 7.39 (Matrix Norm)
If A is an m by n matrix, then kAk is the maximum number α such that kAvk2 ≤ αkvk2 for every
v ∈ Rn.

Note that if A is a normalized adjacency matrix then kAk = 1 (as A1 = 1 and kAvk2 ≤ kvk2
for every v). Also note that the matrix norm satisﬁes that for every two n by n matrices A, B,
kA + Bk ≤ kAk + kBk and kABk ≤ kAkkBk.

Lemma 7.40
Let A be a normalized adjacency matrix of an (n, d, λ)-graph G. Let J be the adjacency matrix of
the n-clique with self loops (i.e., Ji,j = 1/n for every i, j). Then

A = (1 − λ)J + λC

(5)

where kCk ≤ 1.

Note that for every probability vector p, Jp is the uniform distribution, and so this lemma
tells us that in some sense, we can think of a step on a (n, d, λ)-graph as going to the uniform
distribution with probability 1 − λ, and to a diﬀerent distribution with probability λ. This is of
course not completely accurate, as a step on a d-regular graph will only go the one of the d neighbors
of the current vertex, but we’ll see that for the purposes of our analysis, the condition (5) will be
just as good.7
Proof of Lemma 7.40:
λ (A − (1 − λ)J). We need to prove kCvk2 ≤
kvk2 for very v. Decompose v as v = u + w where u is α1 for some α and w ⊥ 1, and kvk2
2 =
kuk2
λ (u − (1 − λ)u) = u. Now, let
w0 = Aw. Then kw0k2 ≤ λkwk2 and, as we saw in the proof of Lemma 7.27, w0 ⊥ 1. Furthermore,
since the sum of the coordinates of w is zero, Jw = 0. We get that Cw = 1
λ w0. Since w0 ⊥ u,
kCwk2

2 + kwk2
Returning to the proof of Theorem 7.38, we can write ˆBA = ˆB(cid:0)(1 − λ)J + λC(cid:1), and hence
k ˆBAk ≤ (1 − λ)k ˆBJk + λk ˆBCk. Since J’s output is always a vector of the form α1, k ˆBJk ≤
β.
Also, because ˆB is an operation that merely zeros out some parts of its input, k ˆBk ≤ 1 implying

2. Since A1 = 1 and J1 = 1 we get that Cu = 1

Indeed, simply deﬁne C = 1

2 = ku + 1

2 + kwk2

2 = kwk2

2 = kuk2

2 ≤ kuk2

2 + k 1

λ w0k2

λ w0k2

2. (cid:4)

√

7Algebraically, the reason (5) is not equivalent to going to the uniform distribution in each step with probability

1 − λ is that C is not necessarily a stochastic matrix, and may have negative entries.

Web draft 2007-01-08 21:59

DRAFT

<!-- pdf-page: 31 -->
7.B. EXPANDER GRAPHS.

p7.31 (145)

√

k ˆBCk ≤ 1. Thus, k ˆBAk ≤ (1 − λ)
and hence k( ˆBA)k−1 ˆB1k2 ≤ ((1 − λ)

β + λ. Since B1 has the value 1/N in |B| places, kB1k2 =
√

√
β√
N
One can obtain a similar error reduction procedure for two-sided error algorithms by running
the algorithm using the k sets of coins obtained from a k − 1 step random walk and deciding on the
output according to the majority of the values obtained. The analysis of this procedure is based
on the following theorem, whose proof we omit:

, establishing (4). (cid:4)

β + λ)k−1

,

√
β√
N

Theorem 7.41 (Expander Chernoff Bound [?])
Let G be an (N, d, λ)-graph and B ⊆ [N ] with |B| = βN . Let X1, . . . , Xk be random
variables denoting a k − 1-step random walk in G (where X1 is chosen uniformly).
For every i ∈ [k], deﬁne Bi to be 1 if Xi ∈ B and 0 otherwise. Then, for every δ > 0,

h

|

Pr

Pk

i=1 Bi
k

i

− β| > δ

< 2e(1−λ)δ2k/60

DRAFT

Web draft 2007-01-08 21:59

<!-- pdf-page: 32 -->
p7.32 (146)

7.B. EXPANDER GRAPHS.

DRAFT

Web draft 2007-01-08 21:59

<!-- pdf-page: 33 -->
Chapter 8

Interactive proofs

“What is intuitively required from a theorem-proving procedure? First, that it is
possible to “prove” a true theorem. Second, that it is impossible to “prove” a false
theorem. Third, that communicating the proof should be eﬃcient, in the following
It does not matter how long must the prover compute during the proving
sense.
process, but it is essential that the computation required from the veriﬁer is easy.”
Goldwasser, Micali, Rackoﬀ 1985

The standard notion of a mathematical proof follows the certiﬁcate deﬁnition of NP. That is,
to prove that a statement is true one provides a sequence of symbols that can be written down in a
book or on paper, and a valid sequence exists only for true statements. However, people often use
more general ways to convince one another of the validity of statements: they interact with one
another, with the person verifying the proof (henceforth the veriﬁer ) asking the person providing
it (henceforth the prover ) for a series of explanations before he is convinced.

It seems natural to try to understand the power of such interactive proofs from the complexity-
theoretic perspective. For example, can one prove that a given formula is not satisﬁable? (recall
that is this problem is coNP-complete, it’s not believed to have a polynomial-sized certiﬁcate).
The surprising answer is yes.
Indeed, interactive proofs turned out to have unexpected powers
and applications. Beyond their philosophical appeal, interactive proofs led to fundamental insights
in cryptographic protocols, the power of approximation algorithms, program checking, and the
hardness of famous “elusive” problems (i.e., NP-problems not known to be in P nor to be NP-
complete) such as graph isomorphism and approximate shortest lattice vector.

8.1 Warmup: Interactive proofs with a deterministic veriﬁer

Let us consider what happens when we introduce interaction into the NP scenario. That is, we’d
have an interrogation-style proof system where rather than the prover send a written proof to the
veriﬁer, the prover and veriﬁer interact with the veriﬁer asking questions and the prover responding,
where at the end the veriﬁer decides whether or not to accept the input. Of course, both veriﬁer
and prover can keep state during the interaction, or equivalently, the message a party sends at any

DRAFT

Web draft 2007-01-08 21:59
p8.1 (147)
Complexity Theory: A Modern Approach. © 2006 Sanjeev Arora and Boaz Barak. References and attributions are
still incomplete.
