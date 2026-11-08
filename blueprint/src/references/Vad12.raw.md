<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: bf2ce542208824ebf39ce132aae2d26a3b90bc04d3496a4ec05361f27e62118c -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
Foundations and Trends R(cid:1) in
Theoretical Computer Science
Vol. 7, Nos. 1–3 (2011) 1–336
c(cid:1) 2012 S. P. Vadhan
DOI: 10.1561/0400000010

Pseudorandomness

By Salil P. Vadhan

Contents

1 Introduction

1.1 Overview of this Survey
1.2 Background Required and Teaching Tips
1.3 Notational Conventions
1.4 Chapter Notes and References

2 The Power of Randomness

2.1 Polynomial Identity Testing
2.2 The Computational Model and Complexity Classes
2.3 Sampling and Approximation Problems
2.4 Random Walks and S-T Connectivity
2.5 Exercises
2.6 Chapter Notes and References

3 Basic Derandomization Techniques

3.1 Enumeration
3.2 Nonconstructive/Nonuniform Derandomization
3.3 Nondeterminism
3.4 The Method of Conditional Expectations
3.5 Pairwise Independence
3.6 Exercises
3.7 Chapter Notes and References

2

2
7
8
8

10

10
17
23
32
40
46

50

51
52
56
58
62
73
77



<!-- pdf-page: 2 -->
4 Expander Graphs

4.1 Measures of Expansion
4.2 Random Walks on Expanders
4.3 Explicit Constructions
4.4 Undirected S-T Connectivity in Deterministic Logspace
4.5 Exercises
4.6 Chapter Notes and References

5 List-Decodable Codes

5.1 Deﬁnitions and Existence
5.2 List-Decoding Algorithms
5.3 List-decoding Views of Samplers and Expanders
5.4 Expanders from Parvaresh–Vardy Codes
5.5 Exercises
5.6 Chapter Notes and References

6 Randomness Extractors

6.1 Motivation and Deﬁnition
6.2 Connections to Other Pseudorandom Objects
6.3 Constructing Extractors
6.4 Exercises
6.5 Chapter Notes and References

7 Pseudorandom Generators

7.1 Motivation and Deﬁnition
7.2 Cryptographic PRGs
7.3 Hybrid Arguments
7.4 Pseudorandom Generators from Average-Case Hardness
7.5 Worst-Case/Average-Case Reductions and

Locally Decodable Codes

7.6 Local List Decoding and PRGs from

Worst-Case Hardness

7.7 Connections to Other Pseudorandom Objects

80

80
92
102
116
121
127

131

131
141
151
155
159
163

166

167
178
188
202
209

212

212
219
224
230

239

252
261



<!-- pdf-page: 3 -->
7.8 Exercises
7.9 Chapter Notes and References

8 Conclusions

8.1 A Uniﬁed Theory of Pseudorandomness
8.2 Other Topics in Pseudorandomness

Acknowledgments

References

270
278

284

284
290

309

311



<!-- pdf-page: 4 -->
Foundations and Trends R(cid:1) in
Theoretical Computer Science
Vol. 7, Nos. 1–3 (2011) 1–336
c(cid:1) 2012 S. P. Vadhan
DOI: 10.1561/0400000010

Pseudorandomness

Salil P. Vadhan

School of Engineering and Applied Sciences, Harvard University, Cambridge,
MA, 02138, USA, salil@seas.harvard.edu

Abstract

This is a survey of pseudorandomness, the theory of eﬃciently generat-
ing objects that “look random” despite being constructed using little
or no randomness. This theory has signiﬁcance for a number of areas
in computer science and mathematics, including computational com-
plexity, algorithms, cryptography, combinatorics, communications, and
additive number theory. Our treatment places particular emphasis on
the intimate connections that have been discovered between a variety
of fundamental “pseudorandom objects” that at ﬁrst seem very diﬀer-
ent in nature: expander graphs, randomness extractors, list-decodable
error-correcting codes, samplers, and pseudorandom generators. The
structure of the presentation is meant to be suitable for teaching in a
graduate-level course, with exercises accompanying each section.



<!-- pdf-page: 5 -->
1

Introduction

1.1 Overview of this Survey

Over the past few decades, randomization has become one of the most
pervasive paradigms in computer science. Its widespread uses include:

Algorithm Design: For a number of important algorithmic prob-
lems, the most eﬃcient algorithms known are randomized. For example:

• Primality Testing: This was shown to have a randomized
polynomial-time algorithm in 1977. It wasn’t until 2002 that
a deterministic polynomial-time algorithm was discovered.
(We will see this algorithm, but not its proof.)

• Approximate Counting: Many approximate counting prob-
lems (e.g., counting perfect matchings in a bipartite graph)
have randomized polynomial-time algorithms, but the fastest
known deterministic algorithms take exponential time.

• Undirected S-T Connectivity: This was shown to have
a randomized logspace algorithm in 1979. It wasn’t until
2005 that a deterministic logspace algorithm was discovered
— using tools from the theory of pseudorandomness, as we
will see.

2



<!-- pdf-page: 6 -->
1.1 Overview of this Survey

3

• Perfect Matching: This was shown to have a randomized
polylogarithmic-time parallel algorithm in the late 1970s.
Deterministically, we only know polynomial-time algorithms.

Even in the cases where deterministic algorithms of comparable com-
plexity were eventually found, the randomized algorithms remain con-
siderably simpler and more eﬃcient than the deterministic ones.

Cryptography: Randomization is central to cryptography. Indeed,
cryptography is concerned with protecting secrets, and how can some-
thing be secret if it is deterministically ﬁxed? For example, we assume
that cryptographic keys are chosen at random (e.g., uniformly from
the set of n-bit strings). In addition to the keys, it is known that often
the cryptographic algorithms themselves (e.g., for encryption) must be
randomized to achieve satisfactory notions of security (e.g., that no
partial information about the message is leaked).

Combinatorial Constructions: Randomness is often used to prove
the existence of combinatorial objects with a desired property. Speciﬁ-
cally, if one can show that a randomly chosen object has the property
with nonzero probability, then it follows that such an object must, in
fact, exist. A famous example due to Erd˝os is the existence of Ramsey
graphs: A randomly chosen n-vertex graph has no clique or indepen-
dent set of size 2 log n with high probability. We will see several other
applications of this “Probabilistic Method” in this survey, such as with
two important objects mentioned below: expander graphs and error-
correcting codes.

Though these applications of randomness are interesting and rich
topics of study in their own right, they are not the focus of this survey.
Rather, we ask the following:

Main Question: Can we reduce or even eliminate the use of ran-
domness in these settings?

We have several motivations for doing this.

• Complexity Theory: We are interested in understanding and
comparing the power of various kinds of computational
resources. Since randomness is such a widely used resource,



<!-- pdf-page: 7 -->
4

Introduction

we want to know how it relates to other resources such as
time, space, and parallelism. In particular, we ask: Can every
randomized algorithm be derandomized with only a small loss
in eﬃciency?

• Using Physical Random Sources: It is unclear whether the
real world has physical sources of perfect randomness. We
may use sources that seem to have some unpredictability,
like the low order bits of a system clock or thermal noise,
but these sources will generally have biases and, more prob-
lematically, correlations. Thus we ask: What can we do with
a source of biased and correlated bits?

• Explicit Constructions: Probabilistic constructions of combi-
natorial objects often do not provide us with eﬃcient algo-
rithms for using those objects. Indeed, the randomly chosen
object often has a description that is exponential in the rele-
vant parameters. Thus, we look for explicit constructions —
ones that are deterministic and eﬃcient. In addition to their
applications, improvements in explicit constructions serve as
a measure of our progress in understanding the objects at
hand. Indeed, Erd˝os posed the explicit construction of near-
optimal Ramsey graphs as an open problem, and substantial
progress on this problem was recently made using the theory
of pseudorandomness (namely randomness extractors).

• Unexpected Applications: In addition, the theory of pseudo-
randomness has turned out to have many applications to
problems that seem to have no connection to derandomiza-
tion. These include data structures, distributed computation,
circuit lower bounds and completeness results in complexity
theory, reducing interaction in interactive protocols, sav-
ing memory in streaming algorithms, and more. We will
see some of these applications in this survey (especially the
exercises).

The paradigm we will use to study the Main Question is that of
pseudorandomness: eﬃciently generating objects that “look random”
using little or no randomness.



<!-- pdf-page: 8 -->
1.1 Overview of this Survey

5

Speciﬁcally, we will study four “pseudorandom” objects:

Pseudorandom Generators: A pseudorandom generator is an
algorithm that takes as input a short, perfectly random seed and then
returns a (much longer) sequence of bits that “looks random.” That
the bits output cannot be perfectly random is clear — the output is
determined by the seed and there are far fewer seeds than possible bit
sequences. Nevertheless, it is possible for the output to “look random”
in a very meaningful and general-purpose sense. Speciﬁcally, we will
require that no eﬃcient algorithm can distinguish the output from a
truly random sequence. The study of pseudorandom generators meet-
ing this strong requirement originated in cryptography, where they have
numerous applications. In this survey, we will emphasize their role in
derandomizing algorithms.

Note that asserting that a function is a pseudorandom generator is
a statement about something that eﬃcient algorithms can’t do (in this
case, distinguish two sequences). But proving that eﬃcient algorithms
cannot compute things is typically out of reach for current techniques
in theoretical computer science; indeed this is why the P vs. NP ques-
tion is so hard. Thus, we will settle for conditional statements. An
ideal theorem would be something like: “If P (cid:1)= NP, then pseudoran-
dom generators exist.” (The assumptions we make won’t exactly be
P (cid:1)= NP, but hypotheses of a similar ﬂavor.)

Randomness Extractors: A randomness extractor takes as input
a source of biased and correlated bits, and then produces a sequence of
almost-uniform bits as output. Their original motivation was the simu-
lation of randomized algorithms with sources of biased and correlated
bits, but they have found numerous other applications in theoretical
computer science. Ideally, extractors would be deterministic, but as we
will see this proves to be impossible for general sources of biased and
correlated bits. Nevertheless, we will get close — constructing extrac-
tors that are only “mildly” probabilistic, in that they use small (loga-
rithmic) number of truly random bits as a seed for the extraction.

Expander Graphs: Expanders are graphs with two seemingly
contradictory properties: they are sparse (e.g., having degree that is



<!-- pdf-page: 9 -->
6

Introduction

a constant, independent of the number of vertices), but also “well-
connected” in some precise sense. For example, the graph cannot be
bisected without cutting a large (say, constant) fraction of the edges.
Expander graphs have numerous applications in theoretical com-
puter science. They were originally studied for their use in designing
fault-tolerant networks (e.g., for telephone lines), ones that maintain
good connectivity even when links or nodes fail. But they also have less
obvious applications, such as an O(log n)-time algorithm for sorting in
parallel.

It is not obvious that expander graphs exist, but in fact it can be
shown, via the Probabilistic Method, that a random graph of degree 3 is
a “good” expander with high probability. However, many applications
of expander graphs need explicit constructions, and these have taken
longer to ﬁnd. We will see some explicit constructions in this survey, but
even the state-of-the-art does not always match the bounds given by
the probabilistic method (in terms of the degree/expansion tradeoﬀ).

Error-Correcting Codes: Error-correcting codes are tools for com-
municating over noisy channels. Speciﬁcally, they specify a way to
encode messages into longer, redundant codewords so that even if the
codeword gets somewhat corrupted along the way, it is still possible
for the receiver to decode the original message. In his landmark paper
that introduced the ﬁeld of coding theory, Shannon also proved the
existence of good error-correcting codes via the Probabilistic Method.
That is, a random mapping of n-bit messages to O(n)-bit codewords
is a “good” error-correcting code with high probability. Unfortunately,
these probabilistic codes are not feasible to actually use — a random
mapping requires an exponentially long description, and we know of no
way to decode such a mapping eﬃciently. Again, explicit constructions
are needed.

In this survey, we will focus on the problem of list decoding. Specif-
ically, we will consider scenarios where the number of corruptions is
so large that unique decoding is impossible; at best one can produce a
short list that is guaranteed to contain the correct message.

A Uniﬁed Theory: Each of the above objects has been the center of
a large and beautiful body of research, but until recently these corpora



<!-- pdf-page: 10 -->
1.2 Background Required and Teaching Tips

7

were largely distinct. An exciting development over the past decade has
been the realization that all four of these objects are almost the same
when interpreted appropriately. Their intimate connections will be a
major focus of this survey, tying together the variety of constructions
and applications that we will see.

The surprise and beauty of these connections has to do with
the seemingly diﬀerent nature of each of these objects. Pseudoran-
dom generators, by asserting what eﬃcient algorithms cannot do, are
objects of complexity theory. Extractors, with their focus on extract-
ing the entropy in a correlated and biased sequence, are information-
theoretic objects. Expander graphs are of course combinatorial objects
(as deﬁned above), though they can also be interpreted algebraically,
as we will see. Error-correcting codes involve a mix of combinatorics,
information theory, and algebra. Because of the connections, we obtain
new perspectives on each of the objects, and make substantial advances
on our understanding of each by translating intuitions and techniques
from the study of the others.

1.2 Background Required and Teaching Tips

The presentation assumes a good undergraduate background in the
theory of computation, and general mathematical maturity. Speciﬁ-
cally, it is assumed that the reader is familiar with basic algorithms
and discrete mathematics as covered in [109], including some exposure
to randomized algorithms; and with basic computational complexity
including P, NP, and reductions, as covered in [366]. Experience with
elementary abstract algebra, particularly ﬁnite ﬁelds, is helpful; recom-
mended texts are [36, 263].

Most of the material in the survey is covered in a one-semester
graduate course that the author teaches at Harvard University, which
consists of 24 lectures of 1.5 hours each. Most of the students in that
course take at least one graduate-level course in theoretical computer
science before this one.

The exercises are an important part of the survey, as they include
proofs of some key facts, introduce some concepts that will be used in
later sections, and illustrate applications of the material to other topics.



<!-- pdf-page: 11 -->
8

Introduction

Problems that are particularly challenging or require more creativity
than most are marked with a star.

1.3 Notational Conventions

We denote the set of numbers {1, . . . , n} by [n]. We write N for the set
of nonnegative integers (so we consider 0 to be a natural number). We
write S ⊂ T to mean that S is a subset of T (not necessarily strict),
and S (cid:1) T for S being a strict subset of T . An inequality we use often
≤ (ne/k)k. All logarithms are base 2 unless otherwise speciﬁed.
is
We often use the convention that lowercase letters are the logarithm
(base 2) of the corresponding capital letter (e.g., N = 2n).

(cid:2)
n
k

(cid:1)

Throughout, we consider random variables that can take values in
arbitrary discrete sets (as well as real-valued random variables). We
generally use capital letters, e.g., X, to denote random variables and
lowercase letters, e.g., x, to denote speciﬁc values. We write x R← X
to indicate that x is sampled according to X. For a set S, we write
x R← S to mean that x is selected uniformly at random from S. We
use the convention that multiple occurrences of a random variable in
an expression refer to the same instantiation, e.g., Pr[X = X] = 1. The
support of a random variable X is denoted by Supp(X) def= {x : Pr[X =
x] > 0}. For an event E, we write X|E to denote the random variable
X conditioned on the event E. For a set S, we write US to denote
a random variable distributed uniformly over S. For n ∈ N, Un is a
random variable distributed uniformly over {0, 1}n.

1.4 Chapter Notes and References

In this section, we only provide pointers to general surveys and
textbooks on the topics covered, plus citations for speciﬁc results
mentioned.

General introductions to the theory of pseudorandomness (other

than this survey) include [162, 288, 393].

Recommended textbooks focused on randomized algorithms are
[290, 291]. The speciﬁc randomized and deterministic algorithms



<!-- pdf-page: 12 -->
1.4 Chapter Notes and References

9

mentioned are due to [6, 13, 220, 236, 237, 267, 287, 314, 327, 369];
for more details see Section 2.6.

Recommended textbooks on cryptography are [157, 158, 238]. The
idea that encryption should be randomized is due to Goldwasser and
Micali [176].

The Probabilistic Method for combinatorial constructions is the
subject of the book [25]. Erd˝os used this method to prove the existence
of Ramsey graphs in [132]. Major recent progress on explicit construc-
tions of Ramsey graphs was recently obtained by Barak, Rao, Shaltiel,
and Widgerson [48] via the theory of randomness extractors.

The modern notion of a pseudorandom generator was formulated in
the works of Blum and Micali [72] and Yao [421], motivated by cryp-
tographic applications. We will spend most of our time on a variant of
the Blum–Micali–Yao notion, proposed by Nisan and Wigderson [302],
where the generator is allowed more running time than the algorithms
it fools. A detailed treatment of the Blum–Micali–Yao notion can be
found in [157].

Surveys on randomness extractors are [301, 352, 354]. The notion
focus on is the one due to Nisan and

of extractor that we will
Zuckerman [303].

A detailed survey of expander graphs is [207]. The probabilistic
construction of expander graphs is due to Pinsker [309]. The applica-
tion of expanders to sorting in parallel is due to Ajtai, Koml´os, and
Szemer´edi [10].

A classic text on coding theory is [282]. For a modern, computer
science-oriented treatment, we recommend Sudan’s lecture notes [380].
Shannon started this ﬁeld with the paper [361]. The notion of list decod-
ing was proposed by Elias [129] and Wozencraft [420], and was reinvig-
orated in the work of Sudan [378]. Recent progress on list decoding is
covered in [184].



<!-- pdf-page: 13 -->
2

The Power of Randomness

Before we study the derandomization of randomized algorithms, we will
need some algorithms to derandomize. Thus in this section, we present
a number of examples of randomized algorithms, as well as develop the
complexity-theoretic framework and basic tools for studying random-
ized algorithms.

2.1 Polynomial Identity Testing

In this section, we give a randomized algorithm to solve the following
computational problem.

Computational Problem 2.1. Polynomial Identity Testing:
Given two multivariate polynomials, f (x1, . . . , xn) and h(x1, . . . , xn),
decide whether f = g.

10



<!-- pdf-page: 14 -->
2.1 Polynomial Identity Testing

11

This problem statement requires some clariﬁcation. Speciﬁcally, we

need to say what we mean by:

• “polynomials”: A (multivariate) polynomial is a ﬁnite expres-

sion of the form

f (x1, . . . , xn) =

(cid:3)

i1,...,in∈N

ci1,...,inxi1

1 xi2

2

· · · xin
n .

We need to specify from what space the coeﬃcients of the
polynomials come; they could be the integers, reals, ratio-
nals, etc. In general, we will assume that the coeﬃcients are
chosen from a ﬁeld (a set with addition and multiplication,
where every nonzero element has a multiplicative inverse) or
more generally an (integral) domain (where the product of
two nonzero elements is always nonzero). Examples of ﬁelds
include Q (the rationals), R (the reals), and Zp (integers
modulo p) where p is prime. An integral domain that is not
a ﬁeld is Z (the integers), but every integral domain is con-
tained in its ﬁeld of fractions, which is Q in the case of Z. Zn
for composite n is not even an integral domain. We remark
that there does exist a ﬁnite ﬁeld Fq of size q = pk for every
prime p and positive integer k, and in fact this ﬁeld is unique
(up to isomorphism). Note that Fq is only equal to Zq in case
q is prime (i.e., k = 1). For more background on algebra, see
the references in the chapter notes.
(cid:4)
· · · xin
For a polynomial f (x1, . . . , xn) =
n ,
we deﬁne its degree (a.k.a. total degree) to be the maximum
sum of the exponents i1 + · · · + in over its monomials with
nonzero coeﬃcients ci1,...,in. Its degree in xj is the maximum
of ij over its monomials with nonzero coeﬃcients.

i1,...,in ci1,...,inxi1

1 xi2

2

• “f = g”: What does it mean for two polynomials to be equal?
There are two natural choices: the polynomials are the same
as functions (they have the same output for every point in
the domain), or the polynomials are the same as formal poly-
nomials (the coeﬃcients for each monomial are the same).
These two deﬁnitions are equivalent over the integers, but
they are not equivalent over ﬁnite ﬁelds. For example,



<!-- pdf-page: 15 -->
12 The Power of Randomness

consider

f (x) =

(cid:5)

α∈F

(x − α).

for a ﬁnite ﬁeld F.1 It is easy to see that f (α) = 0 for all α ∈ F,
but f (cid:1)= 0 as a formal polynomial. For us, equality refers
to equality as formal polynomials unless otherwise speciﬁed
(but often we’ll be working with domains that are larger than
the degrees of the polynomials, in which case the two deﬁ-
nitions are equivalent, as follows from the Schwartz–Zippel
Lemma below).

• “given”: What does it mean to be given a polynomial? There

are several possibilities here:

(1) As a list of coeﬃcients: this trivializes the problem
of Polynomial Identity Testing, as we can just
compare. Since we measure complexity as a function
of the input length, this algorithm runs in linear time.

(2) As an “oracle”: a black box that, given any point in
the domain, gives the value of the polynomial. Here
the only “explicit” inputs to the algorithm are the
description of the ﬁeld F, the number n of variables,
and a bound d on the degree of the polynomial, and
we consider an algorithm to be eﬃcient if it runs in
time polynomial in the lengths of these inputs and
n log |F| (since it takes time at least n log |F| to write
down an input to the oracle).

(3) As an arithmetic formula: a sequence of
symbols like (x1 + x2)(x3 + x7 + 6x5)x3(x5 − x6) +
x2x4(2x3 + 3x5)
the polynomial.
that describes
Observe that while we can solve Polynomial Iden-
tity Testing by expanding the polynomials and
grouping terms, the expanded polynomials may have
length exponential in the length of the formula, and

1 When expanded and terms are collected, this polynomial p can be shown to simply equal
x|F| − x.



<!-- pdf-page: 16 -->
2.1 Polynomial Identity Testing

13

thus the algorithm is not eﬃcient as a function of the
input length.
More general than formulas are circuits. An arith-
metic circuit consists of a directed acyclic graph,
input nodes, which have indegree 0
consisting of
and are labeled by input variables or constants, and
computation nodes, which have indegree 2 and are
labelled by operations (+ or ×) specifying how to
compute a value given the values at its children; one
of the computation nodes is designated as the output
node. Observe that every arithmetic circuit deﬁnes
a polynomial in its input variables x1, . . . , xn. Arith-
metic formulas are equivalent to arithmetic circuits
where the underlying graph is a tree.

The randomized algorithm we describe will work for all of the for-
mulations above, but is only interesting for the second and third ones
(oracles and arithmetic circuits/formulas). It will be convenient to work
with the following equivalent version of the problem.

Computational Problem 2.2. Polynomial Identity Testing
(reformulation): Given a polynomial f (x1, . . . , xn), is f = 0?

That is, we consider the special case of the original problem where
g = 0. Any solution for the general version of course implies one for the
special case; conversely, we can solve the general version by applying
the special case to the polynomial f (cid:3) = f − g.

Algorithm 2.3 (Polynomial Identity Testing).
Input: A multivariate polynomial f (x1, . . . , xn) of degree at most d
over a ﬁeld/domain F.

(1) Let S ⊂ F be any set of size 2d.
(2) Choose α1, . . . , αn
(3) Evaluate f (α1, . . . , αn). If the result is 0, accept. Otherwise,

R← S.

reject.



<!-- pdf-page: 17 -->
14 The Power of Randomness

It is clear that if f = 0, the algorithm will always accept. The cor-
rectness in case f (cid:1)= 0 is based on the following simple but very useful
lemma.

Lemma 2.4 (Schwartz–Zippel Lemma). If f is a nonzero polyno-
mial of degree d over a ﬁeld (or integral domain) F and S ⊂ F, then

Pr
α1,...,αn

R←S

[f (α1, . . . , αn) = 0] ≤ d
|S| .

In the univariate case (n = 1), this amounts to the familiar fact
that a polynomial with coeﬃcients in a ﬁeld and degree d has at most
d roots. The proof for multivariate polynomials proceeds by induction
on n, and we leave it as an exercise (Problem 2.1).

By the Schwartz–Zippel lemma, the algorithm will err with proba-
bility at most 1/2 when f (cid:1)= 0. This error probability can be reduced
by repeating the algorithm many times (or by increasing |S|). Note
that the error probability is only over the coin tosses of the algorithm,
not over the input polynomial f . This is what we mean when we say
randomized algorithm; it should work on a worst-case input with high
probability over the coin tosses of the algorithm. In contrast, algorithms
whose correctness (or eﬃciency) only holds for inputs that are randomly
chosen (according to a particular distribution) are called heuristics, and
their study is called average-case analysis.

Note that we need a few things to ensure that our algorithm will

work.

• First, we need a bound on the degree of the polynomial. We
can get this in diﬀerent ways depending on how the polyno-
mial is represented. For example, for arithmetic formulas, the
degree is bounded by the length of the formula. For arith-
metic circuits, the degree is at most exponential in the size
(or even depth) of the circuit.

• We also must be able to evaluate f when the variables take
arbitrary values in some set S of size 2d. For starters, this
requires that the domain F is of size at least 2d. We should



<!-- pdf-page: 18 -->
2.1 Polynomial Identity Testing

15

also have an explicit description of the domain F enabling us
to write down and manipulate ﬁeld elements, and randomly
sample from a subset of size at least 2d (e.g., the description
of F = Zp is simply the prime p). Then, if we are given f as
an oracle, we have the ability to evaluate f by deﬁnition. If
we are given f as an arithmetic formula or circuit, then we
can do a bottom-up, gate-by-gate evaluation. However, over
inﬁnite domains (like Z), there is subtlety — the bit-length
of the numbers can grow exponentially large. Problem 2.4
gives a method for coping with this.

Since these two conditions are satisﬁed, we have a polynomial-
time randomized algorithm for Polynomial Identity Testing for
polynomials given as arithmetic formulas over Z (or even circuits, by
Problem 2.4). There are no known subexponential-time deterministic
algorithms for this problem, even for formulas in ΣΠΣ form (i.e., a
sum of terms, each of which is the product of linear functions in the
input variables). A deterministic polynomial-time algorithm for ΣΠΣ
formulas where the outermost sum has only a constant number of terms
was obtained quite recently (2005).

2.1.1 Application to Perfect Matching

Now we will see an application of Polynomial Identity Testing to
an important graph-theoretic problem.

Deﬁnition 2.5. Let G = (V, E) be a graph. A matching on G is a
set E(cid:3) ⊂ E such that no two edges in E(cid:3) have a common endpoint. A
perfect matching is a matching such that every vertex is incident to an
edge in the matching.

Computational Problem 2.6. Perfect Matching: Given a graph
G, decide whether there is a perfect matching in G.

Unlike Polynomial Identity Testing, Perfect Matching is
known to have deterministic polynomial-time algorithms — e.g., using



<!-- pdf-page: 19 -->
16 The Power of Randomness

alternating paths, or by reduction to Max Flow in the bipartite case.
However, both of these algorithms seem to be inherently sequential
in nature. With randomization, we can obtain an eﬃcient parallel
algorithm.

Algorithm 2.7 (Perfect Matching in bipartite graphs).
Input: A bipartite graph G with vertices numbered 1, . . . , n on each
side and edges E ⊆ [n] × [n].2

We construct an n × n matrix A where

(cid:6)

xi,j
0

if(i, j) ∈ E
otherwise

,

Ai,j(x) =

where xi,j is a formal variable.

Consider the multivariate polynomial

det(A(x)) =

σ∈Sn

(cid:3)

sign(σ) ·

(cid:5)

i

Ai,σ(i),

where Sn denotes the set of permutations on [n]. Note that the σth term
is nonzero if and only if the permutation σ deﬁnes a perfect matching.
That is, (i, σ(i)) ∈ E for all 1 ≤ i ≤ n. So det(A(x)) = 0 iﬀ G has no
perfect matching. Moreover its degree is bounded by n, and given values
αi,j for the xi,js we can evaluate det(A(α)) eﬃciently in parallel in poly-
logarithmic time using an appropriate algorithm for the determinant.
just
So to test for a perfect matching eﬃciently in parallel,
run the Polynomial Identity Testing algorithm with, say, S =
{1, . . . , 2n} ⊂Z, to test whether det(A(x )) = 0.

Some remarks:

• The above also provides

the most eﬃcient sequential
algorithm for Perfect Matching, using the fact that
Determinant has the same time complexity as Matrix
Multiplication, which is known to be at most O(n2.38).
• More sophisticated versions of the algorithm apply to nonbi-
partite graphs, and enable ﬁnding perfect matchings in the

2 Recall that [n] denotes the set {1, . . . , n}. See Section 1.3.



<!-- pdf-page: 20 -->
2.2 The Computational Model and Complexity Classes

17

same parallel or sequential time complexity (where the result
for sequential time is quite recent).

• Polynomial Identity Testing has been also used to
obtain a randomized algorithm for Primality Testing,
which was derandomized fairly recently (2002) to obtain the
celebrated deterministic polynomial-time algorithm for Pri-
mality Testing. See Problem 2.5.

2.2 The Computational Model and Complexity Classes

2.2.1 Models of Randomized Computation

To develop a rigorous theory of randomized algorithms, we need to
use a precise model of computation. There are several possible ways to
augmenting a standard deterministic computational model (e.g., Turing
machine or RAM model), such as:

(1) The algorithm has access to a “coin-tossing black box” that
provides it with (unbiased and independent) random bits on
request, with each request taking one time step. This is the
model we will use.

(2) The algorithm has access to a black box that, given a num-
ber n in binary, returns a number chosen uniformly at ran-
dom from {1, . . . , n}. This model is often more convenient for
describing algorithms. Problem 2.2 shows that it is equiva-
lent to Model 1, in the sense that any problem that can be
solved in polynomial time on one model can also be solved
in polynomial time on the other.

(3) The algorithm is provided with an inﬁnite tape (i.e., sequence
of memory locations) that is initially ﬁlled with random
bits. For polynomial-time algorithms, this is equivalent to
Model 1. However, for space-bounded algorithms, this model
seems stronger, as it provides the algorithm with free stor-
age of its random bits (i.e., not counted toward its working
memory). Model 1 is considered to be the “right” model for
space-bounded algorithms. It is equivalent to allowing the
algorithm one-way access to an inﬁnite tape of random bits.



<!-- pdf-page: 21 -->
18 The Power of Randomness

We interchangeably use “random bits” and “random coins” to refer

to an algorithm’s random choices.

2.2.2 Complexity Classes

We will now deﬁne complexity classes that capture the power of eﬃcient
randomized algorithms. As is common in complexity theory, these
classes are deﬁned in terms of decision problems, where the set of inputs
where the answer should be “yes” is speciﬁed by a language L ⊂ {0, 1}∗.
However, the deﬁnitions generalize in natural ways to other types of
computational problems, such as computing functions or solving search
problems.

Recall that we say a deterministic algorithm A runs in time
t : N → N if A takes at most t(|x|) steps on every input x, and it runs in
polynomial time if it runs time t(n) =O (nc) for a constant c. Polyno-
mial time is a theoretical approximation to feasible computation, with
the advantage that it is robust to reasonable changes in the model of
computation and representation of the inputs.

Deﬁnition 2.8. P is the class of languages L for which there exists a
deterministic polynomial-time algorithm A such that

• x ∈ L ⇒ A(x) accepts.
• x /∈ L ⇒ A(x) rejects.

For a randomized algorithm A, we say that A runs in time t : N → N
if A takes at most t(|x|) steps on every input x and every sequence of
random bits.

Deﬁnition 2.9. RP is the class of languages L for which there exists
a probabilistic polynomial-time algorithm A such that

• x ∈ L ⇒ Pr[A(x) accepts] ≥ 1/2.
• x (cid:1)∈ L ⇒ Pr[A(x) accepts] = 0.

Here (and in the deﬁnitions below) the probabilities are taken over the
coin tosses of the algorithm A.



<!-- pdf-page: 22 -->
2.2 The Computational Model and Complexity Classes

19

That is, RP algorithms may have false negatives; the algorithm may
sometimes say “no” even if the answer is “yes,” albeit with bounded
probability. But the deﬁnition does not allow for false positives. Thus
RP captures eﬃcient randomized computation with one-sided error.
RP stands for “randomized polynomial time.” Note that the error
probability of an RP algorithm can be reduced to 2−p(n) for any polyno-
mial p by running the algorithm p(n) times independently and accept-
ing the input iﬀ at least one of the trials accepts. By the same reasoning,
the 1/2 in the deﬁnition is arbitrary, and any constant α ∈ (0, 1) or even
α = 1/poly(n) would yield the same class of languages.

A central question in this survey is whether randomization enables
us to solve more problems (e.g., decide more languages) in polynomial
time:

Open Problem 2.10. Does P = RP?

Similarly, we can consider algorithms that may have false positives

but no false negatives.

Deﬁnition 2.11. co-RP is the class of languages L whose complement
¯L is in RP. Equivalently, L ∈ co-RP if there exists a probabilistic
polynomial-time algorithm A such that
• x ∈ L ⇒ Pr[A(x) accepts] = 1.
• x (cid:1)∈ L ⇒ Pr[A(x) accepts] ≤ 1/2.

So, in co-RP we may err on “no” instances, whereas in RP we may

err on “yes” instances.

Using the Polynomial Identity Testing algorithm we saw ear-
lier, we can deduce that Polynomial Identity Testing for arith-
metic formulas is in co-RP. In Problem 2.4, this is generalized to arith-
metic circuits, and thus we have:

Theorem 2.12. Arithmetic Circuit Identity Testing over Z,
deﬁned as the language
ACITZ = {C : C(x1, . . . , xn) an arithmetic circuit over Z s.t. C = 0},
is in co-RP.



<!-- pdf-page: 23 -->
20 The Power of Randomness

It is common to also allow two-sided error in randomized algorithms:

Deﬁnition 2.13. BPP is the class of languages L for which there
exists a probabilistic polynomial-time algorithm A such that

• x ∈ L ⇒ Pr[A(x) accepts] ≥ 2/3.
• x (cid:1)∈ L ⇒ Pr[A(x) accepts] ≤ 1/3.

Just as with RP, the error probability of BPP algorithms can be
reduced from 1/3 (or even 1/2 − 1/poly(n)) to exponentially small by
repetitions, this time taking a majority vote of the outcomes. Proving
this uses some facts from probability theory, which we will review in
the next section.

The cumbersome notation BPP stands for “bounded-error proba-
bilistic polynomial-time,” due to the unfortunate fact that PP (“prob-
abilistic polynomial-time”) refers to the deﬁnition where the inputs in
L are accepted with probability greater than 1/2 and inputs not in L
are accepted with probability at most 1/2. Despite its name, PP is
not a reasonable model for randomized algorithms, as it takes expo-
nentially many repetitions to reduce the error probability. BPP is
considered the standard complexity class associated with probabilis-
tic polynomial-time algorithms, and thus the main question of this
survey is:

Open Problem 2.14. Does BPP = P?

So far, we have considered randomized algorithms that can out-
put an incorrect answer if they are unlucky in their coin tosses; these
are called “Monte Carlo” algorithms. It is sometimes preferable to
have “Las Vegas” algorithms, which always output the correct answer,
but may run for a longer time if they are unlucky in their coin
tosses. For this, we say that A has expected running time t : N → N
if for every input x, the expectation of the number of steps taken by
A(x) is at most t(|x|), where the expectation is taken over the coin
tosses of A.



<!-- pdf-page: 24 -->
2.2 The Computational Model and Complexity Classes

21

Deﬁnition 2.15. ZPP is the class of languages L for which there
exists a probabilistic algorithm A that always decides L correctly and
runs in expected polynomial time.

ZPP stands for “zero-error probabilistic polynomial time.” The fol-

lowing relation between ZPP and RP is left as an exercise.

Fact 2.16 (Problem 2.3). ZPP = RP ∩ co-RP.

We do not know any other relations between the classes associated

with probabilistic polynomial time.

Open Problem 2.17. Are any of the inclusions P ⊂ ZPP ⊂ RP ⊂
BPP proper?

One can similarly deﬁne randomized complexity classes associated
with complexity measures other than time such as space or parallel
computation. For example:

Deﬁnition 2.18. RNC is the class of languages L for which there
exists a probabilistic parallel algorithm A that runs in polylogarithmic
time on polynomially many processors and such that

• x ∈ L ⇒ Pr[A(x) accepts] ≥ 1/2.
• x (cid:1)∈ L ⇒ Pr[A(x) accepts] = 0.

A formal model of a parallel algorithm is beyond the scope of this
survey, but can be found in standard texts on algorithms or parallel
computation. We have seen:

Theorem 2.19. Perfect Matching in bipartite graphs, i.e., the
language PM = {G : G a bipartite graph with a perfect matching}, is
in RNC.

Complexity classes associated with space-bounded computation will

be discussed in Section 2.4.1.



<!-- pdf-page: 25 -->
22 The Power of Randomness

2.2.3 Tail Inequalities and Error Reduction

In the previous section, we claimed that we can reduce the error of a
BPP algorithm by taking independent repetitions and ruling by major-
ity vote. The intuition that this should work is based on the Law of
Large Numbers: if we repeat the algorithm many times, the fraction
of correct answers should approach its expectation, which is greater
than 1/2 (and thus majority rule will be correct). For complexity pur-
poses, we need quantitative forms of this fact, which bound how many
repetitions are needed to achieve a desired probability of correctness.
First, we recall a basic inequality which says that it is unlikely for
(a single instantiation of) a random variable to exceed its expectation
by a large factor.

Lemma 2.20 (Markov’s Inequality). If X is a nonnegative real-
valued random variable, then for any α > 0,
Pr[X ≥ α] ≤ E[X]
α

.

Markov’s Inequality alone does not give very tight concentration
around the expectation; to get even a 50% probability, we need to look
at deviations by a factor of 2. To get tight concentration, we can take
many independent copies of a random variable. There are a variety of
diﬀerent tail inequalities that apply for this setting; they are collectively
referred to as Chernoﬀ Bounds.

Theorem 2.21(A Chernoﬀ Bound). Let X1, . . . , Xt be independent
random variables taking values in the interval [0, 1], let X = (
i Xi)/t,
and µ = E[X]. Then

(cid:4)

Pr[|X − µ| ≥ε] ≤ 2 exp(−tε2/4).

Thus, the probability that the average deviates signiﬁcantly from
the expectation vanishes exponentially with the number of repetitions t.
We leave the proof of this Chernoﬀ Bound as an exercise (Problem 2.7).
Now let’s apply the Chernoﬀ Bound to analyze error-reduction for

BPP algorithms.



<!-- pdf-page: 26 -->
2.3 Sampling and Approximation Problems

23

Proposition 2.22. The following are equivalent:

(1) L ∈ BPP.
(2) For every polynomial p, L has a probabilistic polynomial-

time algorithm with two-sided error at most 2−p(n).

(3) There exists a polynomial q such that L has a probabilis-
tic polynomial-time algorithm with two-sided error at most
1/2 − 1/q(n).

Proof. Clearly, (2) ⇒ (1) ⇒ (3). Thus, we prove (3) ⇒ (2).

Given an algorithm A with error probability at most 1/2 − 1/q(n),
consider an algorithm A(cid:3) that on an input x of length n, runs A for
t(n) independent repetitions and rules according to the majority, where
t(n) is a polynomial to be determined later.

We now compute the error probability of A(cid:3) on an input x of
length n. Let Xi be an indicator random variable that is 1 iﬀ the ith
execution of A(x) outputs the correct answer, and let X = (
i Xi)/t
be the average of these indicators, where t = t(n). Note that A(cid:3)(x) is
correct when X > 1/2. By the error probability of A and linearity of
expectations, we have E[X] ≥ 1/2 + 1/q, where q = q(n). Thus, apply-
ing the Chernoﬀ Bound with ε = 1/q, we have:

(cid:4)

Pr[X ≤ 1/2] ≤ 2 · e−t/2q2

< 2−p(n),

for t(n) = 2p(n)q(n)2 and suﬃciently large n.

2.3 Sampling and Approximation Problems

2.3.1 Sampling

The power of randomization is well-known to statisticians. If we want
to estimate the mean of some quantity over a large population, we can
do so very eﬃciently by taking the average over a small random sample.
Formally, here is the computational problem we are interested in

solving.



<!-- pdf-page: 27 -->
24 The Power of Randomness

Computational Problem 2.23. Sampling (a.k.a.
[+ε]-Approx
Oracle Average): Given oracle access to a function f : {0, 1}m →
[0, 1], estimate µ(f ) def= E[f (Um)] to within an additive error of ε, where
Um is uniformly distributed in {0, 1}m (as in Section 1.3). That is, out-
put an answer in the interval [µ − ε, µ + ε].

And here is the algorithm:

Algorithm 2.24 ([+ε]-Approx Oracle Average).
Input: oracle access to a function f : {0, 1}m → [0, 1], and a desired
error probability δ ∈ (0, 1)

(1) Choose x1, . . . , xt
O(log(1/δ)/ε2).

R← {0, 1}m, for an appropriate choice of t =

(2) Query the oracle to obtain f (x1), . . . , f (xt).
(3) Output (

(cid:4)

i f (xi))/t.

The correctness of this algorithm follows from the Chernoﬀ Bound
(Theorem 2.21). Note that for constant ε and δ, the sample size t is
independent of the size of the population (2m), and we have running
time poly(m) even for ε = 1/poly(m) and δ = 2−poly(m).

For this problem, we can prove that no deterministic algorithm can

be nearly as eﬃcient.

Proposition 2.25.
[+(1/4)]-Approx Oracle Average must make at
queries to its oracle.

deterministic

Any

algorithm

solving
least 2m/2

Proof. Suppose we have a deterministic algorithm A that makes fewer
than 2m/2 queries. Let Q be the set of queries made by A when all
of its queries are answered by 0. (We need to specify how the queries
are answered to deﬁne Q, because A make its queries adaptively, with
future queries depending on how earlier queries were answered.)



<!-- pdf-page: 28 -->
2.3 Sampling and Approximation Problems

25

Now deﬁne two functions:

f0(x) = 0
(cid:6)

f1(x) =

∀ x
0 x ∈ Q
1 x /∈ Q

Then A gives the same answer on both f0 and f1 (since all the
oracle queries return 0 in both cases), but µ(f0) = 0 and µ(f1) > 1/2,
so the answer must have error greater than 1/4 for at least one of the
functions.

Thus, randomization provides an exponential savings for approxi-
mating the average of a function on a large domain. However, this does
not show that BPP (cid:1)= P. There are two reasons for this:

(1) [+ε]-Approx Oracle Average is not a decision problem,
and indeed it is not clear how to deﬁne languages that cap-
ture the complexity of approximation problems. However,
below we will see how a slightly more general notion of deci-
sion problem does allow us to capture approximation prob-
lems such as this one.

(2) More fundamentally, it does not involve the standard model
of input as used in the deﬁnitions of P and BPP. Rather
than the input being a string that is explicitly given to the
algorithm (where we measure complexity in terms of the
length of the string), the input is an exponential-sized oracle
to which the algorithm is given random access. Even though
this is not the classical notion of input, it is an interesting one
that has received a lot of attention in recent years, because
it allows for algorithms whose running time is sublinear (or
even polylogarithmic) in the actual size of the input (e.g., 2m
in the example here). As in the example here, typically such
algorithms require randomization and provide approximate
answers.

2.3.2 Promise Problems

Now we will try to ﬁnd a variant of the [+ε]-Approx Oracle Aver-
age problem that is closer to the P versus BPP question. First, to



<!-- pdf-page: 29 -->
26 The Power of Randomness

obtain the standard notion of input, we consider functions that are
presented in a concise form, as Boolean circuits C : {0, 1}m → {0, 1}
(analogous to the algebraic circuits deﬁned in Section 2.1, but now the
inputs take on Boolean values and the computation gates are ∧, ∨,
and ¬).

Next, we need a more general notion of decision problem than lan-

guages:

Deﬁnition 2.26. A promise problem Π consists of a pair (ΠY , ΠN ) of
disjoint sets of strings, where ΠY is the set of yes instances and ΠN is
the set of no instances. The corresponding computational problem is:
given a string that is “promised” to be in ΠY or ΠN , decide which is
the case.

All of the complexity classes we have seen have natural promise-
problem analogues, which we denote by prP, prRP, prBPP, etc. For
example:

Deﬁnition 2.27. prBPP is the class of promise problems Π for which
there exists a probabilistic polynomial-time algorithm A such that

• x ∈ ΠY ⇒ Pr[A(x) accepts] ≥ 2/3.
• x ∈ ΠN ⇒ Pr[A(x) accepts] ≤ 1/3.

Since every language L corresponds to the promise problem (L, L),
any fact that holds for every promise problem in some promise-class
also holds for every language in the corresponding language class. In
particular, if every prBPP algorithm can be derandomized, so can
every BPP algorithm:

Proposition 2.28. prBPP = prP ⇒ BPP = P.

Except where otherwise noted, all of the results in this survey about
language classes (like BPP) easily generalize to the corresponding
promise classes (like prBPP), but we state most of the results in terms
of the language classes for notational convenience.



<!-- pdf-page: 30 -->
2.3 Sampling and Approximation Problems

27

Now we consider the following promise problem.

Computational Problem 2.29. [+ε]-Approx Circuit Average is
the promise problem CAε, deﬁned as:

CAε

Y = {(C, p) :µ(C ) > p + ε}
N = {(C, p) :µ(C ) ≤ p}
Here ε can be a constant or a function of the input length n = |(C, p)|.

CAε

It turns out that this problem completely captures the power of

probabilistic polynomial-time algorithms.

Theorem 2.30. For every function ε such that 1/poly(n) ≤ ε(n) ≤ 1 −
1/2no(1)
, [+ε]-Approx Circuit Average is prBPP-complete. That is,
it is in prBPP and every promise problem in prBPP reduces to it.

Proof Sketch: Membership in prBPP follows from Algorithm 2.24
and the fact that boolean circuits can be evaluated in polynomial time.
For prBPP-hardness, consider any promise problem Π ∈ prBPP.
We have a probabilistic t(n)-time algorithm A that decides Π with 2-
sided error at most 2−n on inputs of length n, where t(n) = poly(n).
As an upper bound, A uses at most t(n) random bits. Thus we can
view A as a deterministic algorithm on two inputs — its regular input
x ∈ {0, 1}n and its coin tosses r ∈ {0, 1}t(n). (This view of a random-
ized algorithm is useful throughout the study of pseudorandomness.)
We’ll write A(x; r) for As output on input x and coin tosses r. For
every n, there is a circuit C(x; r) of size poly(t(n)) = poly(n) that sim-
ulates the computation of A for any input x ∈ {0, 1}n r ∈ {0, 1}t(n),
and moreover C can be constructed in time poly(t(n)) = poly(n). (See
any text on complexity theory for a proof that circuits can eﬃciently
simulate Turing machine computations.) Let Cx(r) be the circuit C
with x hardwired in. Then the map x (cid:14)→ (Cx, 1/2n) is a polynomial-
time reduction from Π to [+ε]-Approx Circuit Average. Indeed, if
x ∈ ΠN , then A accepts with probability at most 1/2n, soµ(C x) ≤
1/2n. And if x ∈ ΠY , then µ(Cx) ≥ 1 − 1/2n > 1/2n + ε(n(cid:3)), where
n(cid:3) = |(Cx, 1/2n)| = poly(n) and we take n suﬃciently large.



<!-- pdf-page: 31 -->
28 The Power of Randomness

Consequently, derandomizing this one algorithm is equivalent to

derandomizing all of prBPP:

Corollary 2.31.
only if prBPP = prP.

[+ε]-Approx Circuit Average is in prP if and

Note that our proof of Proposition 2.25, giving an exponential lower
bound for [+ε]-Approx Oracle Average does not extend to [+ε]-
Approx Circuit Average. Indeed, it’s not even clear how to deﬁne
the notion of “query” for an algorithm that is given a circuit C explic-
itly; it can do arbitrary computations that involve the internal structure
of the circuit. Moreover, even if we restrict attention to algorithms that
only use the input circuit C as if it were an oracle (other than com-
puting the input length |(C, p)| to know how long it can run), there is
no guarantee that the function f1 constructed in the proof of Proposi-
tion 2.25 has a small circuit.

2.3.3 Approximate Counting to within Relative Error

Note that [+ε]-Approx Circuit Average can be viewed as the prob-
lem of approximately counting the number of satisfying assignments of
a circuit C : {0, 1}m → {0, 1} to within additive error ε · 2m, and a solu-
tion to this problem may give useless answers for circuits that don’t
have very many satisfying assignments (e.g., circuits with fewer than
2m/2 satisfying assignments). Thus people typically study approximate
counting to within relative error. For example, given a circuit C, out-
put a number that is within a (1 + ε) factor of its number of satisfy-
ing assignments, #C. Or the following essentially equivalent decision
problem:

Computational Problem 2.32. [×(1 + ε)]-Approx #CSAT is the
following promise problem:

CSATε

Y = {(C, N ) : #C > (1 + ε) · N }
N = {(C, N ) : #C ≤ N }
Here ε can be a constant or a function of the input length n = |(C, N )|.

CSATε



<!-- pdf-page: 32 -->
2.3 Sampling and Approximation Problems

29

Unfortunately, this problem is NP-hard for general circuits (con-
sider the special case that N = 0), so we do not expect a prBPP
algorithm. However, there is a very pretty randomized algorithm if we
restrict to DNF formulas.

Computational Problem 2.33. [×(1 + ε)]-Approx #DNF is the
restriction of [×(1 + ε)]-Approx #CSAT to C that are formulas in
disjunctive normal form (DNF) (i.e., an OR of clauses, where each
clause is an AND of variables or their negations).

Theorem 2.34. For every function ε(n) ≥ 1/poly(n),
Approx #DNF is in prBPP.

[×(1 + ε)]-

Proof. It suﬃces to give a probabilistic polynomial-time algorithm that
estimates the number of satisfying assignments to within a 1 ± ε factor.
Let ϕ(x1, . . . , xm) be the input DNF formula.

A ﬁrst approach would be to apply random sampling as we have
used above: Pick t random assignments uniformly from {0, 1}m and
evaluate ϕ on each. If k of the assignments satisfy ϕ, output (k/t) · 2m.
However, if #ϕ is small (e.g., 2m/2), random sampling will be unlikely
to hit any satisfying assignments, and our estimate will be 0.

The idea to get around this diﬃculty is to embed the set of sat-
isfying assignments, A, in a smaller set B so that sampling can be
useful. Speciﬁcally, we will deﬁne sets A(cid:3) ⊂ B satisfying the following
properties:

(1) |A(cid:3)| = |A|.
(2) |A(cid:3)| ≥ |B|/poly(n), where n = |(ϕ, N )|.
(3) We can decide membership in A(cid:3) in polynomial time.
(4) |B| computable in polynomial time.
(5) We can sample uniformly at random from B in polynomial

time.

Letting (cid:6) be the number of clauses, we deﬁne A(cid:3) and B as follows:

B = {(i, α) ∈ [(cid:6)] × {0, 1}m : α satisﬁes the ith clause}
A(cid:3) = {(i, α) ∈ B : α does not satisfy any clauses before the ith clause}



<!-- pdf-page: 33 -->
30 The Power of Randomness

Now we verify the desired properties:

(1) |A| = |A(cid:3)| because for each satisfying assignment α, A(cid:3) con-
tains only one pair (i, α), namely the one where the ﬁrst
clause satisﬁed by α is the ith one.

(2) The size of A(cid:3) and B can diﬀer by at most a factor of (cid:6), since
each satisfying assignment α occurs at most (cid:6) times in B.
(3) It is easy to decide membership in A(cid:3) in polynomial time.
(4) |B| =

is the number of literals in
clause i (after removing contradictory clauses that contain
both a variable and its negation).

i=1 2m−mi, where mi

(cid:4)
(cid:4)

(5) We can randomly sample from B as follows. First pick a
clause with probability proportional to the number of satis-
fying assignments it has (2m−mi). Then, ﬁxing those variables
in the clause (e.g., if xj is in the clause, set xj = 1, and if ¬xj
is in the clause, set xj = 0), assign the rest of the variables
uniformly at random.

Putting this together, we deduce the following algorithm:

Algorithm 2.35 ([×(1 + ε)]-Approx #DNF).
Input: A DNF formula ϕ(x1, . . . , xm) with (cid:6) clauses

(1) Generate a random sample of t points in B = {(i, α) ∈ [(cid:6)] ×
{0, 1}m : α satisﬁes the ith clause}, for an appropriate choice
of t = O(1/(ε/(cid:6))2).

(2) Let ˆµ be the fraction of sample points that land in A(cid:3) =
{(i, α) ∈ B : α does not satisfy any clauses before the ith
clause}.

(3) Output ˆµ · |B|.

By

the Chernoﬀ bound,

of
t = O(1/(ε/(cid:6))2), we have ˆµ = |A(cid:3)|/|B| ±ε/(cid:6) with high probabil-
ity (where we write γ = α ± β to mean that γ ∈ [α − β, α + β]). Thus,
with high probability the output of the algorithm satisﬁes:

appropriate

choice

for

an

ˆµ · |B| = |A(cid:3)| ±ε|B |/(cid:6)

= |A| ±ε|A|.



<!-- pdf-page: 34 -->
2.3 Sampling and Approximation Problems

31

There is no deterministic polynomial-time algorithm known for this

problem:

Open Problem 2.36. Give a deterministic polynomial-time algo-
rithm for approximately counting the number of satisfying assignments
to a DNF formula.

However, when we study pseudorandom generators in Section 7, we
will see a quasipolynomial-time derandomization of the above algorithm
(i.e., one in time 2polylog(n)).

2.3.4 MaxCut

We give an example of another algorithmic problem for which random
sampling is a useful tool.

Deﬁnition 2.37. For a graph G = (V, E) and S, T ⊂ V , deﬁne
cut(S, T ) ={{u, v } ∈E : u ∈ S, v ∈ T }, and cut(S) = cut(S, V \ S).

Computational Problem 2.38. MaxCut (search version): Given a
graph G, ﬁnd a largest cut in G, i.e., a set S maximizing |cut(S)|.

Solving this problem optimally is NP-hard (in contrast to MIN-
CUT, which is known to be in P). However, there is a simple random-
ized algorithm that ﬁnds a cut of expected size at least |E|/2 (which
is of course at least 1/2 the optimal, and hence this is referred to as a
“1/2-approximation algorithm”):

Algorithm 2.39 (MaxCut approximation).
Input: A graph G = (V, E) (with no self-loops)

Output a random subset S ⊂ V . That is, place each vertex v in
S independently with probability 1/2.



<!-- pdf-page: 35 -->
32 The Power of Randomness

To analyze this algorithm, consider any edge e = (u, v). Then the
probability that e crosses the cut is 1/2. By linearity of expectations, we
have:

(cid:3)

E[|cut(S)|] =

Pr[e is cut] = |E|/2.

e∈E

This also serves as a proof, via the probabilistic method, that every
graph (without self-loops) has a cut of size at least |E|/2.

In Section 3, we will see how to derandomize this algorithm. We
note that there is a much more sophisticated randomized algorithm
that ﬁnds a cut whose expected size is within a factor of 0.878 of the
largest cut in the graph (and this algorithm can also be derandomized).

2.4 Random Walks and S-T Connectivity

2.4.1 Graph Connectivity

One of the most basic problems in computer science is that of deciding
connectivity in graphs:

Computational Problem 2.40. S-T Connectivity: Given a
directed graph G and two vertices s and t, is there a path from s
to t in G?

This problem can of course be solved in linear time using breadth-
ﬁrst or depth-ﬁrst search. However, these algorithms also require linear
space. It turns out that S-T Connectivity can in fact be solved
using much less workspace. (When measuring the space complexity of
algorithms, we do not count the space for the (read-only) input and
(write-only) output.)

Theorem 2.41. There is a deterministic algorithm deciding S-T Con-
nectivity using space O(log2 n) (and time O(nlog n)).

Proof. The following recursive algorithm IsPath(G, u, v, k) decides
whether there is a path of length at most k from u to v.



<!-- pdf-page: 36 -->
2.4 Random Walks and S-T Connectivity

33

Algorithm 2.42 (Recursive S-T Connectivity).
IsPath(G, u, v, k):

(1) If k = 0, accept if u = v.
(2) If k = 1, accept if u = v or (u, v) is an edge in G.
(3) Otherwise, loop through all vertices w in G and accept if
both IsPath(G, u, w, (cid:15)k/2(cid:16)) and IsPath(G, w, v, (cid:17)k/2(cid:18)) accept
for some w.

We can solve S-T Connectivity by running IsPath(G, s, t, n),
where n is the number of vertices in the graph. The algorithm has
log n levels of recursion and uses log n space per level of recursion (to
store the vertex w), for a total space bound of log2 n. Similarly, the
algorithm uses linear time per level of recursion, for a total time bound
of O(n)log n.

It is not known how to improve the space bound in Theorem 2.41
or to get the running time down to polynomial while maintaining space
no(1). For undirected graphs, however, we can do much better using a
randomized algorithm. Speciﬁcally, we can place the problem in the
following class:

Deﬁnition 2.43. A language L is in RL if there exists a randomized
algorithm A that always halts, uses space at most O(log n) on inputs
of length n, and satisﬁes:

• x ∈ L ⇒ Pr[A(x) accepts] ≥ 1/2.
• x (cid:1)∈ L ⇒ Pr[A(x) accepts] = 0.

Recall that our model of a randomized space-bounded machine is
one that has access to a coin-tossing box (rather than an inﬁnite tape
of random bits), and thus must explicitly store in its workspace any
random bits it needs to remember. The requirement that A always halts
ensures that its running time is at most 2O(log n) = poly(n), because
otherwise there would be a loop in its conﬁguration space. Similarly to



<!-- pdf-page: 37 -->
34 The Power of Randomness

RL, we can deﬁne L (deterministic logspace), co-RL (one-sided error
with errors only on no instances), and BPL (two-sided error).

Now we can state the theorem for undirected graphs.

Computational Problem 2.44. Undirected S-T Connectivity:
Given an undirected graph G and two vertices s and t, is there a path
from s to t in G?

Theorem 2.45. Undirected S-T Connectivity is in RL.

Proof Sketch: The algorithm simply does a polynomial-length ran-
dom walk starting at s.

Algorithm 2.46 (Undirected S-T Connectivity via Random
Walks).
Input: (G, s, t), where G = (V, E) has n vertices.

(1) Let v = s.
(2) Repeat poly(n) times:

(a) If v = t, halt and accept.
(b) Else let v R← {w : (v, w) ∈ E}.

(3) Reject (if we haven’t visited t yet).

Notice that this algorithm only requires space O(log n), to maintain
the current vertex v as well as a counter for the number of steps taken.
Clearly, it never accepts when there isn’t a path from s to t. In the next
section, we will prove that in any connected undirected graph, a random
walk of length poly(n) from one vertex will hit any other vertex with
high probability. Applying this to the connected component containing
s, it follows that the algorithm accepts with high probability when s
and t are connected.

This algorithm, dating from the 1970s, was derandomized only
in 2005. We will cover the derandomized algorithm in Section 4.4.



<!-- pdf-page: 38 -->
2.4 Random Walks and S-T Connectivity

35

However, the general question of derandomizing space-bounded algo-
rithms remains open.

Open Problem 2.47. Does RL = L? Does BPL = L?

2.4.2 Random Walks on Graphs

For generality that will be useful later, many of the deﬁnitions in this
section will be given for directed multigraphs (which we will refer to as
digraphs for short). By multigraph, we mean that we allow G to have
parallel edges and self-loops. Henceforth, we will refer to graphs with-
out parallel edges and self-loops as simple graphs. We call a digraph
d-regular if every vertex has indegree d and outdegree d. A self-loop is
considered a single directed edge (i, i) from a vertex i to itself, so con-
tributes 1 to both the indegree and outdegree of vertex i. An undirected
graph is a graph where the number of edges from i to j equals the num-
ber of edges from j to i for every i and j. (When i (cid:1)= j, we think of a pair
of edges (i, j) and (j, i) as comprising a single undirected edge {i, j},
and a self-loop (i, i) also corresponds to the single undirected edge {i}.)
To analyze the random-walk algorithm of the previous section, it

suﬃces to prove a bound on the hitting time of random walks.

Deﬁnition 2.48. For a digraph G = (V, E), we deﬁne its hitting
time as

hit(G) = max
i,j∈V

min{t : Pr[a random walk of

length t started at i visits j] ≥ 1/2}.

We note that hit(G) is often deﬁned as the maximum over vertices
i and j of the expected time for a random walk from i to visit j. The
two deﬁnitions are the same up to a factor of 2, and the above is more
convenient for our purposes.

We will prove:

Theorem 2.49. For every connected undirected graph G with n ver-
tices and maximum degree d, we have hit(G) =O (d2n3 log n).



<!-- pdf-page: 39 -->
36 The Power of Randomness

We observe that it suﬃces to prove this theorem for d-regular
graphs, because any undirected graph be made regular by adding self-
loops (and this can only increase the hitting time). This is the part of
our proof that fails for directed graphs (adding self-loops cannot correct
an imbalance between indegree and outdegree at a vertex), and indeed
Problem 2.10 shows that general directed graphs can have exponential
hitting time.

There are combinatorial methods for proving the above theorem,
but we will prove it using a linear-algebraic approach, as the same
methods will be very useful in our study of expander graphs. For an
n-vertex digraph G, we deﬁne its random-walk transition matrix, or
random-walk matrix for short, to be the n × n matrix M where Mi,j
is the probability of going from vertex i to vertex j in one step. That
is, Mi,j is the number of edges from i to j divided by the outdegree
of i. In case G is d-regular, M is simply the adjacency matrix of G
divided by d. Notice that for every probability distribution π ∈ Rn on
the vertices of G (written as a row vector), the vector πM is the prob-
ability distribution obtained by selecting a vertex i according to π and
then taking one step of the random walk to end at a vertex j. This is
because (πM )j =

(cid:4)

i πiMi,j.

In our application to bounding hit(G) for a regular digraph G, we
start at a probability distribution π = (0, . . . , 0, 1, 0, . . . , 0) ∈ Rn concen-
trated at vertex i, and are interested in the distribution πM t we get
after taking t steps on the graph. Speciﬁcally, we’d like to show that
it places nonnegligible mass on vertex j for t = poly(n). We will do
this by showing that it in fact converges to the uniform distribution
u = (1/n, 1/n, . . . , 1/n) ∈ Rn within a polynomial number of steps. Note
that uM = u by the regularity of G, so convergence to u is possible (and
will be guaranteed given some additional conditions on G).

(cid:7)

We will measure the rate of convergence in the (cid:6)2 norm. For vec-
tors x, y ∈ Rn, we will use the standard inner product (cid:19)x, y(cid:20) =
i xiyi,
and (cid:6)2 norm (cid:21)x(cid:21) =
(cid:19)x, x(cid:20). We write x ⊥ y to mean that x and y are
orthogonal, i.e., (cid:19)x, y(cid:20) = 0. We want to determine how large k needs
to be so that (cid:21)πM k − u(cid:21) is “small.” This is referred to as the mixing
time of the random walk. Mixing time can be deﬁned with respect to
various distance measures and the (cid:6)2 norm is not the most natural one,

(cid:4)



<!-- pdf-page: 40 -->
2.4 Random Walks and S-T Connectivity

37

but it has the advantage that we will be able to show that the distance
decreases noticeably in every step. This is captured by the following
quantity.

Deﬁnition 2.50. For a regular digraph G with random-walk matrix
M , we deﬁne

λ(G) def= max

π

(cid:21)πM − u(cid:21)
(cid:21)π − u(cid:21) = max
x⊥u

(cid:21)xM (cid:21)
(cid:21)x(cid:21) ,

where the ﬁrst maximization is over all probability distributions π ∈
[0, 1]n and the second is over all vectors x ∈ Rn such that x ⊥ u. We
write γ(G) def= 1 − λ(G).

To see that the ﬁrst deﬁnition of λ(G) is smaller than or equal to
the second, note that for any probability distribution π, the vector
x = (π − u) is orthogonal to uniform (i.e., the sum of its entries is
zero). For the converse, observe that given any vector x ⊥ u, the vector
π = u + αx is a probability distribution for a suﬃciently small α. It can
be shown that λ(G) ∈ [0, 1]. (This follows from Problems 2.10 and 2.9.)
The following lemma is immediate from the deﬁnition of λ(G).

Lemma 2.51. Let G be a regular digraph with random-walk matrix
M . For every initial probability distribution π on the vertices of G and
every t ∈ N, we have

(cid:21)πM t − u(cid:21) ≤λ(G) t · (cid:21)π − u(cid:21) ≤λ(G) t.

Proof. The ﬁrst inequality follows from the deﬁnition of λ(G) and
induction. For the second, we have:

(cid:21)π − u(cid:21)2 = (cid:21)π2(cid:21) + (cid:21)u(cid:21)2 − 2(cid:19)π, u(cid:20)
i + 1/N − 2/N
π2

(cid:3)

=

(cid:3)

πi

πi

≤

i
(cid:3)

i

πi + 1/N − 2/N

i
(cid:3)

i

= 1 − 1/N ≤ 1.



<!-- pdf-page: 41 -->
38 The Power of Randomness

Thus a smaller value of λ(G) (equivalently, a larger value of γ(G))
means that the random walk mixes more quickly. Speciﬁcally, for t ≥
ln(n/ε)/γ(G), it follows that every entry of πM t has probability mass
at least 1/n − (1 − γ(G))t ≥ (1 − ε)/n, and thus we should think of
the walk as being “mixed” within O((log n)/γ(G)). Note that after
O(1/γ(G)) steps, the (cid:6)2 distance is already small (say at most 1/10),
but this is not a satisfactory notion of mixing — a distribution that
assigns ε2 mass to 1/ε2 vertices has (cid:6)2 distance smaller than ε from the
uniform distribution.

Corollary 2.52.
O(n log n/γ(G)).

For

every

regular

digraph G,

hit(G) =

Proof. Let i, j be any two vertices of G. As argued above, a walk of
length ln(2n)/γ(G) from any start vertex has a probability of at least
1/2n of ending at j. Thus, if we do O(n) such walks consecutively, we
will hit j with probability at least 1/2.

Thus, our task reduces to bounding γ(G):

Theorem 2.53. If G is a connected, nonbipartite, and d-regular undi-
rected graph on n vertices, then γ(G) = Ω(1/(dn)2).

Theorem 2.53 and Corollary 2.52 imply Theorem 2.49, as any undi-
rected and connected graph of maximum degree d can be made (d + 1)-
regular and nonbipartite by adding self-loops to each vertex. (We
remark that the bounds of Theorems 2.53 and 2.49 are not tight.) The-
orem 2.53 is proven in Problem 2.9, using a connection with eigenvalues
described in the next section.

2.4.3 Eigenvalues

Recall that a nonzero vector v ∈ Rn is an eigenvector of n × n matrix
M if vM = λv for some λ ∈ R, which is called the corresponding eigen-
value. A useful feature of symmetric matrices is that they can be
described entirely in terms of their eigenvectors and eigenvalues.



<!-- pdf-page: 42 -->
2.4 Random Walks and S-T Connectivity

39

Theorem 2.54 (Spectral Theorem for Symmetric Matrices). If
M is a symmetric n × n real matrix with distinct eigenvalues µ1, . . . , µk,
then the eigenspaces Wi = {v ∈ Rn : vM = µiM } are orthogonal (i.e.,
v ∈ Wi, w ∈ Wj ⇒ v ⊥ w if i (cid:1)= j) and span Rn (i.e., Rn = W1 + · · · +
Wk). We refer to the dimension of Wi as the multiplicity of eigenvalue
µi. In particular, Rn has a basis consisting of orthogonal eigenvectors
v1, . . . , vn having respective eigenvalues λ1, . . . , λn, where the number of
times µi occurs among the λjs exactly equals the multiplicity of µi.

Notice that if G is a undirected regular graph, then its random-walk
matrix M is symmetric. We know that uM = u, so the uniform distri-
bution is an eigenvector of eigenvalue 1. Let v2, . . . , vn and λ2, . . . , λn
be the remaining eigenvectors and eigenvalues, respectively. Given any
probability distribution π, we can write it as π = u + c2v2 + · · · + cnvn.
Then the probability distribution after k steps on the random walk is

πM t = u + λt

2c2v2 + · · · + λt

ncnvn.

In Problem 2.9, it is shown that all of the λis have absolute value at
most 1. Notice that if they all have magnitude strictly smaller than 1,
then πM t indeed converges to u. Thus it is not surprising that our
measure of mixing rate, λ(G), equals the absolute value of the second
largest eigenvalue (in magnitude).

Lemma 2.55. Let G be an undirected graph with random-walk matrix
M . Let λ1, . . . , λn be the eigenvalues of M , sorted so that 1 = λ1 ≥
|λ2| ≥ |λ3| ≥ · · · ≥ |λn|. Then λ(G) =|λ 2|.

Proof. Let u = v1, v2, . . . , vn be the basis of orthogonal eigenvectors
corresponding to the λis. Given any vector x ⊥ u, we can write x =
c2v2 + · · · + cnvn. Then:

(cid:21)xM (cid:21)2 = (cid:21)λ2c2v2 + · · · + λncnvn(cid:21)2

= λ2

2c2
2

(cid:21)v2(cid:21)2 + · · · + λ2

nc2
n

(cid:21)vn(cid:21)2



<!-- pdf-page: 43 -->
40 The Power of Randomness

≤ |λ2|2 · (c2
2
= |λ2|2 · (cid:21)x(cid:21)2

(cid:21)v2(cid:21)2 + · · · + c2
n

(cid:21)vn(cid:21)2)

Equality is achieved with x = v2.

Thus, bounding λ(G) amounts to bounding the eigenvalues of G.
Due to this connection, γ(G) = 1 − λ(G) is often referred to as the
spectral gap, as it is the gap between the largest eigenvalue and the
second largest eigenvalue in absolute value.

2.4.4 Markov Chain Monte Carlo

Random walks are a powerful tool in the design of randomized algo-
rithms. In particular, they are the heart of the “Markov Chain Monte
Carlo” method, which is widely used in statistical physics and for solv-
ing approximate counting problems. In these applications, the goal is
to generate a random sample from an exponentially large space, such
as an (almost) uniformly random perfect matching for a given bipar-
tite graph G. (It turns out that this is equivalent to approximately
counting the number of perfect matchings in G.) The approach is to
do a random walk on an appropriate (regular) graph ˆG deﬁned on
the space (e.g., by doing random local changes on the current per-
fect matching). Even though ˆG is typically of size exponential in the
input size n = |G|, in many cases it can be proven to have mixing time
poly(n) = polylog(| ˆG|), a property referred to as rapid mixing. These
Markov Chain Monte Carlo methods provide some of the best examples
of problems where randomization yields algorithms that are exponen-
tially faster than all known deterministic algorithms.

2.5 Exercises

lemma). Prove Lemma 2.4: If
Problem 2.1 (Schwartz–Zippel
f (x1, . . . , xn) is a nonzero polynomial of degree d over a ﬁeld (or integral
domain) F and S ⊂ F, then

Pr
α1,...,αn

R←S

[f (α1, . . . , αn) = 0] ≤ d
|S| .



<!-- pdf-page: 44 -->
You may use the fact that every nonzero univariate polynomial of
degree d over F has at most d roots.

2.5 Exercises

41

Problem 2.2 (Robustness of the model). Suppose we modify our
model of randomized computation to allow the algorithm to obtain
a random element of {1, . . . , m} for any number m whose binary
representation it has already computed (as opposed to just allowing
it access to random bits). Show that this would not change the classes
BPP and RP.

Problem 2.3 (Zero error versus 1-sided error). Prove that
ZPP = RP ∩ co-RP.

Problem 2.4(Polynomial Identity Testing for integer circuits).
In this problem, you will show how to do Polynomial Identity
Testing for arithmetic circuits over the integers. The Prime Number
Theorem says that the number of primes less than T is (1 ± O(1)) ·
T /ln T , where the O(1) tends to 0 as T → ∞. You may use this fact in
the problem below.

(1) Show that if N is a nonzero integer and M R← {1, . . . , log2 N },

then

Pr[N (cid:1)≡ 0 (mod M )] = Ω(1/loglogN ).

(2) Use the above to prove Theorem 2.12: Arithmetic Circuit

Identity Testing over Z is in co-RP.

Problem 2.5(Polynomial Identity Testing via Modular Reduc-
tion). In this problem, you will analyze an alternative to the algorithm
seen in class, which directly handles polynomials of degree larger than
the ﬁeld size. It is based on the same idea as Problem 2.4, using the
fact that polynomials over a ﬁeld have many of the same algebraic
properties as the integers.



<!-- pdf-page: 45 -->
42 The Power of Randomness

The following deﬁnitions and facts may be useful: A polynomial
f (x) over a ﬁeld F is called irreducible if it has no nontrivial factors
(i.e., factors other than constants from F or constant multiples of f ).
Analogously to prime factorization of integers, every polynomial over
F can be factored into irreducible polynomials and this factorization is
unique (up to reordering and constant multiples). It is known that the
number of irreducible polynomials of degree at most d over a ﬁeld F is
at least |F|d+1/2d. (This is similar to the Prime Number Theorem for
integers mentioned in Problem 2.4, but is easier to prove.) For polyno-
mials f (x) and g(x), f (x) modg (x) is the remainder when f is divided
by g. (More background on polynomials over ﬁnite ﬁelds can be found
in the references listed in Section 2.6.)

In this problem, we consider a version of the Polynomial Iden-
tity Testing problem where a polynomial f (x1, . . . , xn) over ﬁnite
ﬁeld F is presented as a formula built up from elements of F and the
variables x1, . . . , xn using addition, multiplication, and exponentiation
with exponents given in binary. We also assume that we are given a
representation of F enabling addition, multiplication, and division in F
to be done quickly.

(1) Let f (x) be a univariate polynomial of degree ≤ D over
a ﬁeld F. Prove that there are constants c, c(cid:3) such that if
f (x) is nonzero (as a formal polynomial) and g(x) is a ran-
domly selected polynomial of degree at most d = c log D, then
the probability that f (x) modg (x) is nonzero is at least
1/c(cid:3) log D. Deduce a randomized, polynomial-time identity
test for univariate polynomials presented in the above form.
(2) Obtain a randomized polynomial-time identity test for mul-
tivariate polynomials by giving a (deterministic) reduction
to the univariate case.

Problem 2.6 (Primality Testing).

(1) Show that for every positive integer n, the polynomial iden-

tity (x + 1)n ≡ xn + 1 (mod n) holds iﬀ n is prime.



<!-- pdf-page: 46 -->
2.5 Exercises

43

(2) Obtain a co-RP algorithm for the language Primality
Testing = {n : n prime} using Part 1 together with Prob-
lem 2.5. (In your analysis, remember that the integers
modulo n are a ﬁeld only when n is prime.)

Problem 2.7 (Chernoﬀ Bound). Let X1, . . . , Xt be independent
(cid:4)
t
[0, 1]-valued random variables, and X =
i=1 Xi. (Note that, in con-
trast to the statement of Theorem 2.21, here we are writing X for the
sum of the Xis rather than their average.)

(1) Show that for every r ∈ [0, 1/2], E[erX ] ≤ er E[X]+r2t. (Hint:

1 +x ≤ ex ≤ 1 +x + x2 for all x ∈ [0, 1/2].)

(2) Deduce the Chernoﬀ Bound of Theorem 2.21: Pr [X] ≥
E[X]+ εt ≤ e−ε2t/4 and Pr [X ≤ E[X] − εt] ≤ e−ε2t/4.

(3) Where did you use the independence of the Xis?

Problem 2.8 (Necessity of Randomness for Identity Testing*).
In this problem, we consider the “oracle version” of the identity test-
ing problem, where an arbitrary polynomial f : Fm → F of degree d is
given as an oracle and the problem is to test whether f = 0. Show that
any deterministic algorithm that solves this problem when m = d = n
must make at least 2n queries to the oracle (in contrast to the random-
ized identity testing algorithm from class, which makes only one query
provided that |F| ≥2n).

Is this a proof that P (cid:1)= RP? Explain.

Problem 2.9 (Spectral Graph Theory). Let M be the random-
walk matrix for a d-regular undirected graph G = (V, E) on n vertices.
We allow G to have self-loops and multiple edges. Recall that the uni-
form distribution is an eigenvector of M of eigenvalue λ1 = 1. Prove the
following statements. (Hint: for intuition, it may help to think about
what the statements mean for the behavior of the random walk on G.)



<!-- pdf-page: 47 -->
44 The Power of Randomness

(1) All eigenvalues of M have absolute value at most 1.
(2) G is disconnected ⇐⇒ 1 is an eigenvalue of multiplicity at

least 2.

(3) Suppose G is connected. Then G is bipartite ⇐⇒ −1 is an

eigenvalue of M .

(4) G connected ⇒ all eigenvalues of M other than λ1 are at
most 1 − 1/poly(n, d). To do this, it may help to ﬁrst show
that the second largest eigenvalue of M (not necessarily in
absolute value) equals

max
x

(cid:19)xM, x(cid:20) = 1 − 1
d

· min
x

(cid:3)

(i, j) ∈ E

(xi − xj)2,

(cid:4)

i xi = 0, and (cid:19)x, y(cid:20) =

where the maximum/minimum is taken over all vectors x
i xiyi is the
of length 1 such that
standard inner product. For intuition, consider restricting the
above maximum/minimum to x ∈ {+α, −β}n for α, β > 0.
(5) G connected and nonbipartite ⇒ all eigenvalues of M (other
than 1) have absolute value at most 1 − 1/poly(n, d) and
thus γ(G) ≥ 1/poly(n, d).

(cid:4)

(6*) Establish the (tight) bound 1 − Ω(1/d · D · n) in Part 4,
where D is the diameter of the graph. Conclude that γ(G) =
Ω(1/d2n2) if G is connected and nonbipartite.

Problem 2.10 (Hitting Time and Eigenvalues for Directed
Graphs).

(1) Show that for every n, there exists a digraph G with n ver-

tices, outdegree 2, and hit(G) = 2Ω(n).
(cid:7)

(2) Let G be a regular digraph with random-walk matrix M .
λ(G(cid:3)), where G(cid:3) is the undirected graph

Show that λ(G) =
whose random-walk matrix is M M T .

(3) A digraph G is called Eulerian if it is connected and every
vertex has the same indegree as outdegree.3 (For example,

3 This terminology comes from the fact that these are precisely the digraphs that have
Eulerian circuits, closed paths that visit all vertices use every directed edge exactly once.



<!-- pdf-page: 48 -->
2.5 Exercises

45

if we take an connected undirected graph and replace each
undirected edge {u, v} with the two directed edges (u, v) and
(v, u), we obtain an Eulerian digraph.) Show that if G is
an n-vertex Eulerian digraph of maximum degree d, then
hit(G) = poly(n, d).

Problem 2.11(Consequences of Derandomizing prBPP). Even
though prBPP is a class of decision problems, it also captures many
other types of problems that can be solved by randomized algorithms:

(1) (Approximation Problems) Consider the task of approximat-
ing a function f : {0, 1}∗ → N to within a (1 + ε(n)) mul-
tiplicative factor, for some function ε : N → R≥0. Suppose
there is a probabilistic polynomial-time algorithm A such
that for all x, Pr[A(x) ≤ f (x) ≤ (1 + ε(|x|)) · A(x)] ≥ 2/3,
where the probability is taken over the coin tosses of A.
Show that if prBPP = prP, then there is a deterministic
polynomial-time algorithm B such that for all x, B(x) ≤
f (x) ≤ (1 + ε(|x|)) · B(x). (Hint: use a deﬁnition similar to
Computational Problem 2.32.)

(2) (NP Search Problems) An NP search problem is speciﬁed by
a polynomial-time veriﬁer V and a polynomial p; the problem
is, given an input x ∈ {0, 1}n, ﬁnd a string y ∈ {0, 1}p(n) such
that V (x, y) = 1. Suppose that such a search problem can be
solved in probabilistic polynomial time, i.e., there is a prob-
abilistic polynomial-time algorithm A such that for every
input x ∈ {0, 1}n, outputs y ∈ {0, 1}p(n) such that V (x, y) = 1
with probability at least 2/3 over the coin tosses of A.
Show that if prBPP = prP, then there is a deterministic
polynomial-time algorithm B such that for every x ∈ {0, 1}n,
B(x) always outputs y ∈ {0, 1}p(n) such that V (x, y) = 1.
(Hint: consider a promise problem whose instances are pairs
(x, r) where r is a preﬁx of the coin tosses of A.)

(3) (MA Search Problems) In a relaxation of NP, known
as MA, we allow the veriﬁer V to be probabilistic. Let



<!-- pdf-page: 49 -->
46 The Power of Randomness

Π = (ΠY , ΠN ) be a promise problem decided by V ,
i.e.,
Pr[V (x, y) = 1] ≥ 2/3 for (x, y) ∈ ΠY , and Pr[V (x, y) = 1] ≤
1/3 for (x, y) ∈ ΠN . Suppose that the corresponding search
problem can be solved in probabilistic polynomial time, i.e.,
there is a probabilistic polynomial-time algorithm A such
that for every input x ∈ {0, 1}n, outputs y ∈ {0, 1}p(n) such
that (x, y) ∈ ΠY with probability at least 2/3 over the coin
tosses of A. Show that if prBPP = prP, then there is a
deterministic polynomial-time algorithm B such that for
every x ∈ {0, 1}n, B(x) always outputs y ∈ {0, 1}p(n) such
that (x, y) /∈ ΠN . (Note that this conclusion is equivalent to
(x, y) ∈ ΠY if Π is a language, but is weaker otherwise.)
(4) Using Part 3, the Prime Number Theorem (see Problem 2.4),
and the fact that Primality Testing is in BPP (Prob-
lem 2.6) to show that if prBPP = prP, then there is a deter-
ministic polynomial-time algorithm that given a number N ,
outputs a prime in the interval [N, 2N ) for all suﬃciently
large N .

2.6 Chapter Notes and References

Recommended textbooks on randomized algorithms are Motwani–
Raghavan [291] and Mitzenmacher–Upfal [290]. The algorithmic power
of randomization became apparent in the 1970s with a number of strik-
ing examples, notably Berlekamp’s algorithm for factoring polynomi-
als over large ﬁnite ﬁelds [66] and the Miller–Rabin [287, 314] and
Solovay–Strassen [369] algorithms for Primality Testing. The ran-
domized algorithm for Polynomial Identity Testing was indepen-
dently discovered by DeMillo and Lipton [116], Schwartz [351], and
Zippel [425]. More recently, a deterministic polynomial-time Polyno-
mial Identity Testing algorithm for formulas in ΣΠΣ form with
a constant number of terms was given by Kayal and Saxena [241],
improving a previous quasipolynomial-time algorithm of Dvir and
Shpilka [126]. Problem 2.4 is from [351]. Problem 2.8 is from [260].
Algorithms for Polynomial Identity Testing and the study of



<!-- pdf-page: 50 -->
2.6 Chapter Notes and References

47

arithmetic circuits more generally are covered in the recent survey
by Shpilka and Yehudayoﬀ [362]. Recommended textbooks on abstract
algebra and ﬁnite ﬁelds are [36, 263].

The randomized algorithm for Perfect Matching is due to
Lov´asz [267], who also showed how to extend the algorithm to non-
bipartite graphs. An eﬃcient parallel randomized algorithm for ﬁnding
a perfect matching was given by Karp, Upfal, and Wigderson [237] (see
also [294]). A randomized algorithm for ﬁnding a perfect matching in
the same sequential time complexity as Lov´asz’s algorithm was given
recently by Mucha and Sankowski [292] (see also [201]).

The eﬃcient sequential and parallel algorithms for Determinant
mentioned in the text are due [108, 377] and [64, 76, 111], respectively.
For more on algebraic complexity and parallel algorithms, we refer to
the textbooks [89] and [258], respectively. The Polynomial Identity
Testing and Primality Testing algorithms of Problems 2.5 and
2.6 are due to Agrawal and Biswas [5]. Agrawal, Kayal, and Saxena [6]
derandomized the Primality Testing algorithm of [5] to prove that
Primality Testing is in P.

The randomized complexity classes RP, BPP, ZPP, and PP were
formally deﬁned by Gill [152], who conjectured that BPP (cid:1)= P (in fact
ZPP (cid:1)= P). Chernoﬀ Bounds are named after H. Chernoﬀ [95]; the
version in Theorem 2.21 is due to Hoeﬀding [204] and is sometimes
referred to as Hoeﬀding’s Inequality. The survey by Dubhashi and Pan-
conesi [121] has a detailed coverage of Chernoﬀ Bounds and other tail
inequalities. Problem 2.3 is due to Rabin (cf. [152]).

The computational perspective on sampling, as introduced in
Section 2.3.1, is surveyed in [155, 156]. Sampling is perhaps the sim-
plest example of a computational problem where randomization enables
algorithms with running time sublinear in the size of the input. Such
sublinear-time algorithms are now known for a wide variety of interest-
ing computational problems; see the surveys [337, 339].

Promise problems were

introduced by Even, Selman, and
Yacobi
[137]. For survey of their role in complexity theory, see
Goldreich [159]. Problem 2.11 on the consequences of prBPP = prP
is from [163].



<!-- pdf-page: 51 -->
48 The Power of Randomness

The randomized algorithm for [×(1 + ε)]-Approx #DNF is due
to Karp and Luby [236], who initiated the study of randomized
algorithms for approximate counting problems. A 1/2-approximation
algorithm for MaxCut was ﬁrst given in [342]; that algorithm can
be viewed as a natural derandomization of Algorithm 2.39. (See Algo-
rithm 3.17.) The 0.878-approximation algorithm was given by Goemans
and Williamson [154].

The O(log2 n)-space algorithm for S-T Connectivity is due to
Savitch [349]. Using the fact that S-T Connectivity (for directed
graphs) is complete for nondeterministic logspace (NL), this result is
equivalent to the fact that NL ⊂ L2, where Lc is the class of languages
that can be decided deterministic space O(logc n). The latter formu-
lation (and its generalization NSPACE(s(n)) ⊂ DSPACE(s(n)2)) is
known as Savitch’s Theorem. The randomized algorithm for Undi-
rected S-T Connectivity was given by Aleliunas, Karp, Lipton,
Lov´asz, and Racko [13], and was recently derandomized by Rein-
gold [327] (see Section 4.4).

For more background on random walks, mixing time, and the
Markov Chain Monte Carlo Method, we refer the reader to [290, 291,
317]. The use of this method for counting perfect matchings is due to
[83, 219, 220].

The bound on hitting time given in Theorem 2.49 is not tight; for
example, it can be improved to Θ(n2) for regular graphs that are simple
(have no self-loops or parallel edges) [229].

Even though we will focus primarily on undirected graphs (e.g., in
our study of expanders in Section 4), much of what we do generalizes to
regular, or even Eulerian, digraphs. See Problem 2.10 and the references
[139, 286, 331]. Problem 2.10, Part 2 is from [139].

The Spectral Theorem (Theorem 2.54) can be found in any stan-
dard textbook on linear algebra. Problem 2.9 is from [269]; Alon and
Sudakov [26] strengthen it to show γ(G) = Ω(1/dDn), which implies a
tight bound of γ(G) = Ω(1/n2) for simple graphs (where D = O(n/d)).
Spectral Graph Theory is a rich subject, with many applications
beyond the scope of this text; see the survey by Spielman [371] and
references therein.



<!-- pdf-page: 52 -->
2.6 Chapter Notes and References

49

One signiﬁcant omission from this section is the usefulness of ran-
domness for verifying proofs. Recall that NP is the class of languages
having membership proofs that can be veriﬁed in P. Thus it is natural
to consider proof veriﬁcation that is probabilistic, leading to the class
MA, as well as a larger class AM, where the proof itself can depend on
the randomness chosen by the veriﬁer [44]. (These are both subclasses of
the class IP of languages having interactive proof systems [177].) There
are languages, such as Graph Nonisomorphism, that are in AM but
are not known to be in NP [170]. “Derandomizing” these proof sys-
tems (e.g., proving AM = NP) would show that Graph Nonisomor-
phism is in NP, i.e., that there are short proofs that two graphs are
nonisomorphic. Similarly to sampling and sublinear-time algorithms,
randomized proof veriﬁcation can also enable one to read only a small
portion of an appropriately encoded NP proof, leading to the cele-
brated PCP Theorem and its applications to hardness of approxima-
tion [33, 34, 138]. For more about interactive proofs and PCPs, see
[32, 160, 400].



<!-- pdf-page: 53 -->
3

Basic Derandomization Techniques

In the previous section, we saw some striking examples of the power of
randomness for the design of eﬃcient algorithms:

• Polynomial Identity Testing in co-RP.
• [×(1 + ε)]-Approx #DNF in prBPP.
• Perfect Matching in RNC.
• Undirected S-T Connectivity in RL.
• Approximating MaxCut in probabilistic polynomial time.

This was of course only a small sample; there are entire texts on

randomized algorithms. (See the notes and references for Section 2.)

In the rest of this survey, we will turn toward derandomization —
trying to remove the randomness from these algorithms. We will achieve
this for some of the speciﬁc algorithms we studied, and also consider the
larger question of whether all eﬃcient randomized algorithms can be
derandomized. For example, does BPP = P? RL = L? RNC = NC?
In this section, we will introduce a variety of “basic” derandom-
ization techniques. These will each be deﬁcient in that they are either
infeasible (e.g., cannot be carried out in polynomial time) or special-
ized (e.g., apply only in very speciﬁc circumstances). But it will be

50



<!-- pdf-page: 54 -->
3.1 Enumeration

51

useful to have these as tools before we proceed to study more sophisti-
cated tools for derandomization (namely, the “pseudorandom objects”
of Sections 4–7).

3.1 Enumeration

We are interested in quantifying how much savings randomization pro-
vides. One way of doing this is to ﬁnd the smallest possible upper bound
on the deterministic time complexity of languages in BPP. For exam-
ple, we would like to know which of the following complexity classes
contain BPP:

Deﬁnition 3.1 (Deterministic Time Classes). 1

DTIME(t(n)) = {L : L can be decided deterministically

in time O(t(n))}

P = ∪cDTIME(nc)
˜P = ∪cDTIME(2(log n)c

)

SUBEXP = ∩εDTIME(2nε
EXP = ∪cDTIME(2nc

)

)

(“polynomial time”)

(“quasipolynomial time”)

(“subexponential time”)

(“exponential time”)

The “Time Hierarchy Theorem” of complexity theory implies that
all of these classes are distinct, i.e., P (cid:1) ˜P (cid:1) SUBEXP (cid:1) EXP. More
generally, it says that DTIME(O(t(n)/ log t(n))) (cid:1) DTIME(t(n)) for
any eﬃciently computable time bound t. (What is diﬃcult in complex-
ity theory is separating classes that involve diﬀerent computational
resources, like deterministic time versus nondeterministic time.)

Enumeration is a derandomization technique that enables us to
deterministically simulate any randomized algorithm with an exponen-
tial slowdown.

Proposition 3.2. BPP ⊂ EXP.

1 Often DTIME(·) is written as TIME(·), but we include the D to emphasize that it
refers to deterministic rather than randomized algorithms. Also, in some contexts (e.g.,
cryptography), “exponential time” refers to DTIME(2O(n)) and “subexponential time”
to be DTIME(2o(n)); we will use E to denote the former class when it arises in Section 7.



<!-- pdf-page: 55 -->
52 Basic Derandomization Techniques

Proof. If L is in BPP, then there is a probabilistic polynomial-time
algorithm A for L running in time t(n) for some polynomial t. As
in the proof of Theorem 2.30, we write A(x; r) for As output on input
x ∈ {0, 1}n and coin tosses r ∈ {0, 1}m(n), where we may assume m(n) ≤
t(n) without loss of generality. Then:

Pr[A(x; r) accepts] =

1
2m(n)

(cid:3)

A(x; r)

r∈{0,1}m(n)

We can compute the right-hand side of the above expression in deter-
ministic time 2m(n) · t(n).

We see that the enumeration method is general in that it applies
to all BPP algorithms, but it is infeasible (taking exponential time).
However, if the algorithm uses only a small number of random bits, it
becomes feasible:

Proposition 3.3.
If L has a probabilistic polynomial-time algo-
rithm that runs in time t(n) and uses m(n) random bits, then L ∈
DTIME(t(n) · 2m(n)). In particular,
if t(n) = poly(n) and m(n) =
O(log n), then L ∈ P.

Thus an approach to proving BPP = P is to show that the number
of random bits used by any BPP algorithm can be reduced to O(log n).
We will explore this approach in Section 7. However, to date, Propo-
sition 3.2 remains the best unconditional upper-bound we have on the
deterministic time-complexity of BPP.

Open Problem 3.4. Is BPP “closer” to P or EXP? Is BPP ⊂ ˜P?
Is BPP ⊂ SUBEXP?

3.2 Nonconstructive/Nonuniform Derandomization

Next we look at a derandomization technique that can be implemented
eﬃciently but requires some nonconstructive “advice” that depends on
the input length.



<!-- pdf-page: 56 -->
3.2 Nonconstructive/Nonuniform Derandomization

53

Proposition 3.5. If A(x; r) is a randomized algorithm for a language
L that has error probability smaller than 2−n on inputs x of length n,
then for every n, there exists a ﬁxed sequence of coin tosses rn such
that A(x; rn) is correct for all x ∈ {0, 1}n.

Proof. We use the Probabilistic Method. Consider Rn chosen uniformly
at random from {0, 1}r(n), where r(n) is the number of coin tosses used
by A on inputs of length n. Then

Pr[∃x ∈ {0, 1}n s.t. A(x; Rn) incorrect on x]

(cid:3)

≤

Pr[A(x; Rn) incorrect on x]

x

< 2n · 2−n = 1

Thus, there exists a ﬁxed value Rn = rn that yields a correct answer
for all x ∈ {0, 1}n.

The advantage of this method over enumeration is that once we
have the ﬁxed string rn, computing A(x; rn) can be done in polynomial
time. However, the proof that rn exists is nonconstructive; it is not
clear how to ﬁnd it in less than exponential time.

Note that we know that we can reduce the error probability of
any BPP (or RP, RL, RNC, etc.) algorithm to smaller than 2−n by
repetitions, so this proposition is always applicable. However, we begin
by looking at some interesting special cases.

i,j = xi,j if (i, j) ∈ E, and AG

Example 3.6 (Perfect Matching). We apply the proposition to
Algorithm 2.7. Let G = (V, E) be a bipartite graph with m vertices
on each side, and let AG(x1,1, . . . , xm,m) be the matrix that has entries
i,j = 0 if (i, j) (cid:1)∈ E. Recall that the poly-
AG
nomial det(AG(x)) is nonzero if and only if G has a perfect matching.
Let Sm = {0, 1, 2, . . . , m2m2}. We argued that, by the Schwartz–Zippel
Lemma, if we choose α R← Sm2
m at random and evaluate det(AG(α)),
we can determine whether det(AG(x)) is zero with error probability at
most m/|S| which is smaller than 2−m2
. Since a bipartite graph with m



<!-- pdf-page: 57 -->
54 Basic Derandomization Techniques

vertices per side is speciﬁed by a string of length n = m2, by Proposi-
tion 3.5 we know that for every m, there exists an αm ∈ Sm2
m such that
det(AG(αm)) (cid:1)= 0 if and only if G has a perfect matching, for every
bipartite graph G with m vertices on each side.

Open Problem 3.7. Can we ﬁnd such an αm ∈ {0, . . . , m2m2}m2
explicitly, i.e., deterministically and eﬃciently? An NC algorithm (i.e.,
parallel time polylog(m) with poly(m) processors) would put Perfect
Matching in deterministic NC, but even a subexponential-time algo-
rithm would be interesting.

Example 3.8 (Universal Traversal Sequences). Let G be a con-
nected d-regular undirected multigraph on n vertices. From Theo-
rem 2.49, we know that a random walk of poly(n, d) steps from any
start vertex will visit any other vertex with high probability. By increas-
ing the length of the walk by a polynomial factor, we can ensure
that every vertex is visited with probability greater than 1 − 2−nd log n.
By the same reasoning as in the previous example, we conclude that
for every pair (n, d), there exists a universal traversal sequence w ∈
{1, 2, . . . , d}poly(n,d) such that for every n-vertex, d-regular, connected
G and every vertex s in G, if we start from s and follow w then we will
visit the entire graph.

Open Problem 3.9. Can we construct such a universal traversal
sequence explicitly (e.g., in polynomial time or even logarithmic space)?

There has been substantial progress toward resolving this question

in the positive; see Section 4.4.

We now cast the nonconstructive derandomizations provided by

Proposition 3.5 in the language of “nonuniform” complexity classes.

Deﬁnition 3.10. Let C be a class of languages, and a : N → N be a
function. Then C/a is the class of languages deﬁned as follows: L ∈ C/a



<!-- pdf-page: 58 -->
3.2 Nonconstructive/Nonuniform Derandomization

55

if there exists L(cid:3) ∈ C, and α1, α2, . . . ∈ {0, 1}∗ with |αn| ≤a(n), such
that x ∈ L ⇔ (x, α|x|) ∈ L(cid:3). The αs are called the advice strings.

(cid:8)

c P/nc, i.e., polynomial time with polynomial

P/poly is the class

advice.

A basic result in complexity theory is that P/poly is exactly the
class of languages that can be decided by polynomial-sized Boolean
circuits:

Fact 3.11. L ∈ P/poly iﬀ there is a sequence of Boolean circuits
{Cn}n∈N and a polynomial p such that for all n

(1) Cn : {0, 1}n → {0, 1} decides L ∩ {0, 1}n
(2) |Cn| ≤p(n).

We refer to P/poly as a “nonuniform” model of computation
because it allows for diﬀerent, unrelated “programs” for each input
length (e.g., the circuits Cn, or the advice αn), in contrast to classes
like P, BPP, and NP, that require a single “program” of constant
size specifying how the computation should behave for inputs of arbi-
trary length. Although P/poly contains some undecidable problems,2
people generally believe that NP (cid:1)⊂ P/poly. Indeed, trying to prove
lower bounds on circuit size is one of the main approaches to proving
P (cid:1)= NP, since circuits seem much more concrete and combinatorial
than Turing machines. However, this too has turned out to be quite
diﬃcult; the best circuit lower bound known for computing an explicit
function is roughly 5n.

Proposition 3.5 directly implies:

Corollary 3.12. BPP ⊂ P/poly.

A more general meta-theorem is that “nonuniformity is more pow-

erful than randomness.”

2 Consider the unary version of the Halting Problem, which can be decided in constant
time given advice αn ∈ {0, 1} that speciﬁes whether the nth Turing machine halts or not.



<!-- pdf-page: 59 -->
56 Basic Derandomization Techniques

3.3 Nondeterminism

Although physically unrealistic, nondeterminism has proven to be a
very useful resource in the study of computational complexity (e.g.,
leading to the class NP). Thus it is natural to study how it compares
in power to randomness. Intuitively, with nondeterminism we should
be able to guess a “good” sequence of coin tosses for a randomized
algorithm and then do the computation deterministically. This intuition
does apply directly for randomized algorithms with 1-sided error:

Proposition 3.13. RP ⊂ NP.

Proof. Let L ∈ RP and A be a randomized algorithm that decides it.
A polynomial-time veriﬁable witness that x ∈ L is any sequence of coin
tosses r such that A(x; r) = accept.

However, for 2-sided error (BPP), containment in NP is not clear.
Even if we guess a “good” random string (one that leads to a correct
answer), it is not clear how we can verify it in polynomial time. Indeed,
it is consistent with current knowledge that BPP equals NEXP (non-
deterministic exponential time)! Nevertheless, there is a sense in which
we can show that BPP is no more powerful than NP:

Theorem 3.14. If P = NP, then P = BPP.

Proof. For any language L ∈ BPP, we will show how to express mem-
bership in L using two quantiﬁers. That is, for some polynomial-time
predicate P ,

x ∈ L ⇐⇒ ∃y∀ z P (x, y, z),

(3.1)

where we quantify over y and z of length poly(|x|).

Assuming P = NP, we can replace ∀ z P (x, y, z) by a polynomial-
time predicate Q(x, y), because the language {(x, y) :∀ z P (x, y, z)} is
in co-NP = P. Then L = {x : ∃y Q(x, y)} ∈NP = P.

To obtain the two-quantiﬁer expression (3.1), consider a randomized
algorithm A for L, and assume w.l.o.g. that its error probability



<!-- pdf-page: 60 -->
3.3 Nondeterminism 57

is smaller than 2−n and that it uses m = poly(n) coin tosses. Let
Ax ⊂ {0, 1}m be the set of coin tosses r for which A(x; r) = 1. We will
show that if x is in L, there exist m “shifts” (or “translations”) of Ax
that cover all points in {0, 1}m. (Notice that this is a ∃∀ statement.)
Intuitively, this should be possible because Ax contains all but an expo-
nentially small fraction of {0, 1}m. On the other hand if x /∈ L, then no
m shifts of Ax can cover all of {0, 1}m. Intuitively, this is because Ax
is an exponentially small fraction of {0, 1}m.

Formally, by a “shift of Ax” we mean a set of the form Ax ⊕ s =
{r ⊕ s : r ∈ Ax} for some s ∈ {0, 1}m; note that |Ax ⊕ s| = |Ax|. We
will show

x ∈ L ⇒ ∃s1, s2, . . . , sm ∈ {0, 1}m∀ r ∈ {0, 1}m r ∈

m(cid:9)

i=1

(Ax ⊕ si)

⇔ ∃s1, s2, . . . , sm ∈ {0, 1}m ∀ r ∈ {0, 1}m

m(cid:10)

i=1

(A(x; r ⊕ si) = 1);

x /∈ L ⇒ ∀ s1, s2, . . . , sm ∈ {0, 1}m ∃r ∈ {0, 1}m r /∈

m(cid:9)

i=1

(Ax ⊕ si)

⇔ ∀ s1, s2, . . . , sm ∈ {0, 1}m ∃r ∈ {0, 1}m ¬

m(cid:10)

i=1

(A(x; r ⊕ si) = 1).

We prove both parts by the Probabilistic Method, starting with the
second (which is simpler).

x /∈ L Let s1, . . . , sm be arbitrary, and choose R R← {0, 1}m at ran-
dom. Now Ax and hence each Ax ⊕ si contains less than a
2−n fraction of {0, 1}m. So, by a union bound,

Pr[R ∈

(cid:9)

(Ax ⊕ si)] ≤

i

(cid:3)

i

Pr[R ∈ Ax ⊕ si]

< m · 2−n < 1,

for suﬃciently large n. In particular, there exists an r ∈
{0, 1}m such that r /∈
i(Ax ⊕ si).

(cid:8)



<!-- pdf-page: 61 -->
58 Basic Derandomization Techniques

x ∈ L: Choose S1, S2, . . . , Sm

R← {0, 1}m. Then, for every ﬁxed r, we

have:

Pr[r /∈

(cid:9)

(Ax ⊕ Si)] =

i

(cid:5)

i
(cid:5)

=

Pr[r /∈ Ax ⊕ Si]

Pr[Si /∈ Ax ⊕ r]

i
< (2−n)m,

since Ax and hence Ax ⊕ r contains more than a 1 − 2−n
fraction of {0, 1}m. By a union bound, we have:

(cid:9)

Pr[∃r

r /∈

(Ax ⊕ Si)] < 2m · (2−n)m ≤ 1.

i

Thus, there exist s1, . . . , sm such that
all points r in {0, 1}m.

(cid:8)

i(Ax ⊕ si) contains

Readers familiar with complexity theory might notice that the
above proof shows that BPP is contained in the second level of the
polynomial-time hierarchy (PH). In general, the kth level of the PH
contains all languages that satisfy a k-quantiﬁer expression analogous
to (3.1).

3.4 The Method of Conditional Expectations

In the previous sections, we saw several derandomization techniques
(enumeration, nonuniformity, nondeterminism) that are general in the
sense that they apply to all of BPP, but are infeasible in the sense
that they cannot be implemented by eﬃcient deterministic algorithms.
In this section and the next one, we will see two derandomization tech-
niques that sometimes can be implemented eﬃciently, but do not apply
to all randomized algorithms.

3.4.1 The General Approach

Consider a randomized algorithm that uses m random bits. We can
view all its sequences of coin tosses as corresponding to a binary tree



<!-- pdf-page: 62 -->
3.4 The Method of Conditional Expectations

59

of depth m. We know that most paths (from the root to the leaf) are
“good,” that is, give a correct answer. A natural idea is to try and ﬁnd
such a path by walking down from the root and making “good” choices
at each step. Equivalently, we try to ﬁnd a good sequence of coin tosses
“bit-by-bit.”

To make this precise, ﬁx a randomized algorithm A and an input
x, and let m be the number of random bits used by A on input x.
For 1 ≤ i ≤ m and r1, r2, . . . , ri ∈ {0, 1}, deﬁne P (r1, r2, . . . , ri) to be the
fraction of continuations that are good sequences of coin tosses. More
precisely, if R1, . . . , Rm are uniform and independent random bits, then

P (r1, r2, . . . , ri) def=

[A(x; R1, R2, . . . , Rm) is correct

Pr
R1,R2,...,Rm
|R1 = r1, R2 = r2, . . . , Ri = ri]

= E
Ri+1

[P (r1, r2, . . . , ri, Ri+1)].

(See Figure 3.1.)

By

there

averaging,

that
P (r1, r2, . . . , ri, ri+1) ≥ P (r1, r2, . . . , ri). So
(r1, r2, . . . , ri),
we simply pick ri+1 that maximizes P (r1, r2, . . . , ri, ri+1). At the end
we have r1, r2, . . . , rm, and

ri+1 ∈ {0, 1}
at node

exists

such

an

P (r1, r2, . . . , rm) ≥ P (r1, r2, . . . , rm−1) ≥ · · · ≥ P (r1) ≥ P (Λ) ≥ 2/3,

0

1

0

1

0

1

P(0,1)=7/8

o

o x o o o o o

Fig. 3.1 An example of P (r1, r2), where “o” at the leaf denotes a good path.



<!-- pdf-page: 63 -->
60 Basic Derandomization Techniques

where P (Λ) denotes the fraction of good paths from the root. Then
P (r1, r2, . . . , rm) = 1, since it is either 1 or 0.

Note that to implement this method, we need to compute
P (r1, r2, . . . , ri) deterministically, and this may be infeasible. However,
there are nontrivial algorithms where this method does work, often for
search problems rather than decision problems, and where we measure
not a boolean outcome (e.g., whether A is correct as above) but some
other measure of quality of the output. Below we see one such example,
where it turns out to yield a natural “greedy algorithm.”

3.4.2 Derandomized MAXCUT Approximation

Recall the MaxCutproblem:

Computational Problem 3.15 (Computational Problem 2.38,
rephrased). MaxCut: Given a graph G = (V, E), ﬁnd a partition
S, T of V (i.e., S ∪ T = V , S ∩ T = ∅) maximizing the size of the set
cut(S, T ) ={{u, v } ∈E : u ∈ S, v ∈ T }.

We saw a simple randomized algorithm that ﬁnds a cut of (expected)
size at least |E|/2 (not counting any self-loops, which can never be cut),
which we now phrase in a way suitable for derandomization.

Algorithm 3.16 (randomized MaxCut, rephrased).
Input: A graph G = ([N ], E) (with no self-loops)

Flip N coins r1, r2, . . . , rN , put vertex i in S if ri = 0 and in T if
ri = 1. Output (S, T ).

To derandomize this algorithm using the Method of Conditional

Expectations, deﬁne the conditional expectation

e(r1, r2, . . . , ri) def=

E
R1,R2,...,RN

(cid:11)

(cid:12)
(cid:12)
|cut(S, T )|
(cid:12)R1 = r1, R2 = r2, . . . , Ri = ri

(cid:13)

to be the expected cut size when the random choices for the ﬁrst i coins
are ﬁxed to r1, r2, . . . , ri.



<!-- pdf-page: 64 -->
3.4 The Method of Conditional Expectations

61

We know that when no random bits are ﬁxed, e[Λ] = |E|/2 (because
each edge is cut with probability 1/2), and all we need to calculate is
e(r1, r2, . . . , ri) for 1 ≤ i ≤ N . For this particular algorithm it turns out
def= {j : j ≤ i, rj = 0}
that the quantity is not hard to compute. Let Si
def= {j : j ≤ i, rj = 1}) be the set of vertices in S (resp. T ) after
(resp. Ti
def= {i + 1, i + 2, . . . , N } be the “unde-
we determine r1, . . . , ri, and Ui
cided” vertices that have not been put into S or T . Then

e(r1, r2, . . . , ri) =|cut(S i, Ti)| + 1/2(|cut(Ui, [N ])|).

(3.2)

Note that cut(Ui, [N ]) is the set of unordered edges that have at least
one endpoint in Ui. Now we can deterministically select a value for ri+1,
by computing and comparing e(r1, r2, . . . , ri, 0) and e(r1, r2, . . . , ri, 1).

independent of

In fact, the decision on ri+1 can be made even simpler than com-
puting (3.2) in its entirety, by observing that the set cut(Ui+1, [N ])
is
to maximize
e(r1, r2 . . . , ri, ri+1), it is enough to choose ri+1 that maximizes the
|cut(S, T )| term. This term increases by either |cut({i + 1}, Ti)| or
|cut({i + 1}, Si)| depending on whether we place vertex i + 1 in S or
T , respectively. To summarize, we have

the choice of ri+1. Therefore,

e(r1, . . . , ri, 0) − e(r1, . . . , ri, 1) = |cut({i + 1}, Ti)| − |cut({i + 1}, Si)|.

This gives rise to the following deterministic algorithm, which is guar-
anteed to always ﬁnd a cut of size at least |E|/2:

Algorithm 3.17 (deterministic MaxCut approximation).
Input: A graph G = ([N ], E) (with no self-loops)

(1) Set S = ∅, T = ∅
(2) For i = 0, . . . , N − 1:

(a) If |cut({i + 1}, T )| > |cut({i + 1}, S)|, set S ← S ∪

{i + 1},

(b) Else set T ← T ∪ {i + 1}.

Note that this is the natural “greedy” algorithm for this problem. In
other cases, the Method of Conditional Expectations yields algorithms



<!-- pdf-page: 65 -->
62 Basic Derandomization Techniques

that, while still arguably “greedy,” would have been much less easy to
ﬁnd directly. Thus, designing a randomized algorithm and then trying
to derandomize it can be a useful paradigm for the design of deter-
ministic algorithms even if the randomization does not provide gains
in eﬃciency.

3.5 Pairwise Independence

3.5.1 An Example

As a motivating example for pairwise independence, we give another
way of derandomizing the MaxCut approximation algorithm discussed
above. Recall the analysis of the randomized algorithm:
Pr[Ri (cid:1)= Rj] =|E |/2,

E[|cut(S)|] =

(cid:3)

(i,j)∈E

where R1, . . . , RN are the random bits of the algorithm. The key obser-
vation is that this analysis applies for any distribution on (R1, . . . , RN )
satisfying Pr[Ri (cid:1)= Rj] = 1/2 for each i (cid:1)= j. Thus, they do not need to
be completely independent random variables; it suﬃces for them to be
pairwise independent. That is, each Ri is an unbiased random bit, and
for each i (cid:1)= j, Ri is independent from Rj.

This leads to the question: Can we generate N pairwise independent
bits using less than N truly random bits? The answer turns out to be
yes, as illustrated by the following construction.

Construction 3.18 (pairwise independent bits). Let B1, . . . , Bk
be k independent unbiased random bits. For each nonempty S ⊂ [k],
let RS be the random variable ⊕i∈SBi, where ⊕ denotes XOR.

Proposition 3.19. The 2k − 1 random variables RS in Construc-
tion 3.18 are pairwise independent unbiased random bits.

Proof. It is evident that each RS is unbiased. For pairwise indepen-
dence, consider any two nonempty sets S (cid:1)= T ⊂ [k]. Then:

RS = RS∩T ⊕ RS\T
RT = RS∩T ⊕ RT \S.



<!-- pdf-page: 66 -->
3.5 Pairwise Independence

63

Note that RS∩T , RS\T , and RT \S are independent as they depend
on disjoint subsets of the Bis, and at least two of these subsets are
nonempty. This implies that (RS, RT ) takes each value in {0, 1}2 with
probability 1/4.

Note that this gives us a way to generate N pairwise independent
bits from (cid:15)log(N + 1)(cid:16) independent random bits. Thus, we can reduce
the randomness required by the MaxCut algorithm to logarithmic,
and then we can obtain a deterministic algorithm by enumeration.

Algorithm 3.20 (deterministic MaxCut algorithm II).
Input: A graph G = ([N ], E) (with no self-loops)

For all sequences of bits b1, b2, . . . , b(cid:9)log(N +1)(cid:10), run the random-
ized MaxCut algorithm using coin tosses (rS = ⊕i∈Sbi)S(cid:11)=∅ and
choose the largest cut thus obtained.

Since there are at most 2(N + 1) sequences of bis, the deran-
domized algorithm still runs in polynomial time. It is slower than
the algorithm we obtained by the Method of Conditional Expecta-
tions (Algorithm 3.17), but it has the advantage of using logarithmic
workspace and being parallelizable. The derandomization can be sped
up using almost pairwise independence (at the price of a slightly worse
approximation factor); see Problem 3.4.

3.5.2 Pairwise Independent Hash Functions

Some applications require pairwise independent random variables that
take values from a larger range, for example, we want N = 2n pair-
wise independent random variables, each of which is uniformly dis-
tributed in {0, 1}m = [M ]. (Throughout this survey, we will often use
the convention that a lowercase letter equals the logarithm (base 2)
of the corresponding capital letter.) The naive approach is to repeat
the above algorithm for the individual bits m times. This uses roughly
n · m = (log M )(log N ) initial random bits, which is no longer logarith-
mic in N if M is nonconstant. Below we will see that we can do much
better. But ﬁrst some deﬁnitions.



<!-- pdf-page: 67 -->
64 Basic Derandomization Techniques

A sequence of N random variables each taking a value in [M ] can be
viewed as a distribution on sequences in [M ]N . Another interpretation
of such a sequence is as a mapping f : [N ] → [M ]. The latter interpre-
tation turns out to be more useful when discussing the computational
complexity of the constructions.

Deﬁnition 3.21 (pairwise independent hash functions). A
family (i.e., multiset) of functions H = {h : [N ] → [M ]} is pairwise inde-
pendent if the following two conditions hold when H R← H is a function
chosen uniformly at random from H:

(1) ∀ x ∈ [N ], the random variable H(x) is uniformly distributed

in [M ].

(2) ∀ x1 (cid:1)= x2 ∈ [N ], the random variables H(x1) and H(x2) are

independent.

Equivalently, we can combine the two conditions and require that

[H(x1) =y 1 ∧ H(x2) =y 2] =

∀ x1 (cid:1)= x2 ∈ [N ], ∀ y1, y2 ∈ [M ], Pr
R←H

1
M 2 .
Note that the probability above is over the random choice of a function
from the family H. This is why we talk about a family of functions
rather than a single function. The description in terms of functions
makes it natural to impose a strong eﬃciency requirement:

H

Deﬁnition 3.22. A family of functions H = {h : [N ] → [M ]} is explicit
if given the description of h and x ∈ [N ], the value h(x) can be com-
puted in time poly(log N, log M ).

Pairwise independent hash functions are sometimes referred to as
strongly 2-universal hash functions, to contrast with the weaker notion
of 2-universal hash functions, which requires only that Pr[H(x1) =
H(x2)] ≤ 1/M for all x1 (cid:1)= x2. (Note that this property is all we needed
for the deterministic MaxCut algorithm, and it allows for a small sav-
ings in that we can also include S = ∅ in Construction 3.18.)

Below we present another construction of a pairwise independent

family.



<!-- pdf-page: 68 -->
3.5 Pairwise Independence

65

Construction 3.23 (pairwise independent hash functions from
linear maps). Let F be a ﬁnite ﬁeld. Deﬁne the family of functions
H = { ha,b : F → F}a,b∈F where ha,b(x) =ax + b.

Proposition 3.24. The family of functions H in Construction 3.23 is
pairwise independent.

Proof. Notice that the graph of the function ha,b(x) is the line with
slope a and y-intercept b. Given x1 (cid:1)= x2 and y1, y2, there is exactly
one such line containing the points (x1, y1) and (x2, y2) (namely, the
line with slope a = (y1 − y2)/(x1 − x2) and y-intercept b = y1 − ax1).
Thus, the probability over a, b that ha,b(x1) =y 1 and ha,b(x2) =y 2
equals the reciprocal of the number of lines, namely 1/|F|2.

This construction uses 2 log |F| random bits, since we have to choose
R← H. Compare this to
a and b at random from F to get a function ha,b
|F| log |F| bits required to choose a truly random function, and (log |F|)2
bits for repeating the construction of Proposition 3.19 for each output
bit.

Note that evaluating the functions of Construction 3.23 requires
a description of the ﬁeld F that enables us to perform addition and
multiplication of ﬁeld elements. Thus we take a brief aside to review
the complexity of constructing and computing in ﬁnite ﬁelds.

Remark 3.25 (constructing ﬁnite ﬁelds). Recall that for every
prime power q = pk there is a ﬁeld Fq (often denoted GF(q)) of size
q, and this ﬁeld is unique up to isomorphism (renaming elements). The
prime p is called the characteristic of the ﬁeld. Fq has a description
of length O(log q) enabling addition, multiplication, and division to be
performed in polynomial time (i.e., time poly(log q)). (This description
is simply an irreducible polynomial f of degree k over Fp = Zp.) To
construct this description, we ﬁrst need to determine the characteris-
tic p; ﬁnding a prime p of a desired bitlength (cid:6) can be done proba-
bilistically in time poly((cid:6)) = poly(log p) and deterministically in time



<!-- pdf-page: 69 -->
66 Basic Derandomization Techniques

poly(2(cid:4)) = poly(p). Then given p and k, a description of Fq (for q = pk)
can be found probabilistically in time poly(log p, k) = poly(log q) and
deterministically in time poly(p, k). Note that for both steps, the deter-
ministic algorithms are exponential in the bitlength of the characteris-
tic p. Thus, for computational purposes, a convenient choice is often to
instead take p = 2 and k large, in which case everything can be done
deterministically in time poly(k) = poly(log q).

Using a ﬁnite ﬁelds of size 2n as suggested above, we obtain an
explicit construction of pairwise independent hash functions Hn,n =
{h : {0, 1}n → {0, 1}n} for every n. What if we want a family Hn,m
of pairwise independent hash functions where the input length n and
output length m are not equal? For n < m, we can take hash functions
h from Hm,m and restrict their domain to {0, 1}n by deﬁning h(cid:3)(x) =
h(x ◦ 0m−n). In the case that m < n, we can take h from Hn,n and
throw away n − m bits of the output. That is, deﬁne h(cid:3)(x) =h(x )|m,
where h(x)|m denotes the ﬁrst m bits of h(x).

In both cases, we use 2 max{n, m} random bits. This is the best
possible when m ≥ n. When m < n, it can be reduced to m + n ran-
dom bits by using (ax)|m + b where b ∈ {0, 1}m instead of (ax + b)|m.
Summarizing:

Theorem 3.26. For every n, m ∈ N, there is an explicit family of
pairwise independent functions Hn,m = {h : {0, 1}n → {0, 1}m} where
a random function from Hn,m can be selected using max{m, n} + m
random bits.

Problem 3.5 shows that max{m, n} + m random bits is essentially

optimal.

3.5.3 Hash Tables

The original motivating application for pairwise independent functions
was for hash tables. Suppose we want to store a set S ⊂ [N ] of values
and answer queries of the form “Is x ∈ S?” eﬃciently (or, more gener-
ally, acquire some piece of data associated with key x in case x ∈ S).



<!-- pdf-page: 70 -->
3.5 Pairwise Independence

67

A simple solution is to have a table T such that T [x] = 1 if and
only if x ∈ S. But this requires N bits of storage, which is ineﬃcient
if |S|  N .

A better solution is to use hashing. Assume that we have a hash
function h : [N ] → [M ] for some M to be determined later. Let T be a
table of size M , initially empty. For each x ∈ [N ], we let T [h(x)] = x if
x ∈ S. So to test whether a given y ∈ S, we compute h(y) and check if
T [h(y)] = y. In order for this construction to be well-deﬁned, we need h
to be one-to-one on the set S. Suppose we choose a random function H
from [N ] to [M ]. Then, for any set S of size at most K, the probability
that there are any collisions is

Pr[∃ x (cid:1)= y s.t. H(x) =H (y)] ≤

= H(y)] ≤

(cid:3)

Pr[H(x)

x(cid:11)=y∈S
(cid:15)
(cid:14)

K
2

· 1
M

< ε

for M = K2/ε. Notice that the above analysis does not require H to be
a completely random function; it suﬃces that H be pairwise indepen-
dent (or even 2-universal). Thus using Theorem 3.26, we can generate
and store H using O(log N ) random bits. The storage required for the
table T is O(M log N ) =O (K2 log N ) bits, which is much smaller than
N when K = N o(1). Note that to uniquely represent a set of size K,
= Ω(K log N ) (when K ≤ N 0.99). In fact,
we need space at least log
there is a data structure achieving a matching space upper bound of
O(K log N ), which works by taking M = O(K) in the above construc-
tion and using additional hash functions to separate the (few) collisions
that will occur.

N
K

(cid:1)

(cid:2)

Often, when people analyze applications of hashing in computer sci-
ence, they model the hash function as a truly random function. How-
ever, the domain of the hash function is often exponentially large, and
thus it is infeasible to even write down a truly random hash function.
Thus, it would be preferable to show that some explicit family of hash
function works for the application with similar performance. In many
cases (such as the one above), it can be shown that pairwise indepen-
dence (or k-wise independence, as discussed below) suﬃces.



<!-- pdf-page: 71 -->
68 Basic Derandomization Techniques

3.5.4 Randomness-Eﬃcient Error Reduction and Sampling

Suppose we have a BPP algorithm for a language L that has a constant
error probability. We want to reduce the error to 2−k. We have already
seen that this can be done using O(k) independent repetitions (by a
Chernoﬀ Bound). If the algorithm originally used m random bits, then
we use O(km) random bits after error reduction. Here we will see how
to reduce the number of random bits required for error reduction by
doing repetitions that are only pairwise independent.

To analyze this, we will need an analogue of the Chernoﬀ Bound
(Theorem 2.21) that applies to averages of pairwise independent ran-
dom variables. This will follow from Chebyshev’s Inequality, which
bounds the deviations of a random variable X from its mean µ in
terms its variance Var[X] = E[(X − µ)2] = E[X 2] − µ2.

Lemma 3.27 (Chebyshev’s Inequality). If X is a random variable
with expectation µ, then

Pr[|X − µ| ≥ε] ≤ Var[X]

ε2

Proof. Applying Markov’s Inequality (Lemma 2.20) to the random vari-
able Y = (X − µ)2, we have:
Pr[|X − µ| ≥ε] = Pr[( X − µ)2 ≥ ε2] ≤ E[(X − µ)2]

=

.

ε2

Var[X]
ε2

We now use this to show that a sum of pairwise independent random

variables is concentrated around its expectation.

Proposition 3.28 (Pairwise Independent Tail Inequality). Let
X1, . . . , Xt be pairwise independent random variables taking values in
the interval [0, 1], let X = (

i Xi)/t, and µ = E[X]. Then

(cid:4)

Pr[|X − µ| ≥ε] ≤ 1
tε2 .



<!-- pdf-page: 72 -->
Proof. Let µi = E[Xi]. Then
(cid:17)

(cid:16)

Var[X] = E

(X − µ)2

(cid:20)

(cid:3)

3.5 Pairwise Independence

69

(cid:21)
2





(Xi − µi)

i

E[(Xi − µi)(Xj − µj)]

E[(Xi − µi)2]

(by pairwise independence)

Var[Xi]

=

=

=

=

1
t2

1
t2

1
t2

1
t2



· E

·

·

·

(cid:3)

i,j
(cid:3)

i
(cid:3)

i

≤ 1
t

Now apply Chebyshev’s Inequality.

While this requires less independence than the Chernoﬀ Bound, notice
that the error probability decreases only linearly rather than exponen-
tially with the number t of samples.

Error Reduction. Proposition 3.28 tells us that if we use t = O(2k)
pairwise independent repetitions, we can reduce the error proba-
bility of a BPP algorithm from 1/3 to 2−k. If the original BPP
algorithm uses m random bits, then we can do this by choosing
h : {0, 1}k+O(1) → {0, 1}m at random from a pairwise independent
family, and running the algorithm using coin tosses h(x) for all
x ∈ {0, 1}k+O(1). This
requires m + max{m, k + O(1)} = O(m + k)
random bits.

Number of
Repetitions Random Bits

Number of

Independent Repetitions
Pairwise Independent Repetitions

O(k)
O(2k)

O(km)
O(m + k)



<!-- pdf-page: 73 -->
70 Basic Derandomization Techniques

Note that we saved substantially on the number of random bits,
but paid a lot in the number of repetitions needed. To maintain a
polynomial-time algorithm, we can only aﬀord k = O(log n). This set-
ting implies that if we have a BPP algorithm with constant error
that uses m random bits, we have another BPP algorithm that uses
O(m + log n) =O (m) random bits and has error 1/poly(n). That is,
we can go from constant to inverse-polynomial error only paying a con-
stant factor in randomness. (In fact, it turns out there is a way to
achieve this with no penalty in randomness; see Problem 4.6.)

Sampling. Recall the Sampling problem: Given oracle access to a
function f : {0, 1}m → [0, 1], we want to approximate µ(f ) to within an
additive error of ε.

In Section 2.3.1, we saw that we can solve this problem with
probability 1 − δ by outputting the average of f on a random
sample of t = O(log(1/δ)/ε2) points in {0, 1}m, where the correct-
ness follows from the Chernoﬀ Bound. To reduce the number of
truly random bits used, we can use a pairwise independent sample
instead. Speciﬁcally, taking t = 1/(ε2δ) pairwise independent points,
we get an error probability of at most δ (by Proposition 3.28). To
generate t pairwise independent samples of m bits each, we need
O(m + log t) =O (m + log(1/ε) + log(1/δ)) truly random bits.

Number of
Samples

Number of
Random Bits

Truly Random Sample O((1/ε2) · log(1/δ))

Pairwise Independent

O((1/ε2) · (1/δ))

Repetitions

O(m · (1/ε2)
· log(1/δ))
O(m + log(1/ε)
+ log(1/δ))

Both of these sampling algorithms have a natural restricted structure.
First, they choose all of their queries to the oracle f nonadaptively,
based solely on their coin tosses and not based on the answers to pre-
vious queries. Second, their output is simply the average of the queried



<!-- pdf-page: 74 -->
values, whereas the original sampling problem does not constrain the
output function. It is useful to abstract these properties as follows.

3.5 Pairwise Independence

71

Deﬁnition 3.29. A sampler Samp for domain size M is given “coin
tosses” x R← [N ] and outputs a sequence of samples z1, . . . , zt ∈ [M ]. We
say that Samp : [N ] → [M ]t is a (δ, ε) averaging sampler if for every
function f : [M ] → [0, 1], we have

(cid:25)

Pr
R←Samp(U[N ])

(z1,...,zt)

t(cid:3)

(cid:24)

1
t

f (zi) > µ(f ) +ε

≤ δ.

(3.3)

i=1
If Inequality 3.3 only holds for f with (boolean) range {0, 1}, we call
Samp a boolean averaging sampler. We say that Samp is explicit if given
x ∈ [N ] and i ∈ [t], Samp(x)i can be computed in time poly(log N, log t).

We note that, in contrast to the Chernoﬀ Bound (Theorem 2.21)
and the Pairwise Independent Tail Inequality (Proposition 3.28), this
deﬁnition seems to only provide an error guarantee in one direction,
namely that the sample average does not signiﬁcantly exceed the global
average (except with small probability). However, a guarantee in the
other direction also follows by considering the function 1 − f . Thus,
up to a factor of 2 in the failure probability δ, the above deﬁnition
is equivalent to requiring that Pr[|(1/t) ·
i f (zi) − µ(f )| > ε] ≤ δ. We
choose to use a one-sided guarantee because it will make the connection
to list-decodable codes (in Section 5) slightly cleaner.

(cid:4)

Our pairwise-independent sampling algorithm can now be described

as follows:

Theorem 3.30 (Pairwise Independent Sampler). For every
m ∈ N and δ, ε ∈ [0, 1], there is an explicit (δ, ε) averaging sampler
Samp : {0, 1}n → ({0, 1}m)t using n = O(m + log(1/ε) + log(1/δ)) ran-
dom bits and t = O(1/(ε2δ)) samples.

As we will see in subsequent sections, averaging samplers are inti-
mately related to the other pseudorandom objects we are studying
(especially randomness extractors). In addition, some applications of
samplers require samplers of this restricted form.



<!-- pdf-page: 75 -->
72 Basic Derandomization Techniques

3.5.5 k-wise Independence

Our deﬁnition and construction of pairwise independent functions gen-
eralize naturally to k-wise independence for any k.

Deﬁnition 3.31 (k-wise independent hash functions). For
N, M, k ∈ N such that k ≤ N , a family of functions H = {h : [N ] →
[M ]} is k-wise independent if for all distinct x1, x2, . . . , xk ∈ [N ], the
random variables H(x1), . . . , H(xk) are independent and uniformly dis-
tributed in [M ] when H R← H.

Construction 3.32 (k-wise independence from polynomials).
functions H =
Let F be a ﬁnite ﬁeld. Deﬁne the family of
{ha0,a1,...,ak−1:F → F} where each ha0,a1,...,ak−1(x) =a 0 + a1x + a2x2 +
· · · + ak−1xk−1 for a0, . . . , ak−1 ∈ F.

Proposition 3.33. The family H given in Construction 3.32 is k-wise
independent.

Proof. Similarly to the proof of Proposition 3.24, it suﬃces to prove
that for all distinct x1, . . . , xk ∈ F and all y1, . . . , yk ∈ F, there is exactly
one polynomial h of degree at most k − 1 such that h(xi) =y i for all i.
To show that such a polynomial exists, we can use the Lagrange Inter-
polation Formula:

h(x) =

(cid:5)

k(cid:3)

yi ·

i=1

j(cid:11)=i

x − xj
xi − xj

.

To show uniqueness, suppose we have two polynomials h and g of degree
at most k − 1 such that h(xi) =g (xi) for i = 1, . . . , k. Then h − g has
at least k roots, and thus must be the zero polynomial.

Corollary 3.34. For every n, m, k ∈ N, there is a family of k-wise
independent functions H = {h : {0, 1}n → {0, 1}m} such that choosing



<!-- pdf-page: 76 -->
3.6 Exercises

73

a random function from H takes k · max{n, m} random bits, and eval-
uating a function from H takes time poly(n, m, k).

k-wise independent hash functions have applications similar to those
that pairwise independent hash functions have. The increased indepen-
dence is crucial in derandomizing some algorithms. k-wise independent
random variables also satisfy a tail bound similar to Proposition 3.28,
with the key improvement being that the error probability vanishes
linearly in tk/2 rather than t; see Problem 3.8.

3.6 Exercises

Problem 3.1 (Derandomizing RP versus BPP*). Show that
prRP = prP implies
that prBPP = prP, and thus also that
BPP = P. (Hint: Look at the proof that NP = P ⇒ BPP = P.)

Problem 3.2 (Designs). Designs (also known as packings) are col-
lections of sets that are nearly disjoint. In Section 7, we will see how
they are useful in the construction of pseudorandom generators. For-
mally, a collection of sets S1, S2, . . . , Sm ⊂ [d] is called an ((cid:6), a)-design
(for integers a ≤ (cid:6) ≤ d) if

• For all i, |Si| = (cid:6).
• For all i (cid:1)= j, |Si ∩ Sj| < a.

For given (cid:6), we’d like m to be large, a to be small, and d to be small.
That is, we’d like to pack many sets into a small universe with small
intersections.

(cid:1)

(cid:2)

(cid:1)

(cid:2)2

d
a

/

(1) Prove that if m ≤
S1, . . . , Sm ⊂ [d].
Hint: Use the Probabilistic Method. Speciﬁcally, show that
if the sets are chosen randomly, then for every S1, . . . , Si−1,

, then there exists an ((cid:6), a)-design

(cid:4)
a

[#{j < i : |Si ∩ Sj| ≥a}] < 1.

E
Si



<!-- pdf-page: 77 -->
74 Basic Derandomization Techniques

(2) Conclude that for every constant γ > 0 and every (cid:6), m ∈ N,
there exists an ((cid:6), a)-design S1, · · · , Sm ⊂ [d] with d = O( (cid:4)2
a )
and a = γ · log m. In particular, setting m = 2(cid:4), we ﬁt expo-
nentially many sets of size (cid:6) in a universe of size d = O((cid:6))
while keeping the intersections an arbitrarily small fraction
of the set size.

(3) Using the Method of Conditional Expectations, show how
to construct designs as in Parts 1 and 2 deterministically in
time poly(m, d).

Problem 3.3 (More Pairwise Independent Families).

(1) (matrix-vector family) For an n × m {0, 1}-matrix A and
b ∈ {0, 1}n, deﬁne a function hA,b : {0, 1}m → {0, 1}n by
hA,b(x) = (Ax + b) mod 2. (The “mod 2” is applied compo-
nentwise.) Show that Hm,n = {hA,b} is a pairwise indepen-
dent family. Compare the number of random bits needed to
generate a random function in Hm,n to Construction 3.23.
(2) (Toeplitz matrices) A is a Toeplitz matrix if it is constant on
diagonals, i.e., Ai+1,j+1 = Ai,j for all i, j. Show that even if
we restrict the family Hm,n in Part 1 to only include hA,b
for Toeplitz matrices A, we still get a pairwise independent
family. How many random bits are needed now?

Problem 3.4(Almost Pairwise Independence). A family of func-
tions H mapping domain [N ] to range [M ]
independent3 if for every x1 (cid:1)= x2 ∈ [N ], y1, y2 ∈ [M ], we have

isε-almost pairwise

[H(x1) =y 1 and H(x2) =y 2] ≤ 1 +ε
M 2 .

Pr
R←H

H

3 Another common deﬁnition of ε-almost pairwise independence requires instead that for
R← H, the random variable
every x1 (cid:11)= x2 ∈ [N ], if we choose a random hash function H
(H(x1), H(x2)) is ε-close to two uniform and independent elements of [M ] in statistical
diﬀerence (as deﬁned in Section 6). The two deﬁnitions are equivalent up to a factor of
M 2 in the error parameter ε.



<!-- pdf-page: 78 -->
3.6 Exercises

75

(1) Show that there exists a family H of ε-almost pairwise inde-
pendent functions from {0, 1}n to {0, 1}m such that choosing
a random function from H requires only O(m + log n +
log(1/ε)) random bits (as opposed to O(m + n) for exact
pairwise independence). (Hint: First consider domain Fd+1
for an appropriately chosen ﬁnite ﬁeld F and d ∈ N, and look
at maps of the form h = g ◦ fa, where g comes from some
pairwise independent family and fa : Fd+1 → F is deﬁned by
fa(x0, . . . , xd) =x 0 + x1a + x2a2 + · · · + xdad.)

(2) Give a deterministic algorithm that on input an N -vertex,
M -edge graph G (with no self-loops), ﬁnds a cut of size
at least (1/2 − o(1)) · M in time M · polylog(N ) and space
O(log M ) (thereby improving the M · poly(N ) running time
of Algorithm 3.20).

Problem 3.5 (Size Lower Bound for Pairwise Independent
Families). Let H = {h : [N ] → [M ]} be a pairwise independent family
of functions.

(1) Prove that if N ≥ 2, then |H| ≥ M 2.
(2) Prove that if M = 2, then |H| ≥ N + 1. (Hint: based on
H, construct a sequence of orthogonal vectors vx ∈ {±1}|H|
parameterized by x ∈ [N ].)

(3) More generally, prove that for arbitrary M , we have |H| ≥
N · (M − 1) + 1. (Hint: for each x ∈ [N ], construct M − 1
linearly independent vectors vx,y ∈ R|H| such that vx,y ⊥
vx(cid:2),y(cid:2) if x (cid:1)= x(cid:3).)

(4) Deduce that for N = 2n and M = 2m, selecting a random
function from H requires at least max{n, m} + m random
bits.

Problem 3.6(Frequency Moments of Data Streams). Given one
pass through a huge “stream” of data items (a1, a2, . . . , ak), where each



<!-- pdf-page: 79 -->
76 Basic Derandomization Techniques

ai ∈ {0, 1}n, we want to compute statistics on the distribution of items
occurring in the stream while using small space (not enough to store all
the items or maintain a histogram). In this problem, you will see how to
a, where ma = #{i :
compute the second frequency moment f2 =
ai = a}.

a m2

(cid:4)

it
The algorithm works as follows: Before receiving any items,
chooses t random 4-wise independent hash functions H1, . . . , Ht :
{0, 1}n → {+1, −1}, and sets counters X1 = X2 = · · · = Xt = 0. Upon
receiving the ith item ai, it adds Hj(ai) to counter Xj. At the end of
1 + · · · + X 2
the stream, it outputs Y = (X 2
Notice that the algorithm only needs space O(t · n) to store the
hash functions Hj and space O(t · log k) to maintain the counters Xj
(compared to space k · n to store the entire stream, and space 2n · log k
to maintain a histogram).

t )/t.

(1) Show that for every data stream (a1, . . . , ak) and each j, we
j ] =f 2, where the expectation is over the choice of

have E[X 2
the hash function Hj.

j ] ≤ 2f 2
2 .

(2) Show that Var[X 2
(3) Conclude that for a suﬃciently large constant t (independent
of n and k), the output Y is within 1% of f2 with probability
at least 0.99.

(4) Show how to decrease the error probability to δ while only

increasing the space by a factor of log(1/δ).

Problem 3.7(Improved Pairwise Independent Tail Inequality).

(1) Show that if X is a random variable taking values in [0, 1]

and µ = E[X], we have Var[X] ≤ µ · (1 − µ).

(2) Improve the Pairwise Independent Tail Inequality (Propo-
sition 3.28) to show that if X is the average of t pairwise
independent random variables taking values in [0, 1] and µ =
E[X], then Pr[|X − µ| ≥ε] ≤ µ · (1 − µ)/(t · ε2). In particu-
lar, for t = O(1/µ), we have Pr[.99µ ≤ X ≤ 1.01µ] ≥ 0.99.



<!-- pdf-page: 80 -->
3.7 Chapter Notes and References

77

Problem 3.8(k -wise Independent Tail Inequality). Let X be the
average of t k-wise independent random variables for an even integer k,
and let µ = E[X]. Prove that

Pr[|X − µ| ≥ε] ≤

(cid:14)

k2
4tε2

(cid:15)k/2

.

(cid:4)

(Hint: show that all terms in the expansion of E[(X − µ)k] =
i(Xi − µi))k] that involve more than k/2 variables Xi are zero.)
E[(
Note that for ﬁxed k, this probability decays like O(1/(tε2))k/2, improv-
ing the 1/(tε2) bound in pairwise independence when k > 2.

Problem 3.9 (Hitting Samplers). A function Samp : [N ] → [M ]t is
a (δ, ε) hitting sampler if for every set T ⊂ [M ] of density greater than
ε, we have

Pr
R←Samp(U[N ])

(z1,...,zt)

[∃i

zi ∈ T ] ≥ 1 − δ.

(1) Show that every (δ, ε) averaging sampler is a (δ, ε) hitting

sampler.

(2) Show that if we only want a hitting sampler, the number of
samples in Theorem 3.30 can be reduced to O(1/(εδ)). (Hint:
use Problem 3.7.)

(3) For which subset of BPP algorithms are hitting samplers

useful for doing randomness-eﬃcient error reduction?

3.7 Chapter Notes and References

The Time Hierarchy Theorem was proven by Hartmanis and
Stearns [200]; proofs can be found in any standard text on complex-
ity theory, for example, [32, 161, 366]. Adleman [3] showed that every
language in RP has polynomial-sized circuits (cf., Corollary 3.12),
and this was generalized to BPP by Gill. Pippenger [310] showed
the equivalence between having polynomial-sized circuits and P/poly



<!-- pdf-page: 81 -->
78 Basic Derandomization Techniques

(Fact 3.11). The general deﬁnition of complexity classes with advice
(Deﬁnition 3.10) is due to Karp and Lipton [235], who explored the rela-
tionship between nonuniform lower bounds and uniform lower bounds.
A 5n − O(n) circuit-size lower bound for an explicit function (in P)
was given by Iwama et al. [218, 254].

The existence of universal traversal sequences (Example 3.8) was
proven by Aleliunas et al. [13], who suggested ﬁnding an explicit con-
struction (Open Problem 3.9) as an approach to derandomizing the
logspace algorithm for Undirected S-T Connectivity. For the state
of the art on these problems, see Section 4.4. An conjectured determin-
istic NC algorithm for Perfect Matching (derandomizing Algo-
rithm 2.7 in a diﬀerent way than Open Problem 3.7) is given in [4].

Theorem 3.14 is due to Sipser [364], who proved that BPP is in
the fourth level of the polynomial-time hierarchy; this was improved to
the second level by G´acs. Our proof of Theorem 3.14 is due to Laute-
mann [256]. Problem 3.1 is due to Buhrman and Fortnow [85]. For more
on nondeterministic computation and nonuniform complexity, see text-
books on computational complexity, such as [32, 161, 366].

The Method of Conditional Probabilities was formalized and
popularized as an algorithmic tool in the work of Spencer [370] and
Its use in Algorithm 3.17 for approximating Max-
Raghavan [316].
Cut is implicit in [279]. For more on this method, see the textbooks
[25, 291].

A more detailed treatment of pairwise independence (along with
a variety of other topics in pseudorandomness and derandomization)
can be found in the survey by Luby and Wigderson [281]. The use of
limited independence in computer science originates with the seminal
papers of Carter and Wegman [93, 417], which introduced the notions
of universal, strongly universal (i.e., k-wise independent), and almost
strongly universal (i.e., almost k-wise independent) families of hash
functions. The pairwise independent and k-wise independent sample
spaces of Constructions 3.18, 3.23, and 3.32 date back to the work
of Lancaster [255] and Joﬀe [222, 223] in the probability literature,
and were rediscovered several times in the computer science literature.
The construction of pairwise independent hash functions from Part 1
of Problem 3.3 is due to Carter and Wegman [93] and Part 2 is implicit



<!-- pdf-page: 82 -->
3.7 Chapter Notes and References

79

in [408, 168]. The size lower bound for pairwise independent families
in Problem 3.5 is due to Stinson [376], based on the Plackett–Burman
bound for orthogonal arrays [312]. The construction of almost pairwise
independent families in Problem 3.4 is due to Bierbrauer et al. [67]
(though the resulting parameters follow from the earlier work of Naor
and Naor [296]).

The application to hash tables from Section 3.5.3 is due to Carter
and Wegman [93], and the method mentioned for improving the
space complexity to O(K log N ) is due to Fredman, Komlos, and
[142]. The problem of randomness-eﬃcient error reduc-
Szemer´edi
tion (sometimes called “deterministic ampliﬁcation”) was ﬁrst studied
by Karp, Pippenger, and Sipser [234], and the method using pair-
wise independence given in Section 3.5.4 was proposed by Chor and
Goldreich [97]. The use of pairwise independence for derandomizing
algorithms was pioneered by Luby [278]; Algorithm 3.20 for MaxCut
is implicit in [279]. The notion of averaging samplers was introduced
by Bellare and Rompel [57] (under the term “oblivious samplers”). For
more on samplers and averaging samplers, see the survey by Goldre-
ich [155]. Tail bounds for k-wise independent random variables, such
as the one in Problem 3.8, can be found in the papers [57, 97, 350].

Problem 3.2 on designs is from [134], with the derandomization of
Part 3 being from [281, 302]. Problem 3.6 on the frequency moments
of data streams is due to Alon, Matias, and Szegedy [22]. For more on
data stream algorithms, we refer to the survey by Muthukrishnan [295].



<!-- pdf-page: 83 -->
4

Expander Graphs

Now that we have seen a variety of basic derandomization techniques,
we will move on to study the ﬁrst major “pseudorandom object” in this
survey, expander graphs. These are graphs that are “sparse” yet very
“well-connected.”

4.1 Measures of Expansion

We will typically interpret the properties of expander graphs in an
asymptotic sense. That is, there will be an inﬁnite family of graphs Gi,
with a growing number of vertices Ni. By “sparse,” we mean that the
degree Di of Gi should be very slowly growing as a function of Ni. The
“well-connectedness” property has a variety of diﬀerent interpretations,
which we will discuss below. Typically, we will drop the subscripts of i
and the fact that we are talking about an inﬁnite family of graphs will
be implicit in our theorems. As in Section 2.4.2, we will state many
of our deﬁnitions for directed multigraphs (which we’ll call digraphs for
short), though in the end we will mostly study undirected multigraphs.

80



<!-- pdf-page: 84 -->
4.1 Measures of Expansion

81

4.1.1 Vertex Expansion

The classic measure of well-connectedness in expanders requires that
every “not-too-large” set of vertices has “many” neighbors:

Deﬁnition 4.1. A digraph G is a (K, A) vertex expander if
for
all sets S of at most K vertices, the neighborhood N (S) def= {u|∃v ∈
S s.t. (u, v) ∈ E} is of size at least A · |S|.

Ideally, we would like D = O(1), K = Ω(N ), where N is the number

of vertices, and A as close to D as possible.

There are several other measures of expansion, some of which we

will examine in forthcoming sections:

• Boundary Expansion: Instead of N (S), only use the boundary

∂S def= N (S) \ S.

• Edge Expansion (cuts): Instead of ∂S, use the number of

edges leaving S.

• Random Walks: Random walks converge quickly to the uni-
form distribution, that is, the second eigenvalue λ(G) is
small.

• “Quasi-randomness” (a.k.a “Mixing”): for every two sets S
and T (say of constant density), the fraction of edges between
S and T is roughly the product of their densities.

All of these measures are very closely related to each other, and are
even equivalent for certain settings of parameters.

It is not obvious from the deﬁnition that good vertex expanders
(say, with D = O(1), K = Ω(N ), and A = 1 + Ω(1)) even exist. We
will show this using the Probabilistic Method.

Theorem 4.2. For all constants D ≥ 3, there is a constant α > 0 such
that for all N , a random D-regular undirected graph on N vertices is
an (αN, D − 1.01) vertex expander with probability at least 1/2.

Note that the degree bound of 3 is the smallest possible, as every
graph of degree 2 is a poor expander (being a union of cycles and



<!-- pdf-page: 85 -->
82 Expander Graphs

chains). In addition, for most settings of parameters, it is impossible to
have expansion larger than D − 1 (as shown in Problem 4.3).

We prove a slightly simpler theorem for bipartite expanders.

Deﬁnition 4.3. A bipartite multigraph G is a (K, A) vertex expander
if for all sets S of left-vertices of size at most K, the neighborhood
N (S) is of size at least A · |S|.

Now, let BipN,D be the set of bipartite multigraphs that have N
vertices on each side and are D-leftregular, meaning that every vertex
on the left has D neighbors, numbered from 1, . . . , D (but vertices on
the right may have varying degrees).

Theorem 4.4. For every constant D, there exists a constant α > 0
such that for all N , a uniformly random graph from BipN,D is an
(αN, D − 2) vertex expander with probability at least 1/2.

Proof. First, note that choosing G R← BipN,D is equivalent to uniformly
and independently choosing D neighbors on the right for each left
vertex v. Now, for K ≤ αN , let pK be the probability that there
exists a left-set S of size exactly K that does not expand by at
least D − 2. Fixing a subset S of size K, N (S) is a set of KD ran-
dom vertices in [N ] (chosen with replacement). We can imagine these
vertices V1, V2, . . . , VKD being chosen in sequence. Call Vi a repeat if
Vi ∈ {V1, . . . , Vi−1}. Then the probability that Vi is a repeat, even con-
ditioned on V1, . . . , Vi−1, is at most (i − 1)/N ≤ KD/N . So,
Pr[|N (S)| ≤(D − 2) · K] ≤ Pr[there are at least 2K

repeats among V1, . . . , VKD]
(cid:14)
(cid:15)

(cid:15) (cid:14)

≤

KD
2K

2K

.

KD
N

Thus, we ﬁnd that
(cid:15)(cid:14)

(cid:14)

pK ≤

N
K

(cid:15) (cid:14)

(cid:15)

2K

KD
2K
(cid:14)

K

KD
N
(cid:15)

2K

(cid:15)

(cid:14)

≤

N e
K

KDe
2K

(cid:14)

KD
N

(cid:15)

2K

(cid:14)

=

e3D4K
4N

(cid:15)K

,



<!-- pdf-page: 86 -->
4.1 Measures of Expansion

83

where e is the base of the natural logarithm. Since K ≤ αN , we can
set α = 1/(e3D4) to obtain pK ≤ 4−K. Thus

Pr
G∈BipN,D

[G is not an (αN, D − 2) expander] ≤

(cid:13)αN (cid:14)(cid:3)

K=1

4−K <

1
2

.

There are a number of variants to the above probabilistic construc-

tion of expanders.

• We can obtain a bipartite multigraph that is D-regular on
both sides by taking the union of D random perfect match-
ings. This can be analyzed using a small modiﬁcation of the
analysis above; even though V1, . . . , VKD are not indepen-
dent, the probability of a Vi being a repeat conditioned on
V1, . . . , Vi−1 can still be bounded by KD/(N − K). Also, the
multigraph can be made into a simple graph by eliminating
or redistributing edges.

• One can optimize α rather than the expansion factor A,
showing that for all constants α < 1 and D > 2, there exists
a constant A >1 such that for all suﬃciently large N , a
random graph in BipN,D is an (αN, A) vertex expander with
high probability.

• In fact, a very general tradeoﬀ between D, α, and A is known:
a random D-regular N -vertex bipartite multigraph is an
(αN, A) vertex expander with high probability for suﬃciently
large N if D > H(α)+H(αA)
H(α)−αAH(1/A) , where H(p) =p log(1/p) +
(1 − p) log(1/(1 − p)) is the binary entropy function.

• The results can also be extended to unbalanced bipartite
graphs (where the right side is smaller than the left), and
nonbipartite graphs as well, and both of these cases are
important in some applications.

In addition to being natural combinatorial objects, expander graphs
have numerous applications in theoretical computer science, including
the construction of fault-tolerant networks (indeed, the ﬁrst papers
on expanders were in conferences on telephone networks), sorting in
O(log n) time in parallel, derandomization (as we will see),
lower



<!-- pdf-page: 87 -->
84 Expander Graphs

results

regarding

integrality

bounds in circuit complexity and proof complexity, error-correcting
codes, negative
linear
programming relaxations and metric embeddings, distributed routing,
and data structures. For many of these applications, it is not enough
to know that a random graph is a good expander — we need explicit
constructions, that is, ones that are deterministic and eﬃcient. We view
such explicit expanders as “pseudorandom objects” because they are
ﬁxed graphs that possess many of the properties of random graphs.

gaps

for

4.1.2 Spectral Expansion

Intuitively, another way of saying that a graph is well-connected is
to require that random walks on the graph converge quickly to the
stationary distribution. As we have seen in Section 2.4.2, the mixing
rate of random walks in turn is captured well by the second largest
eigenvalue of the transition matrix, and this turns out to be a very
useful measure of expansion for many purposes.

Recall that for an N -vertex regular directed graph G with random-

walk matrix M , we deﬁne

λ(G) def= max

π

(cid:21)πM − u(cid:21)
(cid:21)π − u(cid:21) = max
x⊥u

(cid:21)xM (cid:21)
(cid:21)x(cid:21) ,

where u = (1/N, . . . , 1/N ) ∈ RN is the uniform distribution on [N ], the
ﬁrst maximum is over all probability distributions π ∈ [0, 1]N , and the
second maximum is over all vectors x ∈ RN that are orthogonal to u.
We write γ(G) def= 1 − λ(G) to denote the spectral gap of G.

Deﬁnition 4.5. For γ ∈ [0, 1], we say that a regular digraph G has
spectral expansion γ if γ(G) ≥ γ (equivalently, λ(G) ≤ 1 − γ).1

Larger values of γ(G) (or smaller values of λ(G)) correspond to bet-
ter expansion. Sometimes it is more natural to state results in terms of
γ(G) and sometimes in terms of λ(G). Surprisingly, this linear-algebraic

1 In other sources (including the original lecture notes on which this survey was based), the
spectral expansion referred to λ rather than γ. Here we use γ, because it has the more
natural feature that larger values of γ correspond to the graph being “more expanding.”



<!-- pdf-page: 88 -->
4.1 Measures of Expansion

85

measure of expansion turns out to be equivalent to the combinatorial
measure of vertex expansion for common parameters of interest.

One direction is given by the following:

Theorem 4.6 (spectral expansion ⇒ vertex expansion). If G
is a regular digraph with spectral expansion γ = 1 − λ for some λ ∈
[0, 1], then, for every α ∈ [0, 1], G is an
vertex
expander. In particular, G is an (N/2, 1 +γ ) expander.

αN, 1/((1 − α)λ2 + α)

(cid:1)

(cid:2)

We prove this theorem using the following two useful statistics of

probability distributions.

Deﬁnition 4.7. For a probability distribution π, the collision proba-
bility of π is deﬁned to be the probability that two independent sam-
ples from π are equal, namely CP(π) =
x. The support of π is
Supp(π) ={x : πx > 0}.

x π2

(cid:4)

Lemma 4.8. For every probability distribution π ∈ [0, 1]N , we have:

(1) CP(π) =(cid:21)π (cid:21)2 = (cid:21)π − u(cid:21)2 + 1/N , where u is the uniform

distribution on [N ].

(2) CP(π) ≥ 1/ |Supp(π)|, with equality iﬀ π is uniform on

Supp(π).

Proof. For Part 1, the fact that CP(π) =(cid:21)π (cid:21)2 follows immediately from
the deﬁnition. Then, writing π = u + (π − u), and noting that π − u is
orthogonal to u, we have(cid:21)π (cid:21)2 = (cid:21)u(cid:21)2 + (cid:21)π − u(cid:21)2 = 1/N + (cid:21)π − u(cid:21)2.

For Part 2, by Cauchy–Schwarz we have

(cid:26)

(cid:3)

(cid:7)

|Supp(π)| ·

πx ≤

1 =

x∈Supp(π)

(cid:3)

x

π2
x =

(cid:7)

|Supp(π)| ·

(cid:7)

CP(π),

with equality iﬀ π is uniform on Supp(π).

Proof of Theorem 4.6 The condition that G has spectral expansion
γ = 1 − λ is equivalent to saying that λ(G) ≤ λ. By the deﬁnition of



<!-- pdf-page: 89 -->
86 Expander Graphs

λ(G) and Part 1 of Lemma 4.8, we have
(cid:14)

CP(πM ) − 1
N

≤ λ2 ·

CP(π) − 1
N

(cid:15)

for every probability distribution π. Letting S be any subset of the
vertices of size at most αN and π the uniform distribution on S, we
have CP(π) = 1/|S| and CP(πM ) ≥ 1/ |Supp(πM )| = 1/ |N (S)|. Thus,

(cid:14)

1
|N (S)|

− 1
N

(cid:15)

(cid:14)

≤ λ2 ·

(cid:15)

.

1
|S|

− 1
N

Solving for
|S|/(λ2(1 − α) +α ), as desired.

|N (S)| and using N ≥ |S|/α, we obtain |N (S)| ≥

The other direction, i.e., obtaining spectral expansion from vertex

expansion, is more diﬃcult (and we will not prove it here).

Theorem 4.9 (vertex expansion ⇒ spectral expansion). For
every δ > 0 and D > 0, there exists γ > 0 such that if G is a D-regular
(N/2, 1 +δ ) vertex expander, then it also has spectral expansion γ.
Speciﬁcally, we can take γ = Ω((δ/D)2).

Note ﬁrst the dependence on subset size being N/2: this is necessary,
because a graph can have vertex expansion (αN, 1 + Ω(1)) for α < 1/2
and be disconnected (e.g., the disjoint union of two good expanders),
thereby having no spectral expansion. Also note that the bound on γ
deteriorates as D increases. This is also necessary, because adding edges
to a good expander cannot hurt its vertex expansion, but can hurt its
spectral expansion.

Still, roughly speaking, these two results show that vertex expansion
and spectral expansion are closely related, indeed equivalent for many
interesting settings of parameters:

Corollary 4.10. Let G be an inﬁnite family of D-regular multigraphs,
for a constant D ∈ N. Then the following two conditions are equivalent:

• There is a constant δ > 0 such that every G ∈ G is an

(N/2, 1 +δ ) vertex expander.



<!-- pdf-page: 90 -->
4.1 Measures of Expansion

87

• There is a constant γ > 0 such that every G ∈ G has spectral

expansion γ.

When people informally use the term “expander,” they often mean
a family of regular graphs of constant degree D satisfying one of the
two equivalent conditions above.

However, the two measures are no longer equivalent if one wants
to optimize the expansion constants. For vertex expansion, we have
already seen that if we allow α to be a small constant (depending on
D), then there exist (αN, A) vertex expanders with A very close to
D − 1, e.g., A = D − 1.01, and Problem 4.3 shows that A cannot be
any larger than D − 1. The optimal value for the spectral expansion is
also well-understood. First note that, by taking α → 0 in Theorem 4.6,
a graph with spectral expansion 1 − λ has vertex expansion A ≈ 1/λ2
D − o(1). In fact, this
for small sets. Thus, a lower bound on λ is 1/
lower bound can be improved, as shown in the following theorem (and
proven in Problem 4.4):

√

Theorem 4.11. For every constant D ∈ N, any D-regular, N -vertex
√
multigraph G satisﬁes λ(G) ≥ 2
D − 1/D − O(1), where the O(1)
term vanishes as N → ∞ (and D is held constant).

√

there exist explicit constructions giving λ(G) <
Surprisingly,
D − 1/D. Graphs meeting this bound are called Ramanujan graphs.

2
Random graphs almost match this bound, as well:

Theorem 4.12. For any constant D ∈ N, a random D-regular N -
√
vertex graph satisﬁes λ(G) ≤ 2
D − 1/D + O(1) with probability
1 − O(1) where both O(1) terms vanish as N → ∞ (and D is held
constant).

see what

Now let us

spectral expansion
imply in the world of vertex expansion. With Ramanujan graphs
(λ(G) ≤ 2
D − 1/D), the bound from Theorem 4.6 gives a vertex
expansion factor of A ≈ D/4 for small sets. This is not tight, and

these results

for

√



<!-- pdf-page: 91 -->
88 Expander Graphs

√

it is known that Ramanujan graphs actually have vertex expansion
D/2 − O(1) for sets of density O(1), which is tight in the sense that
there are families of graphs with λ(G) → 2
D − 1/D but vertex
expansion at most D/2. Still, this vertex expansion is not as good
as we obtained via the Probabilistic Method (Theorem 4.2), where
we achieved vertex expansion D − O(1). This means that we cannot
obtain optimal vertex expansion by going through spectral expansion.
Similarly, we cannot obtain optimal spectral expansion by going
through vertex expansion (because the bound on spectral expansion in
Theorem 4.9 necessarily deteriorates as the degree D increases). The
conclusion is that vertex and spectral expansion are loosely equivalent,
but only if we are not interested in optimizing the constants in the
tradeoﬀs between various parameters (and for some applications these
are crucial).

4.1.3 Other Measures of Expansion

In this section, we mention two other useful measures of expansion
involving edges crossing cuts in the graph. For two sets S, T ⊂ V (G),
let e(S, T ) =(cid:21){(u, v ) ∈ S × T | {u, v} ∈E }(cid:21). Here (u, v) refers to an
ordered pair, in contrast to the deﬁnition of cut(S, T ) in Section 2.3.4.
Thus, we count edges entirely within S ∩ T twice, corresponding to
both orientations.

Deﬁnition 4.13. A D-regular digraph G is a (K, ε) edge expander if
for all sets S of at most K vertices, the cut size e(S, S) is at least
ε · |S| ·D .

That is, at least an ε fraction of the edges from S lead outside S.
(Sometimes edge expansion is deﬁned without the normalization factor
of D, only requiring e(S, S) ≥ ε · |S|.) When viewed in terms of the
random walk on G, the ratio e(S, S)/(|S| ·D ) is the probability that,
if we condition the stationary distribution on being in S, the random
walk leaves S in one step. It turns out that if we ﬁx K = N/2, then
edge expansion turns out to be even more closely related to spectral



<!-- pdf-page: 92 -->
4.1 Measures of Expansion

89

expansion than vertex expansion is. Indeed:

Theorem 4.14.

(1) If a D-regular, N -vertex digraph G has spectral expansion

γ, then G is an (N/2, γ/2) edge expander.

(2) If a D-regular, N -vertex digraph G is a (N/2, ε) edge
expander and at least an α fraction of edges leaving each
vertex are self-loops for some α ∈ [0, 1], then G has spectral
expansion α · ε2/2.

The condition about self-loops in Part 2 is to ensure that the graph
is far from being bipartite (or more generally “periodic” in the sense
that all cycle lengths are divisible by some number larger than 1),
because a bipartite graph has spectral expansion 0 but can have positive
edge expansion. For graphs with a constant fraction of self-loops at
each vertex, the theorem implies that the edge expansion is bounded
away from 0 iﬀ the spectral expansion is bounded away from 0. Unlike
Corollary 4.10, this equivalence holds even for graphs of unbounded
degree. The intuition for the relation is that a large edge expansion ε
implies that the random walk on the graph has no “bottlenecks” and
thus should mix rapidly. This connection also holds for Markov chains
in general (when the deﬁnitions are appropriately generalized), where
the edge expansion is known as the conductance. Part 1 of Theorem 4.14
will follow as a special case of the Expander Mixing Lemma below; we
omit the proof of Part 2.

Next, we consider a generalization of edge expansion, where we look
at edges not just from a set S to its complement but between any
two sets S and T . If we think of an expander as being like a random
graph, we would expect the fraction of edges that go from S to T to be
approximately equal to the product of the densities of S and T . The
following result shows that this intuition is correct:

Lemma 4.15 (Expander Mixing Lemma). Let G be a D-regular,
N -vertex digraph with spectral expansion 1 − λ. Then for all sets of



<!-- pdf-page: 93 -->
90 Expander Graphs

vertices S, T of densities α = |S|/N and β = |T |/N , we have

(cid:12)
(cid:12)
(cid:12)
(cid:12)

e(S, T )
N · D

− αβ

(cid:12)
(cid:12)
(cid:12)
(cid:12) ≤ λ

(cid:7)

α · (1 − α) · β · (1 − β).

(cid:7)

≤ λ

αβ ≤ λ.

Observe that the denominator N · D counts all edges of the graph
(as ordered pairs). The lemma states that the diﬀerence between the
fraction of edges from S to T and the expected value if we were to choose
G randomly is “small,” roughly λ times the square root of this fraction.
Finally, note that Part 1 of Theorem 4.14 follows from the Expander
Mixing Lemma by setting T = Sc, soβ = 1 − α and e(S, T )/N D ≥
(1 − λ) · α · (1 − α) ≥ γα/2.
a

that
|e(S, T )/|E| −αβ | = O(1) for all sets S, T (with densities α, β),
the graph is called quasirandom. Thus, the Expander Mixing Lemma
implies that a regular digraph with λ(G) =O (1) is quasirandom.
Quasirandomness has been studied extensively for dense graphs, in
which case it has numerous equivalent formulations. Here we are most
interested in sparse graphs, especially constant-degree graphs (for
which λ(G) =O (1) is impossible).

digraph G = (V, E)

property

When

has

the

Proof. Let χS be the characteristic (row) vector of S and χT
the characteristic vector of T . Let A be the adjacency matrix of
G, and M = A/D be the random-walk matrix for G. Note that
e(S, T ) =χ SAχt
T , where the superscript t denotes the
transpose.

T = χS(DM )χt

⊥ u. The coeﬃcient of u is (cid:19)χS, u(cid:20)/(cid:19)u, u(cid:20) =

We can express χS as the sum of two components, one paral-
lel to the uniform distribution u, and the other a vector χ⊥
S , where
χ⊥
i(χS)i = |S| = αN .
S
Then χS = (αN )u + χ⊥
T . Intuitively,
the components parallel to the uniform distribution “spread” the weight
of S and T uniformly over the entire graph, and χ⊥
T will yield
the error term.

S and similarly χT = (βN )u + χ⊥

S and χ⊥

(cid:4)



<!-- pdf-page: 94 -->
4.1 Measures of Expansion

91

((αN )u + χ⊥

S )M ((βN )u + χ⊥
T )t

Formally, we have

e(S, T )
N · D

=

1
N
1
N

=

(αβN 2)uM ut +

1
N
1
S M ut +
N
Since uM = u and M ut = ut, and both χ⊥
S and χ⊥
u, the above expression simpliﬁes to:

(βN )χ⊥

1
N

+

(αN )uM (χ⊥

T )t

S M (χ⊥
χ⊥

T )t.

T are orthogonal to

e(S, T )
N · D

= (αβN )uut +

S M (χ⊥
χ⊥
T )t
N

= αβ +

(χ⊥

S M )(χ⊥
T )t
N

.

Thus,

(cid:12)
(cid:12)
(cid:12)
(cid:12)

e(S, T )
N · D

(cid:12)
(cid:12)
(cid:12)
(cid:12) =

(cid:12)
(cid:12)
(cid:12)
(cid:12)

− αβ

≤ 1
N
≤ 1
N
To complete the proof, we note that

(cid:12)
(cid:12)
(cid:12)
(cid:12)

(χ⊥

S M )(χ⊥
T )t
N
S M (cid:21) · (cid:21)χ⊥
· (cid:21)χ⊥

T

(cid:21)

· λ(cid:21)χ⊥
S

(cid:21) · (cid:21)χ⊥
T

(cid:21).

αN = (cid:21)χS
(cid:7)
(cid:21) =
β · (1 − β) · N .

(cid:21)χ⊥
S

so
(cid:7)

(cid:21)2 = (cid:21)(αN )u(cid:21)2 + (cid:21)χ⊥
S
(cid:7)

(cid:21)2 = α2N + (cid:21)χ⊥
S
α · (1 − α) · N and similarly χ⊥

(cid:21)2,

(α − α2)N =

T =

Similarly to vertex expansion and edge expansion, a natural ques-
tion is to what extent the converse holds. That is, if e(S, T )/N D is
always “close” to the product of the densities of S and T , then is λ(G)
necessarily small? This is indeed true:

Theorem 4.16 (Converse to Expander Mixing Lemma). Let G
be a D-regular, N -vertex undirected graph. Suppose that for all pairs
of disjoint vertex sets S, T , we have |e(S, T )/(N · D) − µ(S)µ(T )| ≤
(cid:7)
µ(S)µ(T ) for some θ ∈ [0, 1], where µ(R) =|R |/N for any set R of
θ
vertices. Then λ(G) =O (θ log(1/θ)).



<!-- pdf-page: 95 -->
92 Expander Graphs

Putting the two theorems together, we see that λ and θ are the
same up to a logarithmic factor. Thus, unlike the other connections we
have seen, this connection is good for highly expanding graphs (i.e.,
λ(G) close to zero, γ(G) close to 1).

4.2 Random Walks on Expanders

From the previous section, we know that one way of characterizing
an expander graph G is by having a bound on its second eigenvalue
λ(G), and in fact there exist constant-degree expanders where λ(G) is
bounded by a constant less than 1. From Section 2.4.3, we know that
this implies that the random walk on G converges quickly to the uni-
form distribution. Speciﬁcally, a walk of length t started at any vertex
ends at (cid:6)2 distance at most λt from the uniform distribution. Thus
after t = O(log N ) steps, the distribution is very close to uniform, for
example, the probability of every vertex is (1 ± 0.01)/N . Note that,
if G has constant degree, the number of random bits invested here is
O(t) =O (log N ), which is within a constant factor of optimal; clearly
log N − O(1) random bits are also necessary to sample an almost uni-
form vertex. Thus, expander walks give a very good tradeoﬀ between
the number of random bits invested and the “randomness” of the ﬁnal
vertex in the walk. Remarkably, expander walks give good randomness
properties not only for the ﬁnal vertex in the walk, but also for the
sequence of vertices traversed in the walk. Indeed, in several ways to
be formalized below, this sequence of vertices “behaves” like uniform
independent samples of the vertex set.

A canonical application of expander walks is for randomness-
eﬃcient error reduction of randomized algorithms: Suppose we have an
algorithm with constant error probability, which uses some m random
bits. Our goal is to reduce the error to 2−k, with a minimal penalty in
random bits and time. Independent repetitions of the algorithm suﬀers
just an O(k) multiplicative penalty in time, but needs O(km) random
bits. We have already seen that with pairwise independence we can use
just O(m + k) random bits, but the time blows up by O(2k). Expander
graphs let us have the best of both worlds, using just m + O(k) ran-
dom bits, and increasing the time by only an O(k) factor. Note that



<!-- pdf-page: 96 -->
4.2 Random Walks on Expanders

93

for k = O(m), the number of random bits is (1 + O(1)) · m, even better
than what pairwise independence gives.

The general approach is to consider an expander graph with vertex
set {0, 1}m, where each vertex is associated with a setting of the random
bits. We will choose a uniformly random vertex v1 and then do a ran-
dom walk of length t − 1, visiting additional vertices v2, . . . , vt. (Note
that unlike the rapid mixing analysis, here we start at a uniformly ran-
dom vertex.) This requires m random bits for the initial choice, and
log D for each of the t − 1 steps. For every vertex vi on the random walk,
we will run the algorithm with vi as the setting of the random coins.

First, we consider the special case of randomized algorithms with
one-sided error (RP). For these, we should accept if at least one exe-
cution of the algorithm accepts, and reject otherwise. If the input is a
No instance, the algorithm never accepts, so we also reject. If the input
is a Yes instance, we want our random walk to hit at least one vertex
that makes the algorithm accept. Let B denote the set of “bad” vertices
giving coin tosses that make the algorithm reject. By the deﬁnition of
RP, the density of B is at most 1/2. Thus, our aim is to show that the
probability that all the vertices in the walk v1, . . . , vt are in B vanishes
exponentially fast in t, if G is a good expander.

The case t = 2 follows from the Expander Mixing Lemma given
in the previous section. If we choose a random edge in a graph with
spectral expansion 1 − λ, the probability that both endpoints are in a
set B is at most µ(B)2 + λ · µ(B). So if λ   µ(B), then the probability
is roughly µ(B)2, just like two independent random samples. The case
of larger t is given by the following theorem.

Theorem 4.17 (Hitting Property of Expander Walks). If G is a
regular digraph with spectral expansion 1 − λ , then for any B ⊂ V (G)
of density µ, the probability that a random walk (V1, . . . , Vt) oft − 1
steps in G starting in a uniformly random vertex V1 always remains in
B is

(cid:25)

(cid:24)

t(cid:27)

i=1

Pr

Vi ∈ B

≤ (µ + λ · (1 − µ))t .



<!-- pdf-page: 97 -->
94 Expander Graphs

Equivalently, a random walk “hits” the complement of B with high
probability. Note that if µ and λ are constants less than 1, then the
probability of staying in B is 2−Ω(t), completing the analysis of the
eﬃcient error-reduction algorithm for RP.

Before proving the theorem, we discuss general approaches to ana-
lyzing spectral expanders and random walks on them. Typically, the
ﬁrst step is to express the quantities of interest linear-algebraically,
involving applications of the random-walk (or adjacency) matrix M
to some vectors v. For example, when proving the Expander Mixing
Lemma (Lemma 4.15), we expressed the fraction of edges between sets
S and T as χSM χt
T (up to some normalization factor). Then we can
proceed in one of the two following ways:

Vector Decomposition Decompose the input vector(s) v as v = v(cid:15) +
v⊥, where v(cid:15) = ((cid:19)v, u(cid:20)/(cid:19)u, u(cid:20))u is the component of v in the
direction of the uniform distribution u and v⊥ is the component
of v orthogonal to u. Then this induces a similar orthogonal
decomposition of the output vector vM into

vM = (vM )(cid:15) + (vM )⊥ = v(cid:15)M + v⊥M,
where v(cid:15)M = v(cid:15) and (cid:21)v⊥M (cid:21) ≤λ · (cid:21)v⊥(cid:21). Thus, from informa-
tion about how vs lengths are divided into the uniform and non-
uniform components, we deduce information about how vM is
divided into the uniform and non-uniform components. This
is the approach we took in the proof of the Expander Mixing
Lemma.

Matrix Decomposition This corresponds to a diﬀerent decomposi-
tion of the output vector vM that can be expressed in a way
that is independent of the decomposition of the input vector v.
Speciﬁcally, if G has spectral expansion γ = 1 − λ, then

vM = v(cid:15) + v⊥M = γ · v(cid:15) + (λ · v(cid:15) + v⊥M )
= γ · vJ + λ · vE = v(γJ + λE),

where J is the matrix in which every entry is 1/N and the error
matrix E satisﬁes (cid:21)vE(cid:21) ≤ (cid:21)v(cid:21). The advantage of this decom-
position is that we can apply it even when we have no infor-
mation about how v decomposes (only its length). The fact



<!-- pdf-page: 98 -->
4.2 Random Walks on Expanders

95

that M is a convex combination of J and E means that we
can often treat each of these components separately and then
just apply the triangle inequality. However, it is less reﬁned
than the vector decomposition approach, and sometimes gives
weaker bounds. Indeed, if we used it to prove the Expander
Mixing Lemma (without decomposing χS and χT ), we would
get a slightly worse error term of λ
µ(S)µ(T ) +λµ(S )µ(T ).

(cid:7)

The Matrix Decomposition Approach can be formalized using the

following notion.

Deﬁnition 4.18. The (spectral) norm of an N × N real matrix M is
deﬁned to be

(cid:21)M (cid:21) = max
x∈RN
(If M is symmetric, then (cid:21)M (cid:21) equals the largest absolute value of any
eigenvalue of M .)

(cid:21)xM (cid:21)
(cid:21)x(cid:21)

Some basic properties of the matrix norm are that (cid:21)cA(cid:21) = |c| · (cid:21)A(cid:21),
(cid:21)A + B(cid:21) ≤ (cid:21)A(cid:21) + (cid:21)B(cid:21), and (cid:21)A · B(cid:21) ≤ (cid:21)A(cid:21) · (cid:21)B(cid:21) for every two matri-
ces A, B, and c ∈ R. Following the discussion above, we have the fol-
lowing lemma:

Lemma 4.19. Let G be a regular digraph on N vertices with random-
walk matrix M . Then G has spectral expansion γ = 1 − λ iﬀ M =
γJ + λE, where J is the N × N matrix where every entry is 1/N (i.e.,
the random-walk matrix for the complete graph with self-loops) and
(cid:21)E(cid:21) ≤1.

Proof. Suppose that G has spectral expansion γ. Then deﬁne E =
(M − γJ)/λ. To see that E has norm at most 1, ﬁrst observe that
uE = (uM − γuJ)/λ = (1 − γ)u/λ = u. Thus it suﬃces to show that
for every vector v orthogonal to u, the vector vE is orthogonal to u and
is of length at most (cid:21)v(cid:21). Orthogonality follows because vM is orthog-
onal to u (by regularity of G) and vJ = 0. The length bounds follows
from vE = (vM )/λ and (cid:21)vM (cid:21) ≤λ(cid:21)v (cid:21) by the spectral expansion of G.



<!-- pdf-page: 99 -->
96 Expander Graphs

Conversely, suppose that M = γJ + λE for some (cid:21)E(cid:21) ≤1. Then for
every vector v orthogonal to u, we have (cid:21)vM (cid:21) = (cid:21)0 +λvE (cid:21) ≤λ(cid:21)v (cid:21),
and thus G has spectral expansion γ.

Intuitively, this lemma says that we can think of a random step
on a graph with spectral expansion γ as being a random step on the
complete graph with probability γ and “not doing damage” with prob-
ability 1 − γ. This intuition would be completely accurate if E were
a stochastic matrix, but it is typically not (e.g., it may have nega-
tive entries). Still, note that the bound given in Theorem 4.17 exactly
matches this intuition: in every step, the probability of remaining in B
is at most γ · µ + λ = µ + λ · (1 − µ).

Now we can return to the proof of the theorem.

Proof of Theorem 4.17. We need a way to express getting stuck in
B linear-algebraically. For that, we deﬁne P to be the diagonal matrix
with Pi,i = 1 if i ∈ B and Pi,i = 0 otherwise. Thus, the probability a
distribution π picks a node in B is |πP |1, where | · |1 is the (cid:6)1 norm,
|x|1 =
|xi| (which in our case is equal to the sum of the components
of the vector, since all values are nonnegative).

(cid:4)

Let M be the random-walk matrix of G. The probability distribu-
tion for the ﬁrst vertex V1 is given by the vector u. Now we can state
the following crucial fact:

Claim 4.20. The probability that the random walk stays entirely
within B is precisely |uP (M P )t−1|1.

Proof of Claim: By induction on (cid:6), we show that (uP (M P )(cid:4))i is the
probability that the ﬁrst (cid:6) + 1 vertices of the random walk are in B and
the ((cid:6) + 1)st vertex is i. The base case is (cid:6) = 0. If i ∈ B, (uP )i = 1/N ;
if i /∈ B, (uP )i = 0. Now assume the hypothesis holds up to some (cid:6).
Then (uP (M P )(cid:4)M )i is the probability that the ﬁrst (cid:6) + 1 vertices of
the random walk are in B and the ((cid:6) + 2)nd vertex is i (which may
or may not be in B). Multiplying by P , we zero out all components
for nodes not in B and leave the others unchanged. Thus, we obtain
the probability that the ﬁrst (cid:6) + 2 vertices are in B and the ((cid:6) + 2)nd
vertex is i.



<!-- pdf-page: 100 -->
4.2 Random Walks on Expanders

97

To get a bound in terms of the spectral expansion, we will now
switch to the (cid:6)2 norm. The intuition is that multiplying by M shrinks
the component that is perpendicular to u (by expansion) and multi-
plying by P shrinks the component parallel to u (because it zeroes out
some entries). Thus, we should be able to show that the norm (cid:21)M P (cid:21)
is strictly less than 1. Actually, to get the best bound, we note that
uP (M P )t−1 = uP (P M P) t−1, because P 2 = P , so we instead bound
(cid:21)P M P(cid:21). Speciﬁcally:

Claim 4.21. (cid:21)P M P(cid:21) ≤µ + λ · (1 − µ).

Proof of Claim:
(Lemma 4.19), we have:

Using the Matrix Decomposition Lemma

(cid:21)P M P(cid:21) = (cid:21)P (γJ + λE)P (cid:21)

≤ γ · (cid:21)P JP (cid:21) + λ · (cid:21)P EP(cid:21)
≤ γ · (cid:21)P JP (cid:21) + λ

Thus, we only need to analyze the case of J, the random walk on the
complete graph. Given any vector x, let y = xP , so

xP JP = yJP =

yi

uP.

(cid:20)

(cid:21)

(cid:3)

i

Since (cid:21)y(cid:21) ≤ (cid:21)x(cid:21) and y has at most µN nonzero coordinates, we have
(cid:28)(cid:7)

(cid:3)

(cid:30)

(cid:29)

(cid:21)xP JP (cid:21) ≤

· (cid:21)uP (cid:21) ≤

µN · (cid:21)y(cid:21)

·

≤ µ · (cid:21)x(cid:21).

µ
N

(cid:12)
(cid:12)
(cid:12)
(cid:12)
(cid:12)

(cid:12)
(cid:12)
(cid:12)
(cid:12)
(cid:12)

yi

i

Thus,

(cid:21)P M P(cid:21) ≤γ · µ + λ = µ + λ · (1 − µ).

Using Claims 4.20 and 4.21, the probability of never leaving B in a

(t − 1)-step random walk is

|uP (M P )t−1|1 ≤
≤

µN · (cid:21)uP (M P )t−1(cid:21)
µN · (cid:21)uP (cid:21) · (cid:21)P M P(cid:21) t−1

(cid:7)

(cid:7)



<!-- pdf-page: 101 -->
98 Expander Graphs

(cid:7)

≤

µN ·

(cid:30)

µ
N

· (µ + λ · (1 − µ))t−1

≤ (µ + λ · (1 − µ))t.

The hitting properties described above suﬃce for reducing the error
of RP algorithms. What about BPP algorithms, which have two-sided
error? They are handled by the following.

Theorem 4.22(Chernoﬀ Bound for Expander Walks). Let G be
a regular digraph with N vertices and spectral expansion 1 − λ, and
let f : [N ] → [0, 1] be any function. Consider a random walk V1, . . . , Vt
in G from a uniform start vertex V1. Then for any ε >0

(cid:24)(cid:12)
(cid:12)
(cid:12)
(cid:12)
(cid:12)

Pr

1
t

(cid:3)

i

f (Vi) − µ(f )

(cid:12)
(cid:12)
(cid:12)
(cid:12)
(cid:12)

(cid:25)

≥ λ + ε

≤ 2e−Ω(ε2t).

Note that this is just like the standard Chernoﬀ Bound (Theo-
rem 2.21), except that our additive approximation error increases by
λ = 1 − γ. Thus, unlike the Hitting Property we proved above, this
bound is only useful when λ is suﬃciently small (as opposed to bounded
away from 1). This can be achieved by taking the a power of the initial
expander, where edges correspond to walks of length t in the original
expander; this raises the random-walk matrix and λ to the tth power.
However, there is a better Chernoﬀ Bound for Expander Walks, where
λ does not appear in the approximation error, but the exponent in
the probability of error is Ω(γε2t) instead of Ω(ε2t). The bound above
suﬃces in the common case that a small constant approximation error
can be tolerated, as in error reduction for BPP.

(cid:4)

Proof. Let Xi be the random variable f (Vi), and X =
i Xi. Just like
in the standard proof of the Chernoﬀ Bound (Problem 2.7), we show
(cid:31)
i erXi
that the expectation of the moment generating function erX =
is not much larger than er E[X] and apply Markov’s Inequality, for a
suitable choice of r. However, here the factors erXi are not indepen-
dent, so the expectation does not commute with the product. Instead,
we express E[erX ] linear-algebraically as follows. Deﬁne a diagonal



<!-- pdf-page: 102 -->
4.2 Random Walks on Expanders

99

matrix P whose (i, i)th entry is erf (i). Then, similarly Claim 4.20 in
the proof of the hitting proof above, we observe that
(cid:12)
(cid:12)u(M P )t

N · (cid:21)u(cid:21) · (cid:21)M P (cid:21)t = (cid:21)M P (cid:21)t.

(cid:12)
(cid:12)uP (M P )t−1

E[erX ] =

√

≤

(cid:12)
(cid:12)

(cid:12)
(cid:12)

1 =

1

To see this, we simply note that each cross-term in the matrix product
uP (M P )t−1 corresponds to exactly one expander walk v1, . . . , vt, with
i ef (vi). By
a coeﬃcient equal to the probability of this walk times
the Matrix Decomposition Lemma (Lemma 4.19), we can bound

(cid:31)

(cid:21)M P (cid:21) ≤(1 − λ) · (cid:21)JP (cid:21) + λ · (cid:21)EP (cid:21).

Since J simply projects onto the uniform direction, we have

(cid:21)uP (cid:21)2
(cid:21)u(cid:21)2
(cid:4)
v(er·f (v)/N )2
(cid:4)
v(1/N )2
(cid:3)

·

e2rf (v)

(cid:21)JP (cid:21)2 =

=

=

=

1
N

1
N

v
= 1 + 2rµ + O(r2)

v
(cid:3)

·

(1 + 2rf (v) +O (r2))

for r ≤ 1, and thus

(cid:21)JP (cid:21) =

(cid:7)

1 + 2rµ + O(r2) = 1 + rµ + O(r2).

For the error term, we have

(cid:21)EP (cid:21) ≤ (cid:21)P (cid:21) ≤e r = 1 + r + O(r2).

Thus,

(cid:21)M P (cid:21) ≤(1 − λ) · (1 + rµ + O(r2)) + λ · (1 + r + O(r2))

≤ 1 + (µ + λ)r + O(r2),

and we have

E[erX ] ≤ (1 + (µ + λ)r + O(r2))t ≤ e(µ+λ)rt+O(r2t).



<!-- pdf-page: 103 -->
100 Expander Graphs

By Markov’s Inequality,

Pr[X ≥ (µ + λ + ε) · t] ≤ e−εrt+O(r2t) = e−Ω(ε2t),

if we set r = ε/c for a large enough constant c. By applying the same
analysis to the function 1 − f , we see that Pr[X ≤ (µ − λ − ε)t] =
e−Ω(ε2t), and this establishes the theorem.

We now summarize the properties that expander walks give us for

randomness-eﬃcient error reduction and sampling.

For reducing the error of a BPP algorithm from 1/3 to 2−k, we can
apply Theorem 4.22 with λ = ε = 1/12, so that a walk of length t =
O(k) suﬃces. If the original BPP algorithm used m random bits and
the expander is of constant degree (which is possible with λ = 1/12),
then the number of random bits needed is only m + O(k). Comparing
with previous methods for error reduction, we have:

Number of
Repetitions Random Bits

Number of

Independent Repetitions
Pairwise Independent Repetitions
Expander Walks

O(k)
O(2k)
O(k)

O(km)
O(k + m)
m + O(k)

For Sampling, where we are given an oracle to a function
f : {0, 1}m → [0, 1] and we want to approximate µ(f ) to within an addi-
tive error of ε, we can apply Theorem 4.22 with error ε/2 and λ = ε/2.
The needed expander can be obtained by taking an O(log(1/ε))th
power of a constant-degree expander, yielding the following bounds:

Number of
Samples

Number of
Random Bits

Truly Random Sample O((1/ε2) · log(1/δ))
Pairwise Independent

O((1/ε2) · (1/δ))

O(m · (1/ε2) · log(1/δ))
O(m + log(1/ε) + log(1/δ))

Samples

Expander Walks

O((1/ε2) · log(1/δ)) m + O(log(1/δ) · (log(1/ε)/ε2))



<!-- pdf-page: 104 -->
4.2 Random Walks on Expanders

101

The log(1/ε) factor in the number of random bits comes because we
took an O(log(1/ε))th power of a constant-degree expander and thus
spend O(log(1/ε)) random bits for each step on the expander. This
is actually not necessary and comes from the slightly weaker Chernoﬀ
Bound we proved. In any case, note that expander walks have a much
better dependence on the error probability δ in the number of samples
(as compared to pairwise independence), but have a worse dependence
on the approximation error ε in the number of random bits. Problem 4.5
shows how to combine these two samplers to achieve the best of both.
Similarly to pairwise independence, the sampling algorithm based
on expander walks is actually an averaging sampler in the sense of
Deﬁnition 3.29:

Theorem 4.23 (Expander-Walk Sampler). For every m ∈ N and
δ, ε ∈ [0, 1],
there is a (δ, ε) averaging sampler Samp : {0, 1}n →
({0, 1}m)t using n = m + O(log(1/δ) · log(1/ε)/ε2) random bits and
t = O((1/ε2) · log(1/δ)) samples.

The sampling algorithm of Problem 4.5 that combines expander
walks and pairwise independence, however, is not an averaging sampler,
and it is an open problem to achieve similar parameters with an explicit
averaging sampler:

Open Problem 4.24. Give an explicit construction of a (δ, ε) averag-
ing sampler Samp : {0, 1}n → ({0, 1}m)t that uses n = O(m + log(δ) +
log(1/ε)) random bits and t = O((1/ε2) · log(1/δ)) samples.

Before we end this section, we make an important remark: we have
not actually given an eﬃcient algorithm for randomness-eﬃcient error
reduction (or an explicit averaging sampler)! Our algorithm assumes an
expander graph of exponential size, namely 2m where m is the number
of random bits used by the algorithm. Generating such a graph at ran-
dom would use far too many coins. Even generating it deterministically
would not suﬃce, since we would have to write down an exponential-
size object. In the following section, we will see how to deﬁne an explicit



<!-- pdf-page: 105 -->
102 Expander Graphs

expander graph without writing it down in its entirety, and eﬃciently
do random walks in such a graph.

4.3 Explicit Constructions

As discussed in previous sections, expander graphs have numerous
applications in theoretical computer science. (See also the Chapter
Notes and Exercises.) For some of these applications, it may be accept-
able to simply choose the graph at random, as we know that a random
graph will be a good expander with high probability. For many appli-
cations, however, this simple approach does not suﬃce. Some reasons
are the following (in increasing order of signiﬁcance):

• We may not want to tolerate the error probability introduced
by the (unlikely) event that the graph is not an expander.
To deal with this, we could try checking that the graph is
an expander. Computing the expansion of a given graph is
NP-hard for most of the combinatorial measures (e.g., ver-
tex expansion or edge expansion), but the spectral expansion
can be computed to high precision in time polynomial in the
size of the graph (as it is just an eigenvalue computation).
As we saw, spectral expansion does yield estimates on ver-
tex expansion and edge expansion (but cannot give optimal
expansion in these measures).

• Some of the applications of expanders (like the one from the
previous section) are for reducing the amount of randomness
needed for certain tasks. Thus choosing the graph at random
defeats the purpose.

• A number of the applications require exponentially large
expander graphs, and thus we cannot even write down a
randomly chosen expander. For example, for randomness-
eﬃcient error reduction of randomized algorithms, we need
an expander on 2m nodes where m is the number of random
bits used by the algorithm.

From a more philosophical perspective, ﬁnding explicit constructions
is a way of developing and measuring our understanding of these
important combinatorial objects.



<!-- pdf-page: 106 -->
4.3 Explicit Constructions

103

A couple of alternatives for deﬁning explicit constructions of

expanders on N nodes are:

Mildly Explicit: Construct a complete representation of the graph

in time poly(N ).

Fully Explicit: Given a node u ∈ [N ] and i ∈ [D], where D is the
degree of the expander, compute the ith neighbor of u in time
poly(log N ).

Consider the randomness-eﬃcient error reduction application discussed
in the previous section, in which we performed a random walk on an
expander graph with exponentially many nodes. Mild explicitness is
insuﬃcient for this application, as the desired expander graph is of
exponential size, and hence cannot be even entirely stored, let alone
constructed. But full explicitness is perfectly suited for eﬃciently con-
ducting a random walk on a huge graph. So now our goal is the
following:

Goal: Devise a fully explicit construction of an inﬁnite family {Gi}
of D-regular graphs with spectral expansion at least γ, where D and
γ > 0 are constants independent of i.

We remark that we would also like the set {Ni}, where Ni is the
number of vertices in Gi, to be not too sparse, so that the family of
graphs {Gi} has graphs of size close to any desired size.

4.3.1 Algebraic Constructions

Here we mention a few known explicit constructions that are of interest
because of their simple description, the parameters achieved, and/or
the mathematics that goes into their analysis. We will not prove the
expansion properties of any of these constructions (but will rather give
a diﬀerent explicit construction in the subsequent sections).

Construction 4.25(discrete torus expanders). Let G = (V, E) be
the graph with vertex set V = ZM × ZM , and edges from each node
(x, y) to the nodes (x, y), (x + 1, y), (x, y + 1), (x, x + y), (−y, x), where
all arithmetic is modulo M .



<!-- pdf-page: 107 -->
104 Expander Graphs

This is a fully explicit 5-regular digraph with N = M 2 nodes and
spectral expansion γ = Ω(1). It can be made undirected by adding
a reverse copy of each edge. We refer to these as “discrete torus”
expanders because Z2
M can be viewed as a discrete version of the real
torus, namely [0, 1]2 with arithmetic modulo 1. The expansion of these
graphs was originally proved using group representation theory, but
later proofs for similar discrete-torus expanders were found that only
rely on Fourier analysis over the torus.

Construction 4.26 (p-cycle with inverse chords). This is the
graph G = (V, E) with vertex set V = Zp and edges that connect each
node x with the nodes: x + 1, x − 1, and x−1 (where all arithmetic is
mod p and we deﬁne 0−1 to be 0).

This graph is only mildly explicit since we do not know how to con-
struct n-bit primes deterministically in time poly(n) (though Cram´er’s
conjecture in Number Theory would imply that we can do so by simply
checking the ﬁrst poly(n) n-bit numbers). The proof of expansion relies
on the “Selberg 3/16 Theorem” from number theory.

Construction 4.27 (Ramanujan graphs). G = (V, E) is a graph
with vertex set V = Fq ∪ {∞}, the ﬁnite ﬁeld of prime order q s.t.
q ≡ 1 mod 4 plus one extra node representing inﬁnity. The edges in
this graph connect each node z with all z(cid:3) of the form:

z(cid:3) =

(a0 + ia1)z + (a2 + ia3)
(−a2 + ia3)z + (a0 − ia1)
1 + a2

2 + a2

for a0, a1, a2, a3 ∈ Z such that a2
0 + a2
3 = p, a0 is odd and pos-
itive, and a1, a2, a3 are even, for some ﬁxed prime p (cid:1)= q such that p ≡ 1
mod 4, q is a square modulo p, and i ∈ Fq such that i2 = −1 modq .

1 + a2
√

The degree of the graph is the number of solutions to the equa-
tion a2
0 + a2
3 = p, which turns out to be D = p + 1, and it
has λ(G) ≤ 2
spectral expander. (See
Theorems 4.11 and 4.12, and note that this bound is even better than
we know for random graphs, which have an additive O(1) term in the

2 + a2
D − 1/D, so it is anoptimal



<!-- pdf-page: 108 -->
spectral expansion.) These graphs are also only mildly explicit, again
due to the need to ﬁnd the prime q.

4.3 Explicit Constructions

105

These are called Ramanujan Graphs because the proof of their
spectral expansion relies on results in number theory concerning the
“Ramanujan Conjectures.” Subsequently, the term Ramanujan graphs
came to refer to any inﬁnite family of graphs with optimal spectral
expansion γ ≥ 1 − 2

D − 1/D.

√

4.3.2 Graph Operations

The explicit construction of expanders given in the next section will
be an iterative one, where we start with a “constant size” expander H
and repeatedly apply graph operations to get bigger expanders. The
operations that we apply should increase the number of nodes in the
graph, while keeping the degree and the second eigenvalue λ bounded.
We’ll see three operations, each improving one property while paying a
price on the others; however, combined together, they yield the desired
expander. It turns out that this approach for constructing expanders
will also be useful in derandomizing the logspace algorithm for Undi-
rected S-T Connectivity, as we will see in Section 4.4.

The following concise notation will be useful to keep track of each

of the parameters:

Deﬁnition 4.28. An (N, D, γ)-graph is a D-regular digraph on N ver-
tices with spectral expansion γ.

4.3.2.1 Squaring

Deﬁnition 4.29(Squaring of Graphs). If G = (V, E) is aD -regular
digraph, then G2 = (V, E(cid:3)) is aD 2-regular digraph on the same vertex
set, where the (i, j)th neighbor of a vertex x is the jth neighbor of the
ith neighbor of x. In particular, a random step on G2 consists of two
random steps on G.



<!-- pdf-page: 109 -->
106 Expander Graphs

Lemma 4.30. If G is a (N, D, 1 − λ)-graph, then G2 is a (N, D2, 1 −
λ2)-graph.

Namely, the degree deteriorates by squaring, while the spectral

expansion is improved from γ = 1 − λ to γ(cid:3) = 1 − λ2 = 2γ − γ2.

Proof. The eﬀect of squaring on the number of nodes N and the degree
D is immediate from the deﬁnition. For the spectral expansion, note
that if M is the random-walk matrix for G, then M 2 is the random-walk
matrix for G2. So for any vector x ⊥ u,

(cid:21)xM 2(cid:21) ≤λ · (cid:21)xM (cid:21) ≤λ 2 · (cid:21)x(cid:21).

4.3.2.2 Tensoring

The next operation we consider increases the size of the graph at the
price of increasing the degree.

Deﬁnition 4.31 (Tensor Product of Graphs). Let G1 = (V1, E1)
be D1-regular and G2 = (V2, E2) beD 2-regular. Then their tensor
product is the D1D2-regular graph G1 ⊗ G2 = (V1 × V2, E), where the
(i1, i2)th neighbor of a vertex (x1, x2) is (y1, y2), where yb is the ibth
neighbor of xb in Gb. That is, a random step on G1 ⊗ G2 consists of a
random step on G1 in the ﬁrst component and a random step on G2 in
the second component.

Often this operation is simply called the “product” of G1 and G2,
but we use “tensor product” to avoid confusion with squaring and
to reﬂect its connection with the standard tensor products in linear
algebra:

Deﬁnition 4.32 (Tensor Products of Vectors and Matrices).
Let x ∈ RN1, y ∈ RN2, then their tensor product is the vector z =
x ⊗ y ∈ RN1N2 where zij = xiyj.



<!-- pdf-page: 110 -->
4.3 Explicit Constructions

107

Similarly,

for matrices A = (aij) ∈ RN1×N1, B = (bij) ∈ RN2×N2,
their tensor product is the matrix C = A ⊗ B ∈ RN1N2×N1N2 where
C = (cij,i(cid:2)j(cid:2)) for cij,i(cid:2)j(cid:2) = aii(cid:2)bjj(cid:2).

A few comments on the tensor operation:

• A random walk on a tensor graph G1 ⊗ G2 is equivalent to

taking two independent random walks on G1 and G2.

• For vectors x ∈ RN1, y ∈ RN2 that are probability distribu-
tions (i.e., nonnegative vectors with (cid:6)1 norm 1), their tensor
product x ⊗ y is a probability distribution on [N1] × [N2]
where the two components are independently distributed
according to x and y, respectively.

• (x ⊗ y)(A ⊗ B) = (xA) ⊗ (yB) for every x ∈ RN1, y ∈ RN2,
and in fact A ⊗ B is the unique matrix with this property.
• Not all vectors z ∈ RN1N2 are decomposable as x ⊗ y for x ∈
RN1 and y ∈ RN2. Nevertheless, the set of all decomposable
tensors x ⊗ y spans RN1N2.

• If M1, M2 are the random-walk matrices for graphs G1, G2
respectively, then the random-walk matrix for the graph
G1 ⊗ G2 is

M1 ⊗ M2 = (IN1 ⊗ M2)(M1 ⊗ IN2) = (M1 ⊗ IN2)(IN1 ⊗ M2),

where IN denotes the N × N identity matrix. That is, we
can view a random step on G1 ⊗ G2 as being a random step
on the G1 component followed by one on the G2 component
or vice-versa.

The eﬀect of tensoring on expanders is given by the following:

Lemma 4.33. If G1 is an (N1, D1, γ1)-graph and G2 is an (N2, D2, γ2)-
graph, then G1 ⊗ G2 is an (N1N2, D1D2, min{γ1, γ2})-graph.

In particular, if G1 = G2, then the number of nodes improves, the
degree deteriorates, and the spectral expansion remains unchanged.



<!-- pdf-page: 111 -->
108 Expander Graphs

Proof. As usual, we write γ1 = 1 − λ1, γ2 = 1 − λ2; then our goal is to
show that G1 ⊗ G2 has spectral expansion 1 − max{λ1, λ2}. The intu-
ition is as follows. We can think of the vertices of G1 ⊗ G2 as being par-
titioned into N1 “clouds,” each consisting of N2 vertices, where cloud
v1 contains all vertices of the form (v1, ·). Thus, any probability dis-
tribution (V1, V2) on the vertices (v1, v2) of G1 ⊗ G2 can be thought of
as picking a cloud v1 according to the marginal distribution2 V1 and
then picking the vertex v2 within the cloud v1 according to the con-
ditional distribution V2|V1=v1. If the overall distribution on pairs is far
from uniform, then either

(1) The marginal distribution V1 on the clouds must be far from

uniform, or

(2) the conditional distributions V2|V1=v1 within the clouds must

be far from uniform.

When we take a random step, the expansion of G1 will bring us closer
to uniform in Case 1 and the expansion of G2 will bring us closer to
uniform in Case 2.

One way to prove the bound in the case of undirected graphs is
to use the fact that the eigenvalues of M1 ⊗ M2 are all the products
of eigenvalues of M1 and M2, so the largest magnitude is 1 · 1 and
the next largest is bounded by either λ1 · 1 or 1 · λ2. Instead, we use
the Vector Decomposition Method to give a proof that matches the
intuition more closely and is a good warm-up for the analysis of the
zig-zag product in the next section. Given any vector x ∈ RN1N2 that is
orthogonal to uN1N2, we can decompose x as x = x(cid:15) + x⊥, where x(cid:15) is
a multiple of uN2 on each cloud of size N2 and x⊥ is orthogonal to uN2
on each cloud. Note that x(cid:15) = y ⊗ uN2, where y ∈ RN1 is orthogonal to
uN1 (because x(cid:15) = x − x⊥ is orthogonal to uN1N2). If we think of x as
the nonuniform component of a probability distribution, then x(cid:15) and
x⊥ correspond to the two cases in the intuition above.

For the ﬁrst case, we have

x(cid:15)M = (y ⊗ uN2)(M1 ⊗ M2) = (yM1) ⊗ uN2.

2 For two jointly distributed random variables (X, Y ), the marginal distribution of X is
simply the distribution of X alone, ignoring information about Y .



<!-- pdf-page: 112 -->
4.3 Explicit Constructions

109

The expansion of G1 tells us that M1 shrinks y by a factor of λ1, and
thus (cid:21)x(cid:15)M (cid:21) ≤λ 1 · (cid:21)x(cid:15)(cid:21). For the second case, we write

x⊥M = x⊥(IN1 ⊗ M2)(M1 ⊗ IN2).

The expansion of G2 tells us that M2 will shrink x⊥ by a factor of λ2 on
each cloud, and thus IN1 ⊗ M2 will shrink x⊥ by the same factor. The
subsequent application of M1 ⊗ IN2 cannot increase the length (being
the random-walk matrix for a regular graph, albeit a disconnected one).
Thus, (cid:21)x⊥M (cid:21) ≤λ 2(cid:21)x⊥(cid:21).

Finally, we argue that x(cid:15)M and x⊥M are orthogonal. Note that
x(cid:15)M = (yM1) ⊗ uN2 is a multiple of uN2 on every cloud. Thus it suﬃces
to argue that x⊥ remains orthogonal to uN2 on every cloud after we
apply M . Applying (IN1 ⊗ M2) retains this property (because applying
M2 preserves orthogonality to uN2, by regularity of G2) and applying
(M1 ⊗ IN2) retains this property because it assigns each cloud a linear
combination of several other clouds (and a linear combination of vectors
orthogonal to uN2 is also orthogonal to uN2).

Thus,

(cid:21)xM (cid:21)2 = (cid:21)x(cid:15)M (cid:21)2 + (cid:21)x⊥M (cid:21)2

· (cid:21)x⊥(cid:21)2

· (cid:21)x(cid:15)(cid:21)2 + λ2
≤ λ2
1
2
≤ max{λ1, λ2}2 · ((cid:21)x(cid:15)(cid:21)2 + (cid:21)x⊥(cid:21)2)
= max{λ1, λ2}2 · (cid:21)x(cid:21)2,

as desired.

4.3.2.3 The Zig–Zag Product

Of the two operations we have seen, one (squaring) improves expan-
sion and one (tensoring) increases size, but both have the deleterious
eﬀect of increasing the degree. Now we will see a third operation that
decreases the degree, without losing too much in the expansion. By
repeatedly applying these three operations, we will be able to con-
struct arbitrarily large expanders while keeping both the degree and
expansion constant.



<!-- pdf-page: 113 -->
110 Expander Graphs

Let G be an (N1, D1, γ1) expander and H be a (D1, D2, γ2) expander.
The zig–zag product of G and H, denoted G $z H, will be deﬁned as
follows. The nodes of G $z H are the pairs (u, i) where u ∈ V (G) and
i ∈ V (H). The edges of G $z H will be deﬁned so that a random step
on G $z H corresponds to a step on G, but using a random step on H
to choose the edge in G. (This is the reason why we require the number
of vertices in H to be equal to the degree of G.) A step in G $z H will
therefore involve a step to a random neighbor in H and then a step
in G to a neighbor whose index is equal to the label of the current
node in H. Intuitively, a random walk on a “good” expander graph
H should generate choices that are suﬃciently random to produce a
“good’ random walk on G. One problem with this deﬁnition is that it
is not symmetric. That is, the fact that you can go from (u, i) to (v, j)
does not mean that you can go from (v, j) to (u, i). We correct this by
adding another step in H after the step in G. In addition to allowing
us to construct undirected expander graphs, this extra step will also
turn out to be important for the expansion of G $z H.

More formally,

Deﬁnition 4.34 (Zig–Zag Product). Let G be an D1-regular
digraph on N1 vertices, and H a D2-regular digraph on D1 vertices.
Then G $z H is a graph whose vertices are pairs (u, i) ∈ [N1] × [D1].
For a, b ∈ [D2], the (a, b)th neighbor of a vertex (u, i) is the vertex (v, j)
computed as follows:

(1) Let i(cid:3) be the ath neighbor of i in H.
(2) Let v be the i(cid:3)th neighbor of u in G, soe = (u, v) is thei (cid:3)th
edge leaving u. Let j(cid:3) be such that e is the j(cid:3)th edge entering
v in G. (In an undirected graph, this simply means that u is
the j(cid:3)’th neighbor of v.)

(3) Let j be the b’th neighbor of j(cid:3) in H.

Note that the graph G $z H depends on how the edges leaving and
entering each vertex of G are numbered. Thus it is best thought of
as an operation on labelled graphs. (This is made more explicit in



<!-- pdf-page: 114 -->
Section 4.3.3 via the notion of an “edge-rotation map.”) Nevertheless,
the bound we will prove on expansion holds regardless of the labelling:

4.3 Explicit Constructions

111

Theorem 4.35. If G is a (N1, D1, γ1)-graph, and H is a (D1, D2, γ2)-
graph then G $z H is a (N1D1, D2
2 )-graph. In particular, if
γ1 = 1 − λ1 and γ2 = 1 − λ2, then γ = 1 − λ for λ ≤ λ1 + 2λ2.

2, γ = γ1 · γ2

G should be thought of as a big graph and H as a small graph, where
D1 is a large constant and D2 is a small constant. Note that the number
of nodes D1 in H is required to equal the degree of G. Observe that
when D1 > D2

2 the degree is reduced by the zig-zag product.
There are two diﬀerent intuitions underlying the expansion of the

zig–zag product:

• Given an initial distribution (U, I) on the vertices of G1

$z G2
that is far from uniform, there are two extreme cases, just as
in the intuition for the tensor product.3 Either
(1) All the (conditional) distributions I|U =u within the

clouds are far from uniform, or

(2) All the (conditional) distributions I|U =u within the
clouds of size D1 are uniform (in which case the
marginal distribution U on the clouds must be far
from uniform).

In Case 1, the ﬁrst H-step (U, I) (cid:14)→ (U, I (cid:3)) already brings us
closer to the uniform distribution, and the other two steps
cannot hurt (as they are steps on regular graphs). In Case 2,
the ﬁrst H-step has no eﬀect, but the G-step (U, I (cid:3)) (cid:14)→ (V, J (cid:3))
has the eﬀect of making the marginal distribution on clouds
closer to uniform, that is, V is closer to uniform than U .
But note that the joint distribution (V, J (cid:3)) isn’t actually any
$z G2
closer to the uniform distribution on the vertices of G1
because the G-step is a permutation. Still, if the marginal

3 Here we follow our convention of using capital letters to denote random variables corre-
sponding to the lower-case values in Deﬁnition 4.34.



<!-- pdf-page: 115 -->
112 Expander Graphs

distribution V on clouds is closer to uniform, then the con-
ditional distributions within the clouds J (cid:3)|V =v must have
become further from uniform, and thus the second H-step
(V, J (cid:3)) (cid:14)→ (V, J) brings us closer to uniform. This leads to a
proof by Vector Decomposition, where we decompose any vec-
tor x that is orthogonal to uniform into components x(cid:15) and
x⊥, where x(cid:15) is uniform on each cloud, and x⊥ is orthogonal
to uniform on each cloud. This approach gives the best known
bounds on the spectral expansion of the zig–zag product, but
it can be a bit messy since the two components generally do
not remain orthogonal after the steps of the zig–zag product
(unlike the case of the tensor product, where we were able to
show that x(cid:15)M is orthogonal to x⊥M ).

• The second intuition is to think of the expander H as behav-
ing “similarly” to the complete graph on D1 vertices (with
self-loops). In the case that H equals the complete graph,
then it is easy to see that G $z H = G ⊗ H. Thus it is natu-
ral to apply Matrix Decomposition, writing the random-walk
matrix for an arbitrary expander H as a convex combination
of the random-walk matrix for the complete graph and an
error matrix. This gives a very clean analysis, but slightly
worse bounds than the Vector Decomposition Method.

We now proceed with the formal proof, following the Matrix Decom-

position approach.

Proof of Theorem 4.35. Let A, B, and M be the random-walk matri-
$z G2, respectively. We decompose M into the
ces for G1, G2, and G1
product of three matrices, corresponding to the three steps in the def-
$z G2s edges. Let ˜B be the transition matrix for taking
inition of G1
a random G2-step on the second component of [N1] × [D1], that is,
˜B = IN1 ⊗ B, where IN1 is the N1 × N1 identity matrix. Let ˆA be the
permutation matrix corresponding to the G1-step. That is, ˆA(u,i),(v,j)
is 1 iﬀ (u, v) is thei th edge leaving u and the jth edge entering v. By
the deﬁnition of G1

$z G2, we haveM = ˜B ˆA ˜B.

By the Matrix Decomposition Lemma (Lemma 4.19), B = γ2J +
(1 − γ2)E, where every entry of J equals 1/D1 and E has norm at



<!-- pdf-page: 116 -->
4.3 Explicit Constructions

113

most 1. Then ˜B = γ2 ˜J + (1− γ2) ˜E, where ˜J = IN1 ⊗ J and ˜E = IN1 ⊗
E has norm at most 1.

This gives

M = (γ2 ˜J + (1− γ2) ˜E) ˆA(γ2 ˜J + (1− γ2) ˜E) =γ 2
2
where we take (1 − γ2
˜E; noting that their norms sum to at most (1 − γ2
norm at most 1. Now, the key observation is that ˜J ˆA ˜J = A ⊗ J.

2 )F to be the sum of the three terms involving
2 ), we see that F has

˜J ˆA ˜J + (1− γ2

2 )F,

Thus,

and thus

as desired.

M = γ2
2

· A ⊗ J + (1− γ2

2 )F,

· λ(A ⊗ J) + (1 − γ2
2 )

· (1 − γ1) + (1 − γ2
2 )

λ(M ) ≤ γ2
2
≤ γ2
2
= 1 − γ1γ2
2 ,

4.3.3 The Expander Construction

As a ﬁrst attempt for constructing a family of expanders, we construct
an inﬁnite family G1, G2, ... of graphs utilizing only the squaring and
the zig–zag operations:

Construction 4.36 (Mildly Explicit Expanders). Let H be a
(D4, D, 7/8)-graph (e.g., as constructed in Problem 4.8), and deﬁne:

G1 = H 2
Gt+1 = G2
t

$z H

Proposition 4.37. For all t, Gt is a (D4t, D2, 1/2)-graph.

Proof. By induction on t.

Base Case: by the deﬁnition of H and Lemma 4.30, G1 = H 2 is a

(D4, D2, 1 − λ2

0)-graph and λ2
0

≤ 1/2.



<!-- pdf-page: 117 -->
114 Expander Graphs

Induction Step: First note that G2
t

$z H is well-deﬁned because

deg(G2

t ) = deg(Gt)2 = (D2)2 = #nodes(H). Then,

deg(Gt+1) = deg(H)2 = D2

#nodes(Gt+1) = #nodes(G2

t ) · #nodes(H) =N t · D4 = D4tD4 = D4(t+1)

λ(Gt+1) ≤ λ(Gt)2 + 2λ(H) ≤ (1/2)2 + 2· (1/8) = 1/2

Now, we recursively bound the time to compute neighbors in Gt.
Actually, due to the way the G-step in the zig–zag product is deﬁned,
we bound the time to compute the edge-rotation map (u, i) (cid:14)→ (v, j),
where the ith edge leaving u equals the jth edge entering v. Denote
by time(Gt) the time required for one evaluation of the edge-rotation
map for Gt. This requires two evaluations of the edge-rotation map for
Gt−1 (the squaring requires two applications, while the zig–zag part
does not increase the number of applications), plus time poly(log Nt)
for manipulating strings of length O(log Nt). Therefore,
time(Gt) = 2 · time(Gt−1) + poly(log Nt)

= 2t · poly(log Nt)
= N Θ(1)
t

,

where the last equality holds because Nt = D4t for a constant D. Thus,
this construction is only mildly explicit.

We remedy the above diﬃculty by using tensoring to make the sizes

of the graphs grow more quickly:

Construction 4.38 (Fully Explicit Expanders). Let H be a
(D8, D, 7/8)-graph, and deﬁne:

G1 = H 2

Gt+1 = (Gt ⊗ Gt)2 $z H

In this family of graphs, the number of nodes grows doubly exponen-
, while the computation time grows only exponentially

tially Nt ≈ c2t
as before. Namely,

time(Gt) = 4t · poly(log Nt) = poly(log Nt).



<!-- pdf-page: 118 -->
4.3 Explicit Constructions

115

We remark that the above family is rather sparse, so the numbers
in {Nt} are far apart. To overcome this shortcoming, we can amend
the above deﬁnition to have

Gt = (G(cid:9)t/2(cid:10) ⊗ G(cid:13)t/2(cid:14))2 $z H.

Now Nt = D8t, so given a number N , we can ﬁnd a graph Gt
in
the family whose size is at most D8·N = O(N ). Moreover, the con-
struction remains fully explicit because time(Gt) =O (time(G(cid:9)t/2(cid:10)) +
time(G(cid:13)t/2(cid:14))) = poly(t). Thus we have established:

Theorem 4.39. There is a constant D ∈ N such that for every t ∈ N,
there is a fully explicit expander graph Gt with degree D, spectral
expansion 1/2, and Nt = D4t nodes.

Consequently, the randomness-eﬃcient error-reduction and averag-

ing sampler based on expander walks can be made explicit:

Corollary 4.40. If a language L has a BPP algorithm with error
probability at most 1/3 that uses m(n) random bits on inputs of length
n, then for every polynomial k(n), L has a BPP algorithm with error
probability at most 2−k(n) that uses m(n) +O (k(n)) random bits.

Corollary 4.41. There is an explicit averaging sampler achieving the
parameters of Theorem 4.23.

4.3.4 Open Problems

As we have seen, spectral expanders such as those in Theorem 4.39
are also vertex expanders (Theorem 4.6 and Corollary 4.10) and edge
expanders (Theorem 4.14), but these equivalences do not extend to
optimizing the various expansion measures.

As mentioned in Section 4.3.1, there are known explicit construc-
tions of optimal spectral expanders, namely Ramanujan graphs. How-
ever, unlike the expanders of Theorem 4.39, those constructions rely



<!-- pdf-page: 119 -->
116 Expander Graphs

on deep results in number theory. The lack of a more elementary con-
struction seems to signify a limitation in our understanding of expander
graphs.

Open Problem 4.42. Give an explicit “combinatorial” construction
of constant-degree expander graphs G with λ(G) ≤ 2
D − 1/D (or
even λ(G) =O (1/

D), where D is the degree.

√

√

For vertex expansion, it is known how to construct bipartite (or
directed) expanders with constant left-degree (or out-degree) D and
expansion (1 − ε) · D for an arbitrarily small constant ε (see Section 6),
but achieving the optimal expansion of D − O(1) (cf., Theorem 4.4) or
constructing undirected vertex expanders with high expansion remains
open.

Open Problem 4.43. For an arbitrarily large constant D, give an
explicit construction of bipartite (Ω(N ), D − c) vertex expanders with
N vertices on each side and left-degree D, where c is a universal con-
stant independent of D.

Open Problem 4.44. For an arbitrarily small constant ε >0, give an
explicit construction of undirected (Ω(N ), (1 − ε)D) vertex expanders
with N vertices and constant degree D that depends only on ε.

We remark that while Open Problem 4.43 refers to balanced bipar-
tite graphs (i.e., ones with the same number of vertices on each side),
the imbalanced case is also interesting and important. (See Prob-
lems 4.10, 5.5 and Open Problems 5.36, 6.35.)

4.4 Undirected S-T Connectivity in Deterministic Logspace

Recall the Undirected S-T Connectivity problem: Given an undi-
rected graph G and two vertices s, t, decide whether there is a path from
s to t. In Section 2.4, we saw that this problem can be solved in random-
ized logspace (RL). Here we will see how we can use expanders and the
operations above to solve this problem in deterministic logspace (L).



<!-- pdf-page: 120 -->
4.4 Undirected S-T Connectivity in Deterministic Logspace

117

The algorithm is based on the following two ideas:

• Undirected S-T Connectivity can be solved in logspace
on constant-degree expander graphs. More precisely, it is easy
on constant-degree graphs where every connected compo-
nent is promised to be an expander (i.e., has spectral expan-
sion bounded away from 1): we can try all paths of length
O(log N ) from s in logarithmic space; this works because
expanders have logarithmic diameter. (See Problem 4.2.)
• The same operations we used to construct an inﬁnite
expander family above can also be used to turn any graph
into an expander (in logarithmic space). Above, we started
with a constant-sized expander and used various operations
to build larger and larger expanders. There, the goal was
to increase the size of the graph (which was accomplished
by tensoring and/or zig–zag), while preserving the degree
and the expansion (which was accomplished by zig–zag and
squaring, which made up for losses in these parameters).
Here, we want to improve the expansion (which will be
accomplished by squaring), while preserving the degree (as
will be handled by zig–zag) and ensuring the graph remains
of polynomial size (so we will not use tensoring).

Speciﬁcally, the algorithm is as follows.

Algorithm 4.45 (Undirected S-T Connectivity in L).
Input: An undirected graph G with N edges and vertices s and t.

(1) Let H be a ﬁxed (D4, D, 3/4) graph for some constant D.
(2) Reduce (G, s, t) to (G0, s0, t0), where G0 is a D2-regular graph
in which every connected component is nonbipartite and s0
and t0 are connected in G0 iﬀ s and t are connected in G.

(3) For k = 1, . . . , (cid:6) = O(log N ), deﬁne:

$z H

(a) Let Gk = G2
(b) Let sk and tk be any two vertices in the “clouds”
of Gk corresponding to sk−1 and tk−1, respectively.

k−1



<!-- pdf-page: 121 -->
118 Expander Graphs

(Note that if sk and tk are connected in Gk, then
sk−1 and tk−1 are connected in Gk−1.)

(4) Try all paths of length O(log N ) in G(cid:4) from s(cid:4) and accept if

any of them visit t(cid:4).

$z H; below we will show that C2

We will discuss how to implement this algorithm in logspace later,
and ﬁrst analyze its correctness. Let Ck be the connected component
of Gk containing sk. Observe that Ck is a connected component of
$z H is connected and hence
C2
k−1
k−1
$z H. Since C0 is undirected, connected, and nonbipartite,
Ck = C2
we have γ(C0) ≥ 1/poly(N ) by Theorem 2.53. We will argue that in
each iteration the spectral gap increases by a constant factor, and thus
after O(log N ) iterations we have an expander.

k−1

By Lemma 4.30, we have

γ(C2

k−1) ≥ 2 · γ(Ck−1) · (1 − γ(Ck−1)/2) ≈ 2γ(Ck)

for small γ(Ck−1). By Theorem 4.35, we have

γ(C2

k−1

$z H) ≥ γ(H)2 · γ(C2
(cid:14)

k−1)

(cid:15)
2

≥

3
4

≥ min

· 2 · γ(Ck−1) · (1 − γ(Ck−1)/2)

(cid:6)

35
32

· γ(Ck−1),

1
18

,

where the last inequality is obtained by considering whether γ(Ck−1) ≤
$z H is connected, so we
1/18 or γ(Ck−1) > 1/18. In particular, C2
$z H and
have Ck = C2

k−1

k−1

γ(Ck) ≥ min

(cid:6)

35
32

· γ(Ck−1),

1
18

.

Thus, after (cid:6) = O(log N ) iterations, we must have γ(C(cid:4)) ≥ 1/18. More-
over, observe that the number of vertices N(cid:4) in G(cid:4) is at most N0 ·
(D4)(cid:4) = poly(N ), so considering paths of length O(log N ) will suﬃce
to decide s-t connectivity in G(cid:4).

 
 


<!-- pdf-page: 122 -->
4.4 Undirected S-T Connectivity in Deterministic Logspace

119

To show that the algorithm can be implemented in logarithmic
space, we argue that the edge-rotation map of each Gk can be com-
puted with only O(1) more space than the edge-rotation map of Gk−1,
so that G(cid:4) requires space O(log N ) +O ((cid:6)) =O (log N ). Since the induc-
tive claim here refers to sublogarithmic diﬀerences of space (indeed
O(1) space) and sublogarithmic space is model-dependent (even keep-
ing a pointer into the input requires logarithmic space), we will refer
to a speciﬁc model of computation in establishing it. (The ﬁnal result,
that Undirected S-T Connectivity is in L, is, however, model-
independent because logspace computations in any reasonable com-
putational model can be simulated by logspace computations in any
other reasonable model.) Formally, let space(Gk) denote the workspace
needed to compute the edge-rotation map of Gk on a multi-tape Turing
machine with the following input/output conventions:

• Input Description:

— Tape 1 (read-only): Contains the initial input graph
G, with the head at the leftmost position of the tape.

— Tape 2 (read–write): Contains the input pair (v, i),
where v is a vertex of Gi and i ∈ [D2] is an index of
the a neighbor on a read–write tape, with the head at
the rightmost position of i. The rest of the tape may
contain additional data.

— Tapes 3+ (read-write): Blank worktapes with the

head at the leftmost position.

• Output Description:

— Tape 1: The head should be returned to the leftmost

position.

— Tape 2: In place of (v, i), it should contain the output
(w, j) where w is the ith neighbor of v and v is the
jth neighbor of w. The head should be at the right-
most position of j and the rest of the tape should
remain unchanged from its state at the beginning of
the computation.



<!-- pdf-page: 123 -->
120 Expander Graphs

— Tapes 3+ (read–write): Are returned to the blank

state with the heads at the leftmost position.

k−1

$z H) = space(G2

k−1) +O (1). For G2

With these conventions, it is not diﬃcult to argue that space(G0) =
O(log N ), and space(Gk) = space(Gk−1) +O (1). For the latter, we
ﬁrst argue that space(G2
k−1) = space(Gk−1) +O (1), and then that
space(G2
k−1, we are given a
triple (v, (i1, i2)) on tape 2, with the head on the rightmost position
of i2, and both i1 and i2 are elements of [D2] (and thus of constant
size). We move the head left to the rightmost position of i1, compute
the edge-rotation map of Gk−1 on (v, i1) so that tape 2 now contains
(w, j1, i2). Then we swap j1 and i2, and run the edge-rotation map of
Gk−1 on (w, i2) to get (w, j2, j1), and move the head to the rightmost
$z H, we are given a
position of j1, completing the rotation. For G2
k−1
tuple ((v, i), (a1, a2)), where v is a vertex of G2
k−1, i is a vertex of H
(equivalently, an edge-label for G2
k−1), and a1, a2 are edge labels for H.
Evaluating the rotation map requires two evaluations of the rotation
map for H (both of which are “constant-size” operations) and one eval-
uation of the rotation map of G2
k−1.

Thus we have proven:

Theorem 4.46. Undirected S-T Connectivity is in L.

We remark that proving RL = L in general remains open. The
best deterministic simulation known for RL is essentially L3/2 =
DSPACE(log3/2 n), which makes beautiful use of known pseudoran-
dom generators for logspace computation. (Unfortunately, we do not
have space to cover this line of work in this survey.) Historically,
improved derandomizations for Undirected S-T Connectivity
have inspired improved derandomizations of RL (and vice-versa). Since
Theorem 4.46 is still quite recent (2005), there is a good chance that
we have not yet exhausted the ideas in it.

Open Problem 4.47. Show that RL ⊂ Lc for some constant c <3/2.

Another open problem is the construction of universal traversal
sequences — ﬁxed walks of polynomial length that are guaranteed to



<!-- pdf-page: 124 -->
4.5 Exercises

121

visit all vertices in any connected undirected regular graph of a given
size. (See Example 3.8 and Open Problem 3.9.) Using the ideas from
the algorithm above, it is possible to obtain logspace-constructible,
polynomial-length universal traversal sequences for all regular graphs
that are consistently labelled in the sense that no pair of distinct vertices
have the same i’th neighbor for any i ∈ [D]. For general labellings, the
best known universal traversal sequences are of length N O(log N ) (and
are constructible in space O(log2 N )).

Open Problem 4.48 (Open Problem 3.9, restated). Give an
explicit construction of universal traversal sequences of polynomial
length for arbitrarily labelled undirected graphs (or even for an arbi-
trary labelling of the complete graph).

We remark that handling general labellings (for “pseudorandom
walk generators” rather than universal traversal sequences) seems to
be the main obstacle in extending the techniques of Theorem 4.46 to
prove RL = L. (See the Chapter Notes and References.)

4.5 Exercises

Problem 4.1(Bipartite Versus Nonbipartite Expanders). Show
that constructing bipartite expanders is equivalent to constructing
(standard, nonbipartite) expanders. That is, show how given an explicit
construction of one of the following, you can obtain an explicit construc-
tion of the other:

(1) D-regular (αN, A) expanders on N vertices for inﬁnitely
many N , where α > 0, A >1, and D are constants indepen-
dent of N .

(2) D-regular (on both sides) (αN, A) bipartite expanders with
N vertices on each side for inﬁnitely many N , where α > 0,
A >1, and D are constants independent of N .

(Your transformations need not preserve the constants.)



<!-- pdf-page: 125 -->
122 Expander Graphs

Problem 4.2 (More Combinatorial Consequences of Spectral
Expansion). Let G be a graph on N vertices with spectral expansion
γ = 1 − λ. Prove that:

(1) The independence number α(G) is at most (λ/(1 + λ))N ,
where α(G) is deﬁned to be the size of the largest indepen-
dent set, i.e., subset S of vertices s.t. there are no edges with
both endpoints in S.

(2) The chromatic number χ(G) is at least (1 + λ)/λ, where
χ(G) is deﬁned to be the smallest number of colors for which
the vertices of G can be colored s.t. all pairs of adjacent ver-
tices have diﬀerent colors.

(3) The diameter of G is O(log1/λ N ).

Recall that computing α(G) and χ(G) exactly are NP-complete prob-
lems. However, the above shows that for expanders, nontrivial bounds
on these quantities can be computed in polynomial time.

Problem 4.3 (Limits on Vertex Expansion). This problem and
the next one give limits on the vertex and spectral expansion that can
be achieved as a function of the degree D. Both bounds are proved by
relating the expansion of an arbitrary D-regular graph G by that of
the inﬁnite D-regular tree TD (where every vertex has one parent and
D − 1 children), which is in some sense the “best possible” D-regular
expander.

(1) Show that if a D-regular digraph G is a (K, A) expander,

then TD is a (K, A) expander.

(2) Show that for every D ∈ N, there are inﬁnitely many K ∈ N

such that TD is not a (K, D − 1 + 2/K) expander.

(3) Deduce that for constant D ∈ N and α > 0, if a D-regular,
N -vertex digraph G is an (αN, A) vertex expander, then A ≤
D − 1 +O (1), where the O(1) term vanishes as N → ∞ (and
D, α are held constant).



<!-- pdf-page: 126 -->
4.5 Exercises

123

Problem 4.4 (Limits on Spectral Expansion). Let G be a D-
regular undirected graph and TD be the inﬁnite D-regular tree (as
in Problem 4.3). For a graph H and (cid:6) ∈ N, let p(cid:4)(H) denote the proba-
bility that if we choose a random vertex v in H and do a random walk
of length 2(cid:6), we end back at vertex v.

(1) Show that p(cid:4)(G) ≥ p(cid:4)(TD) ≥ C(cid:4) · (D − 1)(cid:4)/D2(cid:4), where C(cid:4) is
the (cid:6)th Catalan number, which equals the number of properly
parenthesized strings in {(, )}2(cid:4) — strings where no preﬁx has
more)s than (s.

(2) Show that N · p(cid:4)(G) ≤ 1 + (N − 1) · λ(G)2(cid:4). (Hint: use the
fact that the trace of a matrix equals the sum of its eigen-
values.)

(3) Using the fact that C(cid:4) =

(cid:1)

(cid:2)

2(cid:4)
(cid:4)
√

/((cid:6) + 1), prove that

D − 1
D

− O(1),

λ(G) ≥ 2

where the O(1) term vanishes as N → ∞ (and D is held
constant).

Problem 4.5 (Near-Optimal Sampling).

(1) Describe an algorithm for Sampling that tosses O(m +
coins, makes O((1/ε2) · log(1/δ))
log(1/ε) + log(1/δ))
queries to a function f : {0, 1}m → [0, 1], and estimates
µ(f ) to within ±ε with probability at least 1 − δ. (Hint:
use expander walks to generate several sequences of coin
tosses for the pairwise-independent averaging sampler, and
compute the answer via a “median of averages.”)

an explicit
3.9)

(2) Give
lem
n = O(m + log(1/ε) + log(1/δ))
t = O((1/ε) · log(1/δ)) samples.

(δ, ε) hitting
Samp : {0, 1}n → ({0, 1}m)t

sampler

coins

and

that

(see Prob-
tosses
generates



<!-- pdf-page: 127 -->
124 Expander Graphs

It turns out that these bounds on the randomness and query/sample
complexities are each optimal up to constant factors (for most param-
eter settings of interest).

Problem 4.6(Error Reduction For Free*). Show that if a problem
has a BPP algorithm with constant error probability, then it has a
BPP algorithm with error probability 1/n that uses exactly the same
number of random bits.

Problem 4.7 (Vertex Expanders versus Hitting Samplers).
Here we will see that hitting samplers (deﬁned in Problem 3.9) are
equivalent to a variant of vertex expanders, where we only require that
for (left-)sets S of size exactly K, there are at least A · K neighbors.
We call such graphs (= K, A) vertex expanders and will revisit them in
the next section (Deﬁnition 5.32).

Given a bipartite multigraph with neighbor function Γ : [N ] ×
[D] → [M ], we can obtain a sampler Samp : [N ] → [M ]D by setting
Samp(x)y = Γ(x, y). Conversely, every such sampler gives rise to a
bipartite multigraph. Prove that Samp is a (δ, ε) hitting sampler if
and only if Γ is an (= K, A) vertex expander for K = (cid:17)δN (cid:18) + 1 and
A = (1 − ε)M/K.

Thus, bipartite vertex expanders and hitting samplers are equiva-
lent. However, the typical settings of parameters for the two objects are
very diﬀerent. For example, in vertex expanders, a primary goal is usu-
ally to maximize the expansion factor A, but A · K may be signiﬁcantly
smaller than M . In samplers, AK = (1 − ε)M is usually taken to be
very close to M , but A = (1 − ε)M/δN may even be smaller than 1.
Similarly, the most common setting of expanders takes K/N ≈ δ to be a
constant, whereas in samplers it is often thought of as vanishingly small.

Problem 4.8 (A “Constant-Sized” Expander).

(1) Let F be a ﬁnite ﬁeld. Consider a graph G with vertex set F2
and edge set {((a, b), (c, d)) : ac = b + d}. That is, we connect



<!-- pdf-page: 128 -->
4.5 Exercises

125

vertex (a, b) to all points on the line y = ax − b. Prove that
G is |F|-regular and λ(G) ≤ 1/

|F|. (Hint: consider G2.)

(cid:7)

(2) Show that if |F|

is suﬃciently large (but still constant),
then by applying appropriate operations to G, we can
obtain a base graph for the expander construction given in
Section 4.3.3, i.e., a (D8, D, 7/8) graph for some constant D.

Problem 4.9 (The Replacement Product). Given a D1-regular
graph G1 on N1 vertices and a D2-regular graph G2 on D1 vertices,
$r G2 on vertex set [N1] × [D1]: vertex
consider the following graph G1
(u, i) is connected to (v, j) iﬀ (a)u = v and (i, j) is an edge in G2, or
(b) v is the i’th neighbor of u in G1 and u is the jth neighbor of v. That
is, we “replace” each vertex v in G1 with a copy of G2, associating each
edge incident to v with one vertex of G2.

(1) Prove that there is a function g such that if G1 has spec-
tral expansion γ1 > 0 and G2 has spectral expansion γ2 > 0
$r G2 has spectral
(and both graphs are undirected), then G1
$r G2)3 has
expansion g(γ1, γ2, D2) > 0. (Hint: Note that (G1
G1

$z G2 as a subgraph.)

(2) Show how to convert an explicit construction of constant-
degree (spectral) expanders into an explicit construction of
degree 3 (spectral) expanders.

(3) Without using Theorem 4.14, prove an analogue of Part 1 for
edge expansion. That is, there is a function h such that if G1
is an (N1/2, ε1) edge expander and G2 is a (D1/2, ε2) edge
$r G2 is a (N1D1/2, h(ε1, ε2, D2)) edge
expander, then G1
expander, where h(ε1, ε2, D2) > 0 if ε1, ε2 > 0. (Hint: given
$r G2, partition S into the clouds
any set S of vertices of G1
that are more than “half-full” and those that are not.)
(4) Prove that the functions g(γ1, γ2, D2) and h(ε1, ε2, D2) must
$r G2 cannot be a

depend on D2, by showing that G1
(N1D1/2, ε) edge expander if ε >1/(D 2 + 1) and N1 ≥ 2.



<!-- pdf-page: 129 -->
126 Expander Graphs

Problem 4.10(Unbalanced Vertex Expanders and Data Struc-
tures). Consider a (K, (1 − ε)D) bipartite vertex expander G with N
left vertices, M right vertices, and left degree D.

(1) For a set S of left vertices, a y ∈ N (S) is called a unique
neighbor of S if y is incident to exactly one edge from S.
Prove that every left-set S of size at most K has at least
(1 − 2ε)D|S| unique neighbors.

(2) For a set S of size at most K/2, prove that at most |S|/2
vertices outside S have at least δD neighbors in N (S), for
δ = O(ε).

Now we’ll see a beautiful application of such expanders to data
structures. Suppose we want to store a small subset S of a large universe
[N ] such that we can test membership in S by probing just 1 bit of our
data structure. A trivial way to achieve this is to store the characteristic
vector of S, but this requires N bits of storage. The hashing-based data
structures mentioned in Section 3.5.3 only require storing O(|S|) words,
each of O(log N ) bits, but testing membership requires reading an entire
word (rather than just one bit.)

Our data structure will consist of M bits, which we think of as a
{0, 1}-assignment to the right vertices of our expander. This assignment
will have the following property.

Property Π: For all left vertices x, all but a δ = O(ε) fraction of the
neighbors of x are assigned the value χS(x) (where χS(x) = 1
iﬀ x ∈ S).

(3) Show that if we store an assignment satisfying Property Π,
then we can probabilistically test membership in S with error
probability δ by reading just one bit of the data structure.

(4) Show that an assignment satisfying Property Π exists pro-
vided |S| ≤K/ 2. (Hint: ﬁrst assign 1 to all of Ss neighbors
and 0 to all its nonneighbors, then try to correct the errors.)

It turns out that the needed expanders exist with M = O(K log N )
(for any constant ε), so the size of this data structure matches the



<!-- pdf-page: 130 -->
4.6 Chapter Notes and References

127

hashing-based scheme while admitting (randomized) 1-bit probes. How-
ever, note that such bipartite vertex expanders do not follow from
explicit spectral expanders as given in Theorem 4.39, because the latter
do not provide vertex expansion beyond D/2 nor do they yield highly
imbalanced expanders (with M   N ) as needed here. But in Section 5,
we will see how to explicitly construct expanders that are quite good
for this application (speciﬁcally, with M = K1.01 · polylogN ).

4.6 Chapter Notes and References

A detailed coverage of expander graphs and their applications in theo-
retical computer science is given by Hoory, Linial, and Wigderson [207].
Applications in pure mathematics are surveyed by Lubotzky [276].

The ﬁrst papers on expander graphs appeared in conferences on
telephone networks. Speciﬁcally, Pinsker [309] proved that random
graphs are good expanders, and used these to demonstrate the existence
of graphs called “concentrators.” Bassalygo [52] improved Pinsker’s
results, in particular giving the general tradeoﬀ between the degree D,
expansion factor A, and set density α mentioned after Theorem 4.4.
The ﬁrst computer science application of expanders (and “supercon-
centrators”) came in an approach by Valiant [403] to proving circuit
lower bounds. An early and striking algorithmic application was the
O(log n)-depth sorting network by Ajtai, Koml´os, and Szemer´edi [10],
which also illustrated the usefulness of expanders for derandomization.
An exciting recent application of expanders is Dinur’s new proof of the
PCP Theorem [118].

The fact that spectral expansion implies vertex expansion and edge
expansion was shown by Tanner [385] (for vertex expansion) and Alon
and Milman [23] (for edge expansion). The converses are discrete ana-
logues of Cheeger’s Inequality for Riemannian manifolds [94], and var-
ious forms of these were proven by Alon [15] (for vertex expansion),
Jerrum and Sinclair [219] (for edge expansion in undirected graphs
and, more generally, conductance in reversible Markov chains), and
Mihail [286] (for edge expansion in regular digraphs and conductance
in nonreversible Markov chains).



<!-- pdf-page: 131 -->
128 Expander Graphs

The “Ramanujan” upper bound on spectral expansion given by
Theorem 4.11 was proven by Alon and Boppana (see [15, 297]). Theo-
rem 4.12, stating that random graphs are asymptotically Ramanujan,
was conjectured by Alon [15], but was only proven recently by
Friedman [143]. Kahale [228] proved that Ramanujan graphs have
vertex expansion roughly D/2 for small sets.

Forms of the Expander Mixing Lemma date back to Alon and
Chung [18], who considered the number of edges between a set and
its complement (i.e., T = V \S). The converse to the Expander Mix-
ing Lemma (Theorem 4.16) is due to Bilu and Linial [68]. For more
on quasirandomness, see [25, 104] for the case of dense graphs and
[100, 101] for sparse graphs.

The sampling properties of random walks on expanders were ana-
lyzed in a series of works starting with Ajtai, Koml´os, and Sze-
mer´edi [11]. The hitting bound of Theorem 4.17 is due to Kahale [228],
and the Chernoﬀ Bound for expander walks (cf., Theorem 4.22) is due
to Gillman [153]. Our proof of the Chernoﬀ Bound is inspired by that
of Healy [203], who also provides some other variants and generaliza-
tions. The RP version of Problem 4.6 is due to Karp, Pippenger, and
Sipser [234], who initiated the study of randomness-eﬃcient error reduc-
tion of randomized algorithms. It was generalized to BPP in [107]. The
equivalence of hitting samplers and bipartite vertex expanders from
Problem 4.7 is due to Sipser [365]. Problem 4.5 is due to Bellare, Gol-
dreich, and Goldwasser [55]; matching lower bounds for sampling were
given by Canetti, Even, and Goldreich [91]. Open Problem 4.24 was
posed by Bellare and Rompel [57].

Construction 4.25 is due to Margulis [283], and was the ﬁrst explicit
construction of constant-degree expanders. Gabber and Galil [146] (see
also [221]) gave a much more elementary proof of expansion for sim-
ilar expanders, which also provided a speciﬁc bound on the spectral
expansion (unlike Margulis’ proof). Construction 4.26 is variant of
a construction of Lubotzky, Phillips, and Sarnak. (See [275, Thm.
4.42], from which the expansion of Construction 4.26 can be deduced.)
Ramanujan graphs (Construction 4.27) were constructed independently
by Lubotzky, Phillips, and Sarnak [277] and Margulis [284]. For more



<!-- pdf-page: 132 -->
4.6 Chapter Notes and References

129

on Ramanujan graphs and the mathematical machinery that goes into
their analysis, see the books [112, 348, 275].

The zig–zag product and the expander constructions of Section 4.3.3
are due to Reingold, Vadhan, and Wigderson [333]. Our analysis of
the zig–zag product is from [331], which in turn builds on [338], who
used matrix decomposition (Lemma 4.19) for analyzing other graph
products. Earlier uses of graph products in constructing expanders
include the use of the tensor product in [385]. Problem 4.9, on the
replacement product, is from [331, 333], and can be used in place
of the zig–zag product in both the expander constructions and the
Undirected S-T Connectivity algorithm (Algorithm 4.45). Inde-
pendently of [333], Martin and Randall [285] proved a “decomposition
theorem” for Markov chains that implies a better bound on the spectral
expansion of the replacement product.

√

√

There has been substantial progress on giving a combinatorial
construction of Ramanujan graphs (Open Problem 4.42). Bilu and
Linial [68] give a mildly explicit construction achieving λ(G) = ˜O(
D),
Ben-Aroya and Ta-Shma [58] give a fully explicit construction achiev-
ing λ(G) =D 1/2+o(1), and Batson, Spielman, and Srivastava [53] give
a mildly explicit construction of a weighted graph achieving λ(G) =
O(

D).
Constant-degree bipartite expanders with expansion (1 − ε)·D have
been constructed by Capalbo et al. [92], based on a variant of the zig–
zag product for “randomness condensers.” (See Section 6.3.5.) Alon and
Capalbo [17] have made progress on Open Problem 4.44 by giving an
explicit construction of undirected constant-degree “unique-neighbor”
expanders (see Problem 4.10).

The deterministic logspace algorithm for Undirected S-T Con-
nectivity (Algorithm 4.45) is due to Reingold [327]. The result
that RL ⊂ L3/2 is due to Saks and Zhou [344], with an important
ingredient being Nisan’s pseudorandom generator for space-bounded
computation [299]. Based on Algorithm 4.45, explicit polynomial-
length universal traversal sequences for “consistently labelled” regular
digraphs, as well as “pseudorandom walk generators” for such graphs,
were constructed in [327, 331]. (See also [338].) In [331], it is shown
that pseudorandom walk generators for arbitrarily labelled regular



<!-- pdf-page: 133 -->
130 Expander Graphs

digraphs would imply RL = L. The best known explicit construction
of a full-ﬂedged universal traversal sequence is due to Nisan [299], has
length nO(log n), and can be constructed in time nO(log n) and space
O(log2 n). (See Section 8.2.1 for more on the derandomization of RL.)
Problem 4.8, Part 1 is a variant of a construction of Alon [16];
Part 4.8 is from [333]. The results of Problem 4.2 are from [23, 103,
205, 268]. The result of Problem 4.10, on bit-probe data structures for
set membership, is due to Buhrman, Miltersen, Radhakrishnan, and
Venkatesan [87].



<!-- pdf-page: 134 -->
5

List-Decodable Codes

The ﬁeld of coding theory is motivated by the problem of communicat-
ing reliably over noisy channels — where the data sent over the channel
may come out corrupted on the other end, but we nevertheless want
the receiver to be able to correct the errors and recover the original
message. There is a vast literature studying aspects of this problem
from the perspectives of electrical engineering (communications and
information theory), computer science (algorithms and complexity),
and mathematics (combinatorics and algebra). In this survey, we are
interested in codes as “pseudorandom objects.” In particular, a general-
ization of the notion of an error-correcting code yields a framework that
we will use to unify all of the main pseudorandom objects covered in
this survey (averaging samplers, expander graphs, randomness extrac-
tors, list-decodable codes, pseudorandom generators).

5.1 Deﬁnitions and Existence

5.1.1 Deﬁnition

The approach to communicating over a noisy channel is to restrict the
data we send to be from a certain set of strings that can be easily
disambiguated (even after being corrupted).

131



<!-- pdf-page: 135 -->
132 List-Decodable Codes

Deﬁnition 5.1. A q-ary code is a multiset1 C ⊂ Σˆn, where Σ is an
alphabet of size q. Elements of C are called codewords. We deﬁne the
following key parameters:

• ˆn is the block length.
• n = log |C| is the message length.
• ρ = n/(ˆn · log |Σ|) is the(relative) rate of the code.

An

function

encoding

bijective mapping
Enc : {1, . . . , |C|} → C. Given such an encoding function, we view
the elements of {1, . . . , |C|} as messages. When n = log |C| is an integer,
we often think of messages as strings in {0, 1}n.

for

an

is

C

We view C and Enc as being essentially the same object (with Enc
merely providing a “labelling” of codewords), with the former being
useful for studying the combinatorics of codes and the latter for algo-
rithmic purposes.

We remark that our notation diﬀers from the standard notation in
coding theory in several ways. Typically in coding theory, the input
alphabet is taken to be the same as the output alphabet (rather than
{0, 1} and Σ, respectively), the blocklength is denoted n, and the mes-
sage length (over Σ) is denoted k and is referred to as the rate. Our
notational choices are made in part to facilitate stating connections to
other pseudorandom objects covered in this survey.

So far, we haven’t talked at all about the error-correcting properties
of codes. Here we need to specify two things: the model of errors (as
introduced by the noisy channel) and the notion of a successful recovery.
For the errors, the main distinction is between random errors and
worst-case errors. For random errors, one needs to specify a stochastic
model of the channel. The most basic one is the binary symmetric chan-
nel (over alphabet Σ = {0, 1}), where each bit is ﬂipped independently
with probability δ. People also study more complex channel models,

1 Traditionally, codes are deﬁned to be sets rather than multisets. However, the generality
aﬀorded by multisets will allow the connections we see later to be stated more cleanly.
In the case C is a multiset, the condition that a mapping Enc : {1, . . . , N } → C is bijective
means that for every c ∈ C, |Enc−1(c)| equals the multiplicity of c in C.



<!-- pdf-page: 136 -->
5.1 Deﬁnitions and Existence

133

but as usual with stochastic models, there is always the question of
how well the theoretical model correctly captures the real-life distri-
bution of errors. We, however, will focus on worst-case errors, where
we simply assume that fewer than a δ fraction of symbols have been
changed. That is, when we send a codeword c ∈ Σˆn over the channel,
the received word r ∈ Σˆn diﬀers from c in fewer than δˆn places. Equiv-
alently, c and r are close in Hamming distance:

Deﬁnition 5.2 (Hamming distance). For two strings x, y ∈ Σˆn,
their (relative) Hamming distance dH (x, y) equals Pri[xi (cid:1)= yi]. The
agreement is deﬁned to be agr(x, y) = 1 − dH (x, y).

For a string x ∈ Σˆn and δ ∈ [0, 1], the (open) Hamming ball of
radius δ around x is the set B(x, δ) of strings y ∈ Σˆn such that
dH (x, y) < δ.

For the notion of a successful recovery, the traditional model
requires that we can uniquely decode the message from the received
word (in the case of random errors, this need only hold with high prob-
ability). Our main focus will be on a more relaxed notion which allows
us to produce a small list of candidate messages. As we will see, the
advantage of such list decoding is that it allows us to correct a larger
fraction of errors.

Deﬁnition 5.3. Let Enc : {0, 1}n → Σˆn be an encoding algorithm
for a codeC . A δ-decoding algorithm for Enc is a function Dec :
Σˆn → {0, 1}n such that for every m ∈ {0, 1}n and r ∈ Σˆn satisfying
dH (Enc(m), r) < δ, we have Dec(r) =m. If such a function Dec exists,
we call the code δ-decodable.

A (δ, L)-list-decoding algorithm for Enc is a function Dec : Σˆn →
({0, 1}n)L such that for every m ∈ {0, 1}n and r ∈ Σˆn satisfying
dH (Enc(m), r) < δ, we havem ∈ Dec(r). If such a function Dec exists,
we call the code (δ, L)-list-decodable.

Note that a δ-decoding algorithm is the same as a (δ, 1)-list-
decoding algorithm. It is not hard to see that, if we do not care about



<!-- pdf-page: 137 -->
134 List-Decodable Codes

computational eﬃciency, the existence of such decoding algorithms
depends only on the combinatorics of the set of codewords.

Deﬁnition 5.4. The (relative) minimum distance of a codeC ⊂ Σˆn
equals minx(cid:11)=y∈C dH (x, y).2

Proposition 5.5. Let C ⊂ Σˆn be a code with any encoding function
Enc.

(1) For δˆn ∈ N, Enc is δ-decodable iﬀ its minimum distance is at

least 2δ − 1/ˆn.

(2) Enc is (δ, L)-list-decodable iﬀ for every r ∈ Σˆn, we have

|B(r, δ) ∩ C| ≤ L.

Proof. Item 2 follows readily from the deﬁnitions.

For Item 1, ﬁrst note that Enc is δ-decodable iﬀ there is no received
word r ∈ Σˆn at distance less than δ from two codewords c1, c2. (Such
an r should decode to both c1 and c2, which is impossible for a unique
decoder.) If the code has minimum distance at least 2δ − 1/ˆn, then
c1 and c2 disagree in at least 2δˆn − 1 positions, which implies that r
disagrees with one of them in at least δˆn positions. (Recall that δˆn is an
integer by hypothesis.) Conversely, if the code has minimum distance
smaller than 2δ − 1/ˆn, then there are two codewords that disagree in
at most 2δˆn − 2 positions, and we can construct r that disagrees with
each in at most δˆn − 1 positions.

Because of the factor of 2 in Item 1, unique decoding is only possible
at distances up to 1/2, whereas we will see that list decoding is possible
at distances approaching 1 (with small lists).

The main goals in constructing codes are to have inﬁnite families of

codes (e.g., for every message length n) in which we:

2 If any codeword appears in C with multiplicity greater than 1, then the minimum distance
is deﬁned to be zero.



<!-- pdf-page: 138 -->
5.1 Deﬁnitions and Existence

135

• Maximize the fraction δ of errors correctible (e.g., constant

independent of n and ˆn).

• Maximize the rate ρ (e.g., a constant independent of n

and ˆn).

• Minimize the alphabet size q (e.g., a constant, ideally q = 2).
• Keep the list size L relatively small (e.g., a constant or

poly(n)).

• Have computationally eﬃcient encoding and decoding

algorithms.

In particular, coding theorists are very interested in obtaining the
optimal tradeoﬀ between the constants δ and ρ with eﬃciently encod-
able and decodable codes.

5.1.2 Existential Bounds

Like expanders, the existence of very good codes can be shown using
the probabilistic method. The bounds will be stated in terms of the
q-ary entropy functions, so we begin by deﬁning those.

Deﬁnition 5.6. For q, ˆn ∈ N and δ ∈ [0, 1], we deﬁne Hq(δ, ˆn) ∈ [0, 1]
to be such that |B(x, δ)| = qHq(δ,ˆn)·ˆn for x ∈ Σˆn, where Σ is an alphabet
of size q.

We also deﬁne the q-ary entropy function Hq(δ) =δ · logq((q −

1)/δ) + (1 − δ) · logq(1/(1 − δ)).

The reason we use similar notation for Hq(δ, ˆn) and Hq(δ) is Part 1

of the following:

Proposition 5.7. For every q ∈ N, δ ∈ (0, 1 − 1/q), ε ∈ [0, 1/2],

(1) limˆn→∞ Hq(δ, ˆn) =H q(δ).
(2) Hq(δ) ≤ H2(δ)/ log q + δ.
(3) H2(1/2 − ε) = 1 − Θ(ε2).



<!-- pdf-page: 139 -->
136 List-Decodable Codes

Now we state the bounds for random error-correcting codes.

Theorem 5.8.

(1) For all ˆn, q ∈ N and δ ∈ (0, 1 − 1/q), there exists a q-ary code
of block length ˆn, minimum distance at least δ, and rate at
least ρ = 1 − Hq(δ, ˆn).

(2) For all integers ˆn, q, L ∈ N and δ ∈ (0, 1 − 1/q), there exists
a (δ, L)-list-decodable q-ary code of block length ˆn and rate
at least ρ = 1 − Hq(δ, ˆn) − 1/(L + 1).

Proof.

(1) Pick the codewords c1, . . . , cN in sequence ensuring that ci
is at distance at least δ from c1, . . . , ci−1. The union of
the Hamming balls of radius δ around c1, . . . , ci−1 contains
at most (i − 1) · qHq(δ,ˆn)·ˆn < (N − 1) · qHq(δ,ˆn)·ˆn, so there is
always a choice of ci outside these balls if we take N =
(cid:15)q(1−Hq(δ,ˆn))·ˆn(cid:16).

(2) We use the probabilistic method. Choose the N codewords
randomly and independently from Σˆn. The probability that
there is a Hamming Ball of radius δ containing at least L + 1
codewords is at most
(cid:15)

(cid:20)

(cid:21)

(cid:15)

(cid:14)

(cid:14)

L+1

q ˆn ·

N
L + 1

·

qHq(δ,ˆn)·ˆn
q ˆn

≤

N − 1
q(1−Hq(δ,ˆn)−1/(L+1))·ˆn

L+1

,

which is less than 1 if we take N = (cid:15)q(1−Hq(δ,ˆn)−1/(L+1))·ˆn(cid:16).

Note that while the rate bounds are essentially the same for achiev-
ing minimum distance δ and achieving list-decoding radius δ (as we take
large list size), the bounds are incomparable because minimum distance
δ only corresponds to unique decoding up to radius roughly δ/2. The
bound for list decoding is known to be tight up to the dependence on L
(Problem 5.1), while the bound on minimum distance is not tight in
general. Indeed, there are families of “algebraic-geometric” codes with



<!-- pdf-page: 140 -->
5.1 Deﬁnitions and Existence

137

constant alphabet size q, constant minimum distance δ > 0, and con-
stant rate ρ >0 where ρ >1 − Hq(δ, ˆn) for suﬃciently large ˆn. (Thus,
this is a rare counterexample to the phenomenon “random is best.”)
Identifying the best tradeoﬀ between rate and minimum distance, even
for binary codes, is a long-standing open problem in coding theory.

Open Problem 5.9. For each constant δ ∈ (0, 1), identify the largest
ρ >0 such that for every ε >0, there exists an inﬁnite family of codes
Cˆn ⊂ {0, 1}ˆn of rate at least ρ − ε and minimum distance at least δ.

Let’s look at some special cases of the parameters in Theorem 5.8.
For binary codes (q = 2), we will be most interested in the case
δ → 1/2, which corresponds to correcting the maximum possible frac-
tion of errors for binary codes. (No nontrivial decoding is possible
for binary codes at distance greater than 1/2, since a completely
random received word will be at distance roughly 1/2 with most code-
words.) In this case, Proposition 5.7 tells us that the rate approaches
1 − H2(1/2 − ε) = Θ(ε2), i.e., the blocklength is ˆn = Θ(n/ε2) (for list
size L = Θ(1/ε2)). For large alphabets q, Proposition 5.7 tells us that
the rate approaches 1 − δ as q grows. We will be most interested in
the case δ = 1 − ε for small ε, so we can correct a δ = 1 − ε fraction of
errors with a rate arbitrarily close to ε. For example, we can achieve
rate of ρ = 0.99ε, a list size of L = O(1/ε) and an alphabet of size
poly(1/ε). More generally, it is possible to achieve rate ρ = (1 − γ)ε
with an alphabet size of q = (1/ε)O(1/γ).

While we are primarily interested in list-decodable codes, minimum
distance is often easier to bound. The following allows us to translate
bounds on minimum distance into bounds on list-decodability.

Proposition 5.10 (Johnson Bound).

(1) If C has minimum distance 1 − ε,

then it

is

(1 −

√

√

O(

ε), O(1/

ε))-list-decodable.

(2) If a binary code C has minimum distance 1/2 − ε, then it is

√

(1/2 − O(

ε), O(1/ε))-list-decodable.



<!-- pdf-page: 141 -->
138 List-Decodable Codes

Proof. We prove Item 1, and leave Item 2 as an exercise in the next
section (Problem 6.3). The proof is by inclusion–exclusion. Suppose for
contradiction that there are codewords c1, . . . , cs at distance less than
√
1 − ε(cid:3) from some r ∈ Σˆn, for ε(cid:3) = 2

ε and s = (cid:15)2/ε(cid:3)(cid:16). Then:

1 ≥ fraction of positions where r agrees with some ci

(cid:3)

agr(ci, cj)

1≤i<j≤s

(cid:3)

≥

agr(r, ci) −

i

> sε(cid:3) −

(cid:15)

(cid:14)

s
2

· ε

≥ 2 − 1 = 1,

where the last inequality is by our setting of parameters. Hence,
contradiction.

Note the quadratic loss in the distance parameter. This means that
optimal codes with respect to minimum distance are not necessarily
optimal with respect to list decoding. Nevertheless, if we do not care
about the exact tradeoﬀ between the rate and the decoding radius, the
above can yield codes where the decoding radius is as large as possible
(approaching 1 for large alphabets and 1/2 for binary alphabets).

5.1.3 Explicit Codes

As usual, most applications of error-correcting codes (in particular the
original motivating one) require computationally eﬃcient encoding and
decoding. For now, we focus on only the eﬃciency of encoding.

Deﬁnition 5.11. A code Enc : {0, 1}n → Σˆn is (fully) explicit if given
a message m ∈ {0, 1}n and an index i ∈ ˆn, the ith symbol of Enc(m)
can be computed in time poly(n, log ˆn, log |Σ|).

The reason we talk about computing individual symbols of the code-
word rather than the entire codeword is to have a meaningful deﬁnition
even for codes where the blocklength ˆn is superpolynomial in the mes-
sage length n. One can also consider weaker notions of explicitness,



<!-- pdf-page: 142 -->
5.1 Deﬁnitions and Existence

139

where we simply require that the entire codeword Enc(m) can be com-
puted in time poly(ˆn, log |Σ|).

The constructions of codes that we describe will involve arithmetic
over ﬁnite ﬁelds. See Remark 3.25 for the complexity of constructing
ﬁnite ﬁelds and carrying out arithmetic in such ﬁelds .

In describing the explicit constructions below, it will be convenient
to think of the codewords as functions c : [ˆn] → Σ rather than as strings
in Σˆn.

Construction 5.12 (Hadamard Code). For n ∈ N, the (binary)
Hadamard code of message length n is the binary code of blocklength
→ Z2 that are linear (modulo 2).
ˆn = 2n consisting of all functions c : Zn
2

Proposition 5.13. The Hadamard code:

(1) is explicit with respect to the encoding function that takes a
2 to the linear function cm deﬁned by cm(x) =

message m ∈ Zn
(cid:4)
i mixi mod 2.

(2) has minimum distance 1/2, and
(3) is (1/2 − ε, O(1/ε2)) list-decodable for every ε >0.

Proof. Explicitness is clear by inspection. The minimum distance
follows from the fact that for every two distinct linear functions
c, c(cid:3) : Zn
→ Z2, Prx[c(x) =c (cid:3)(x)] = Prx[(c − c(cid:3))(x) = 0] = 1/2. The list-
2
decodability follows from the Johnson Bound.

The advantages of the Hadamard code are its small alphabet
(binary) and optimal distance (1/2), but unfortunately its rate is expo-
nentially small (ρ = n/2n). By increasing both the ﬁeld size and degree,
we can obtain complementary properties

Construction 5.14 (Reed–Solomon Codes). For a prime power q
and d ∈ N, the q-ary Reed–Solomon code of degree d is the code of
blocklength ˆn = q and message length n = (d + 1)· log q consisting of
all polynomials p : Fq → Fq of degree at most d.



<!-- pdf-page: 143 -->
140 List-Decodable Codes

Proposition 5.15. The q-ary Reed–Solomon Code of degree d:

(1) is explicit with respect to the encoding function that takes a
vector of coeﬃcients m ∈ Fd+1
to the polynomial pm deﬁned
(cid:4)
d
i=0 mixi (assuming we have a description of
by pm(x) =
the ﬁeld Fq).
(cid:7)

(2) has minimum distance δ = 1 − d/q, and
(3) is (1 − O(

q/d)) list-decodable.

d/q), O(

(cid:7)

q

Proof. Again explicitness follows by inspection. The minimum distance
follows from the fact that two distinct polynomials of degree at most d
agree in at most d points (else their diﬀerence would have more than d
roots). The list-decodability follows from the Johnson Bound.

Note that by setting q = O(d), Reed–Solomon codes simultaneously
achieve constant rate and constant distance, the only disadvantage
being that the alphabet is of nonconstant size (namely q = ˆn > n.)

Another useful setting of parameters for Reed–Solomon codes
in complexity theory is q = poly(d), which gives polynomial rate
(ˆn = poly(n)) and distance tending to 1 polynomially fast (δ = 1 − 1/
poly(n)).

The following codes “interpolate” between Hadamard and Reed–
Solomon codes, by allowing the number of variables, the degree, and
ﬁeld size all to vary.

Construction 5.16 (Reed–Muller Codes). For a prime power q
and d, m ∈ N, the q-ary Reed–Muller code of degree d and dimension m
· log q
is the code of blocklength ˆn = qm and message length n =
consisting of all polynomials p : Fm
→ Fq of (total) degree at most d.
q

(cid:2)
m+d
d

(cid:1)

Proposition 5.17. The q-ary Reed–Muller Code of degree d and
dimension m:



<!-- pdf-page: 144 -->
5.2 List-Decoding Algorithms

141

(1) is explicit with respect to the encoding function that takes

a vector of coeﬃcients v ∈ F(m+d
d )
nomial pv.

q

to the corresponding poly-

(2) has minimum distance δ ≥ 1 − d/q, and
(3) is (1 − O(

q/d)) list-decodable.

d/q), O(

(cid:7)

(cid:7)

Proof. Same as for Reed–Solomon Codes, except we use the Schwartz–
Zippel Lemma (Lemma 2.4) to deduce the minimum distance.

Note that Reed–Solomon Codes are simply Reed–Muller codes of
dimension m = 1, and Hadamard codes are essentially Reed–Muller
codes of degree d = 1 and alphabet size q = 2 (except that the Reed–
Muller code also contains aﬃne linear functions).

5.2 List-Decoding Algorithms

In this section, we will describe eﬃcient list-decoding algorithms for the
Reed–Solomon code and variants. It will be convenient to work with
the following notation:

Deﬁnition 5.18.
Enc : {1, . . . , N } →Σ ˆn. For
agr(Enc(m), r) > ε}.

Let C be a code with encoding function
r ∈ Σˆn, deﬁne LIST(r, ε) ={m ∈ Σˆn :

Then the task of (1 − ε) list decoding (according to Deﬁnition 5.3)
is equivalent to producing the elements of LIST(r, ε) given r ∈ Σˆn. In
this section, we will see algorithms that do this in time polynomial in
the bit-length of r, i.e., time poly(ˆn, log |Σ|).

5.2.1 Review of Algebra

The list-decoding algorithms will require some additional algebraic
facts and notation:

• For every ﬁeld F, F[X1, . . . , Xn] is the integral domain con-
sisting of formal polynomials Q(X1, . . . , Xn) with coeﬃcients



<!-- pdf-page: 145 -->
142 List-Decodable Codes

in F, where addition and multiplication of polynomials is
deﬁned in the usual way.

• A nonzero polynomial Q(X1, . . . , Xn) isirreducible if we can-
not write Q = RS, where R, S are nonconstant polynomials.
For a ﬁnite ﬁeld Fq of characteristic p and d ∈ N, a univariate
irreducible polynomial of degree d over Fq can be found in
deterministically in time poly(p, log q, d).

• F[X1, . . . , Xn] is aunique factorization domain . That is, every
nonzero polynomial Q can be factored as Q = Q1Q2 · · · Qm,
where each Qi is irreducible and this factorization is unique
up to reordering and multiplication by constants from
F. Given the description of a ﬁnite ﬁeld F
pk and the
polynomial Q, this factorization can be done probabilisti-
cally in time poly(log p, k, |Q|) and deterministically in time
poly(p, k, |Q|).

• For a nonzero polynomial Q(Y, Z) ∈ F[Y, Z] and f (Y ) ∈ F[Y ],
if Q(Y, f (Y )) = 0, then Z − f (Y ) is one of the irreducible
factors of Q(Y, Z) (and thus f (Y ) can be found in polynomial
time). This is analogous to the fact that if c ∈ Z is a root of
an integer polynomial Q(Z), then Z − c is one of the factors
of Q (and can be proven in the same way, by long division).

5.2.2 List-Decoding Reed–Solomon Codes

Theorem 5.19. There is a polynomial-time (1 − ε) list-decoding algo-
rithm for the q-ary Reed–Solomon code of degree d, for ε = 2
d/q.
That is, given a function r : Fq → Fq and d ∈ N, all polynomials of
degree at most d that agree with r on more than εq = 2
dq inputs
can be found in polynomial time.

(cid:7)

√

In fact the constant of 2 can be improved to 1, matching the com-
binatorial list-decoding radius for Reed–Solomon codes given by an
optimized form of the Johnson Bound. See Problem 5.6.

Proof. We are given a received word r : Fq → Fq, and want to ﬁnd all
elements of LIST(r, ε) for ε = 2
d/q.

(cid:7)



<!-- pdf-page: 146 -->
5.2 List-Decoding Algorithms

143

Step 1: Find a low-degree Q “explaining” r. Speciﬁcally,
Q(Y, Z) will be a nonzero bivariate polynomial of degree at most dY
in its ﬁrst variable Y and dZ in its second variable, with the prop-
erty that Q(y, r(y)) = 0 for all y ∈ Fq. Each such y imposes a linear
constraint on the (dY + 1)(dZ + 1) coeﬃcients of Q. Thus, this system
has a nonzero solution provided (dY + 1)(dZ + 1) > q, and it can be
found in polynomial time by linear algebra (over Fq).

Step 2: Argue that each f (Y ) ∈ LIST(r, ε) is a “root” of Q.
it will be the case that Q(Y, f (Y )) = 0 for each f ∈
Speciﬁcally,
LIST(r, ε). The reason is that Q(Y, f (Y )) is a univariate polynomial
of degree at most dY + d · dZ, and has more than εq zeroes (one for
each place that f and r agree). Thus, we can conclude Q(Y, f (Y )) = 0
provided εq ≥ dY + d · dZ. Then we can enumerate all of the elements
of LIST(r, ε) by factoring Q(Y, Z) and taking all the factors of the form
Z − f (Y ).

For this algorithm to work, the two conditions we need to satisfy

are

and

(dY + 1)(dZ + 1) > q,

εq ≥ dY + d · dZ.

These conditions can be satisﬁed by setting dY = (cid:17)εq/2(cid:18), dZ =

(cid:7)

(cid:17)εq/(2d)(cid:18), and ε = 2

d/q.

Note that the rate of Reed–Solomon codes is ρ = (d + 1)/q = Θ(ε2).
The alphabet size is q = ˜Ω(n/ρ) = ˜Ω(n/ε2). In contrast, the random
codes of Theorem 5.8 achieve ρ ≈ ε and q = poly(1/ε). It is not known
whether the ε =
d/q bound on the list-decodability of Reed–Solomon
codes can be improved, even with ineﬃcient decoding.

(cid:7)

√

Open Problem 5.20. Do there exist constants ε, ρ ∈ (0, 1) with
ε <
ρ and an inﬁnite sequence of prime powers q such that the
q-ary Reed–Solomon code of degree d = (cid:17)ρq(cid:18) is (1 − ε, poly(q))-list-
decodable?



<!-- pdf-page: 147 -->
144 List-Decodable Codes

5.2.3 Parvaresh–Vardy Codes

Our aim is to improve the rate-distance tradeoﬀ to ρ = ˜Θ(ε). Intuitively,
the power of the Reed–Solomon list-decoding algorithm comes from the
fact that we can interpolate the q points (y, r(y)) of the received word
using a bivariate polynomial Q of degree roughly
q in each variable
(think of d = O(1) for now). If we could use m variables instead of 2,
then the degrees would only have to be around q1/m.

√

First attempt: Replace Step 1 with ﬁnding an (m + 1)-variate poly-
nomial Q(Y, Z1, . . . , Zm) of degree dY in Y and dZ in each Zi such
that Q(y, r(y), r(y), . . . , r(y)) = 0 for every y ∈ Fq. Then, we will be
able to choose a nonzero polynomial Q of degree roughly q1/m such
that Q(Y, f (Y ), . . . , f (Y )) = 0 for every f ∈ LIST(r, ε), and hence it
follows that Z − f (Y ) divides the bivariate polynomial Q∗(Y, Z) =
Q(Y, Z, . . . , Z). Unfortunately, Q∗ might be the zero polynomial even
if Q is nonzero.

Second attempt: Replace Step 1 with ﬁnding an (m + 1)-variate
polynomial Q(Y, Z1, . . . , Zm) of degree dY in Y and dZ = h − 1 in each
Zi such that Q(y, r(y), r(y)h, r(y)h2
) = 0 for every y ∈ Fq.
Then, it follows that Q∗(Y, Z) =Q(Y, Z, Z h, . . . , Zhm−1
) is nonzero if Q
is nonzero because every monomial in Q with individual degrees at most
h − 1 in Z1, . . . , Zm gets mapped to a diﬀerent power of Z. However,
here the diﬃculty is that the degree of Q∗(Y, f (Y )) is too high (roughly
d∗ = dY + d · hm > dm

Z ) for us to satisfy the constraint εq ≥ d∗.

, . . . , r(y)hm−1

Parvaresh–Vardy codes get the best of both worlds by provid-
ing more information with each symbol — not just the evaluation
of f at each point, but the evaluation of m − 1 other polynomials
f1, . . . , fm−1, each of which is still of degree d (as is good for arguing
that Q(Y, f (Y ), f1(Y ), . . . , fm−1(Y )) = 0, but can be viewed as raising
f to successive powers of h for the purposes of ensuring that Q∗ is
nonzero.

To introduce this idea, we need some additional algebra.

• For univariate polynomials f (Y ) and E(Y ), we deﬁne
f (Y ) modE (Y ) to be the remainder when f is divided by E.



<!-- pdf-page: 148 -->
5.2 List-Decoding Algorithms

145

If E(Y ) is of degree k, then f (Y ) modE (Y ) is of degree at
most k − 1.

• The ring F[Y ]/E(Y ) consists of all polynomials of degree at
most k − 1 with arithmetic modulo E(Y ) (analogous to Zn
consisting of integers smaller than n with arithmetic mod-
ulo n). If E is irreducible, then F[Y ]/E(Y ) is a ﬁeld (anal-
ogous to Zp being a ﬁeld when p is prime). Indeed, this is
how the ﬁnite ﬁeld of size pk is constructed: take F = Zp and
E(Y ) to be an irreducible polynomial of degree k over Zp,
and then F[Y ]/E(Y ) is the (unique) ﬁeld of size pk.

• A multivariate polynomial Q(Y, Z1, . . . , Zm) can be reduced
modulo E(Y ) by writing it as a polynomial in variables
Z1, . . . , Zm with coeﬃcients in F[Y ] and then reducing each
coeﬃcient modulo E(Y ). After reducing Q modulo E, we
think of Q as a polynomial in variables Z1, . . . , Zm with coef-
ﬁcients in the ﬁeld F[Y ]/E(Y ).

Construction 5.21 (Parvaresh–Vardy Codes). For a prime
power q, integers m, d, h ∈ N, and an irreducible polynomial E(Y ) of
degree larger than d, the q-ary Parvaresh–Vardy Code of degree d,
power h, redundancy m, and irreducible E is deﬁned as follows:

• The alphabet is Σ = Fm
q .
• The blocklength is ˆn = q.
• The message space is Fd+1

, where we view each message as
representing a polynomial f (Y ) of degree at most d over Fq.

q

• For y ∈ Fq, the yth symbol of the Enc(f ) is

[f0(y), f1(y), . . . , fm−1(y)],

where fi(Y ) =f (Y )hi

mod E(Y ).

Theorem 5.22. For every prime power q, integer 0 ≤ d < q, and irre-
ducible polynomial E of degree d + 1, the q-ary Parvaresh–Vardy code
of degree d, redundancy m = (cid:15)log(q/d)(cid:16), power h = 2, and irreducible E



<!-- pdf-page: 149 -->
146 List-Decodable Codes

has rate ρ = ˜Ω(d/q) and can be list-decoded in polynomial time up to
distance δ = 1 − ˜O(d/q).

Proof. We are given a received word r : Fq → Fm
elements of LIST(r, ε), for some ε = ˜O(d/q).

q , and want to ﬁnd all

Step 1: Find a low-degree Q “explaining” r. We ﬁnd a nonzero
polynomial Q(Y, Z0, . . . , Zm−1) of degree at most dY in its ﬁrst vari-
able Y and at most h − 1 in each of the remaining variables, and sat-
isfying Q(y, r(y)) = 0 for all y ∈ Fq.

Such a Q exists and can be found by linear algebra in time poly(q, m)

provided that:

dY · hm > q.

(5.1)

Moreover, we may assume that Q is not divisible by E(Y ). If it is,
we can divide out all the factors of E(Y ), which will not aﬀect the
conditions Q(y, r(y)) = 0 since E has no roots (being irreducible).

Step 2: Argue that each f (Y ) ∈ LIST(r, ε) is a “root” of a related
univariate polynomial Q∗. First, we argue as before that for f ∈
LIST(r, ε), we have

Q(Y, f0(Y ), . . . , fm−1(Y )) = 0.
Since each fi has degree at most deg(E) − 1 =d, this will be ensured
provided

(5.2)

εq ≥ dY + (h − 1) · d · m.

(5.3)

Once we have this, we can reduce both sides of Equation (5.2) mod-

ulo E(Y ) and deduce

0 =Q(Y, f 0(Y ), f1(Y ), . . . , fm−1(Y )) mod E(Y )

= Q(Y, f (Y ), f (Y )h, . . . , f (Y )hm−1

) modE (Y )

Thus, if we deﬁne the univariate polynomial

Q∗(Z) =Q(Y, Z, Z h, . . . , Zhm−1

) modE (Y ),

then f (Y ) is a root of Q∗ over the ﬁeld Fq[Y ]/E(Y ).



<!-- pdf-page: 150 -->
5.2 List-Decoding Algorithms

147

Observe that Q∗ is nonzero because Q is not divisible by E(Y ) and
has degree at most h − 1 in each Zi. Thus, we can ﬁnd all elements
of LIST(r, ε) by factoring Q∗(Z). Constructing Q∗(Z) and factoring it
can be done in time poly(q, d, hm) = poly(q).

For this algorithm to work, we need to satisfy Conditions (5.1) and
(5.3). We can satisfy Condition (5.3) by setting dY = (cid:15)εq − dhm(cid:16), in
which case Condition (5.1) is satisﬁed for

ε =

1
hm +

dhm
q

= ˜O(d/q),

(5.4)

for h = 2 and m = (cid:15)log(q/d)(cid:16). Observing that the rate is ρ = d/(mq) =
˜Ω(d/q), this completes the proof of the theorem.

Note that the obstacles to obtaining a tradeoﬀ ρ ≈ ε are the factor
of m in expression for the rate ρ = d/(mq) and the factor of hm in
Equation (5.4) for ε. We remedy these in the next section.

5.2.4 Folded Reed–Solomon Codes

In this section, we show how to obtain an optimal rate-distance tradeoﬀ,
where the rate ρ is arbitrarily close to the agreement parameter ε.

Consider

the Parvaresh–Vardy construction with polynomial
E(Y ) =Y q−1 − γ, where γ is a generator of the multiplicative group F∗
q;
it can be shown that E(Y ) is irreducible. (That is, {γ, γ2, . . . , γq−1} =
Fq \ {0}.) Then it turns out that f q(Y ) modE (Y ) =f (Y q) mod
E(Y ) =f (γY ). So, we set h = q and the degree of fi(Y ) =f hi
(Y ) mod
E(Y ) =f (γiY ) isd even though E has degree q − 1. For each nonzero
element y of Fq, the yth symbol of the PV encoding of f (Y ) is then

[f (y), f (γy), . . . , f (γm−1y)] = [f (γj), f (γj+1), . . . , f (γj+m−1)],

(5.5)

where we write y = γj.

Thus, the symbols of the PV encoding have a lot of overlap. For
example, the γjth symbol and the γj+1th symbol share all but one
component. Intuitively, this means that we should only have to send a
1/m fraction of the symbols of the codeword, saving us a factor of m
in the rate. (The other symbols can be automatically ﬁlled in by the



<!-- pdf-page: 151 -->
148 List-Decodable Codes

receiver.) Thus, the rate becomes ρ = d/q, just like in Reed–Solomon
codes.

More formally, we use the following codes.

Construction 5.23 (Folded Reed–Solomon Codes). For a prime
power q, a generator γ of F∗
q, integers m, d ∈ N, the q-ary folded Reed–
Solomon code of degree d, folding parameter m, and generator γ is
deﬁned as follows:

• The alphabet is Σ = Fm
q .
• The blocklength is ˆn = (cid:17)(q − 1)/m(cid:18).
• The message space is Fd+1

, where we view each message as
representing a polynomial f (Y ) of degree at most d over Fq.

q

• For k ∈ [ˆn], the k’th symbol of Enc(f ) is

[f (γ(k−1)m), f (γ(k−1)m+1), . . . , f (γk·m−1)].

We now show that these codes can be eﬃciently list-decoded at

distance arbitrarily close to 1 − ρ, where ρ = d/q is the rate.

Theorem 5.24. For every prime power q, integers 0 ≤ d, m ≤ q, and
generator γ of F∗
q, the q-ary folded Reed–Solomon code of degree d,
folding parameter m, and generator γ has rate at least ρ = d/q and can
be list-decoded in time qO(m) up to distance δ = 1 − d/q − O(
1/m).

(cid:7)

Note that this theorem is most interesting (and improves on the
Reed–Solomon decoding of Theorem 5.19) when m is larger than q/d,
in contrast to the setting of parameters in Theorem 5.22, where m is
logarithmic in q. We can aﬀord the larger setting of m because now the
rate ρ does not depend on m, and it is this change in parameters that
enables us to save us the factor of hm in Equation (5.4). However, the
running time, list size, and alphabet size do grow exponentially with m.

Proof. We are given a received word r : [ˆn] → Fm
q , and want to ﬁnd
all elements of LIST(r, ε) for an appropriate choice of ε = d/q +
O(

1/m).

(cid:7)



<!-- pdf-page: 152 -->
5.2 List-Decoding Algorithms

149

Step 0: Unpack to a PV received word. From r, we will
obtain a received word r(cid:3) : Fq → Fm(cid:2)
for the Parvaresh–Vardy code of
degree d, power h = q, redundancy m(cid:3) = (cid:17)
m − 1(cid:18), and irreducible
E(Y ) =Y q−1 − γ. Speciﬁcally, following Equation (5.5), each symbol
of r yields m − m(cid:3) symbols of r(cid:3). If r agrees with the FRS encoding of
f in more than εˆn positions, then r(cid:3) will agree with the PV encoding
of f in more than εˆn · (m − m(cid:3)) positions. We have

√

q

εˆn · (m − m(cid:3)) ≥ ε · ((q − 1)/m − 1) · (m − m(cid:3)) = (ε − O(1/
√

Thus our task is now to ﬁnd LIST(r(cid:3), ε(cid:3)) for ε(cid:3) = ε − O(1/
m), which
we do in a similar manner to the decoding algorithm for Parvaresh–
Vardy codes.

√

m)) · q.

Step 1: Find a low-degree Q “explaining” r(cid:3). We ﬁnd a nonzero
polynomial Q(Y, Z0, . . . , Zm(cid:2)−1) satisfying Q(y, r(cid:3)(y)) = 0 for all y ∈ Fq
and such that Q has degree at most dY in its ﬁrst variable Y and total
degree at most dZ = 1 in the Zi variables. That is, Q only has mono-
mials of the form Y jZi for j ≤ dY . The number of these monomials is
(dY + 1)· m(cid:3), so we can ﬁnd such a Q in time poly(q, m(cid:3)) = poly(q, m)
provided:

(dY + 1)· m(cid:3) > q.

(5.6)

As before, we may assume that Q is not divisible by E(Y ). (Note
that using total degree 1 instead of individual degrees h − 1 in the Zis
requires an exponentially larger setting of m(cid:3) compared to the setting
of m needed for Equation (5.1). However, this will provide a signiﬁcant
savings below. In general, it is best to consider a combination of the
two constraints, requiring that the total degree in the Zis is at most
some dZ and that the individual degrees are all at most h − 1.)

Step 2: Argue that each f (Y ) ∈ LIST(r(cid:3), ε(cid:3)) is a “root” of a
related univariate polynomial Q∗. First, we argue as before that
for f ∈ LIST(r(cid:3), ε(cid:3)), we have

Q(Y, f0(Y ), . . . , fm(cid:2)−1(Y )) = 0,

(5.7)



<!-- pdf-page: 153 -->
150 List-Decodable Codes

where fi(Y ) =f hi
most d, this will be ensured provided

(Y ) modE (Y ) =f (γiY ). Since each fi has degree at

ε(cid:3)q ≥ dY + d.

(5.8)

Note the savings of the factor (h − 1) · m as compared to Inequal-
ity (5.3); this is because we chose Q to be of total degree 1 in the Zis
instead of having individual degree 1.

Now, as in the Parvaresh–Vardy decoding, we can reduce both sides

of Equation (5.7) modulo E(Y ) and deduce

0 =Q(Y, f 0(Y ), f1(Y ), . . . , fm−1(Y )) mod E(Y )

= Q(Y, f (Y ), f (Y )h, . . . , f (Y )hm−1

) modE (Y ).

Thus, if we deﬁne the univariate polynomial

Q∗(Z) =Q(Y, Z, Z h, . . . , Zhm−1

) modE (Y ),

then f (Y ) is a root of Q∗ over the ﬁeld Fq[Y ]/E(Y ).

Observe that Q∗ is nonzero because Q is not divisible by E(Y ) and
has degree at most h − 1 in each Zi. Thus, we can ﬁnd all elements of
LIST(r(cid:3), ε(cid:3)) by factoring Q∗(Z). Constructing and factoring Q∗(Z) can
be done in time poly(q, hm) =q O(m).

For this algorithm to work, we need to satisfy Conditions (5.6) and
(5.8). We can satisfy Condition (5.6) by setting dY = (cid:17)q/m(cid:3)(cid:18), in which
case Condition (5.8) is satisﬁed for

Recalling that ε(cid:3) = ε − O(1/
d/q + O(1/
m).

√

ε(cid:3) ≥ 1/m(cid:3) + d/q.
√

m) and m(cid:3) = (cid:17)

√

m − 1(cid:18), we can take ε =

Setting parameters appropriately gives:

Theorem 5.25. The following holds for all constants ε, γ > 0. For
every n ∈ N, there is an explicit code of message length n and rate
ρ = ε − γ that can be list-decoded in polynomial time from distance
1 − ε, with alphabet size q = poly(n).



<!-- pdf-page: 154 -->
5.3 List-decoding Views of Samplers and Expanders

151

The polynomials in the running time, alphabet size, and list size
depend exponentially on γ; speciﬁcally they are of the form nO(1/γ2).
Nonconstructively, it is possible to have alphabet size (1/ε)O(ε/γ) and
list size O(1/γ) (see discussion after Theorem 5.8), and one could hope
for running time that is a ﬁxed polynomial in n, with an exponent
that is independent of γ. Recent work has achieved these parameters,
albeit with a randomized construction of codes; it remains open to
have a fully explicit and deterministic construction. However, for a
ﬁxed constant-sized alphabet, e.g., q = 2, it is still not known how to
achieve list-decoding capacity.

Open Problem 5.26. For any desired constants ρ, δ > 0 such that
ρ >1 − H2(δ), construct an explicit family of of codes Encn : {0, 1}n →
{0, 1}ˆn that have rate at least ρ and are δ-list-decodable in polynomial
time.

5.3 List-decoding Views of Samplers and Expanders

In this section, we show how averaging samplers and expander graphs
can be understood as variants of list-decodable codes. The general list
decoding framework we use to describe these connections will also allow
us to capture the other pseudorandom objects we study in this survey.
We begin with the syntactic correspondence between the three

objects, so we can view each as a function Γ : [N ] × [D] → [M ]:

Construction 5.27 (Syntactic Correspondence of Expanders,
Samplers, and Codes).

(1) Given a bipartite multigraph G with N left vertices, M right
vertices, and left-degree D, we let Γ : [N ] × [D] → [M ] be its
neighbor function, i.e., Γ(x, y) is they th neighbor of x in G.
(2) Given a sampler Samp : [N ] → [M ]D, we deﬁne Γ : [N ] ×

[D] → [M ] by

Γ(x, y) = Samp(x)y.



<!-- pdf-page: 155 -->
152 List-Decodable Codes

(3) Given a code Enc : [N ] → [q]D, we set M = q · D, associate
the elements of [q] × [D] with [M ], and deﬁne Γ : [N ] ×
[D] → [M ] by

Γ(x, y) = (y, Enc(x)y).

The correspondence between expanders and samplers is identical to
the one from Problem 4.7, which shows that the vertex expansion of G
is equivalent to the hitting sampler properties of Samp.

Note that codes correspond to expanders and samplers where the
ﬁrst component of a neighbor/sample equals the edge-label/sample-
number. Conversely, any such expander/sampler can be viewed as a
code. Many constructions of expanders and samplers have or can be
easily modiﬁed to have this property. This syntactic constraint turns
out to be quite natural in the setting of samplers. It corresponds to
the case where we have D functions f1, . . . , fD : [M ] → [0, 1], we are
interested in estimating the total average (1/D)
i µ(fi), but can only
evaluate each fi on a single sample.

(cid:4)

We now consider the following generalized notion of list decoding.

Deﬁnition 5.28. For a function Γ : [N ] × [D] → [M ], a set T ⊂ [M ],
and ε ∈ [0, 1), we deﬁne

LISTΓ(T, ε) ={x : Pr
y

[Γ(x, y) ∈ T ] > ε} and

LISTΓ(T, 1) = {x : ∀ y Γ(x, y) ∈ T }.

More generally, for a function f : [M ] → [0, 1], we deﬁne

LISTΓ(f, ε) ={x : E
y

[f (Γ(x, y))] > ε}.

We can formulate the list-decoding property of Enc, the averaging
sampler property of Samp, and the vertex expansion property of Γ in



<!-- pdf-page: 156 -->
5.3 List-decoding Views of Samplers and Expanders

153

this language as follows:

Proposition 5.29. Let Enc and Γ be as in Construction 5.27. Then
Enc is (1 − 1/q − ε, K) list-decodable iﬀ for every r ∈ [M ]D, we have
|LISTΓ(Tr, 1/q + ε)| ≤K,

where Tr = {(y, ry) :y ∈ [D]}.

Proof. Observe that, for each x ∈ [N ] and r ∈ [M ]D,
[Γ(x, y) ∈ Tr] = Pr
y

[(y, Enc(x)y) ∈ Tr]

Pr
y

= Pr
y

[Enc(x)y = ry]

= agr(Enc(x), r).

Thus |LIST(Tr, 1/q + ε)| ≤K if and only if there are at most K mes-
sages x whose encodings have agreement greater than 1/q + ε with r,
which is the same as being (1 − 1/q − ε, K) list-decodable.

Proposition 5.30. Let Samp and Γ be as in Construction 5.27. Then

(1) Samp is a (δ, ε) averaging sampler iﬀ for every function f :

[M ] → [0, 1], we have

|LISTΓ(f, µ(f ) +ε)| ≤δN.

(2) Samp is a (δ, ε) boolean averaging sampler iﬀ for every set

T ⊂ [M ], we have

|LISTΓ(T, µ(T ) +ε)| ≤δN.

Proof. Observe that x ∈ LISTΓ(f, µ(f ) +ε) if and only if x is a “bad”
D
set of coin tosses for Samp — namely (1/D) ·
i=1 f (zi) > µ(f ) +ε,
where (z1, . . . , zD) = Samp(x). Thus Samp errs with probability at most
δ over x R← U[N ] if and only if |LISTΓ(f, µ(f ) +ε)| ≤δN . The boolean
averaging sampler case follows by viewing boolean functions f as char-
acteristic functions of sets T .

(cid:4)



<!-- pdf-page: 157 -->
154 List-Decodable Codes

Noting that the sets Tr in Proposition 5.29 have density µ(Tr) = 1/q,
we see that the averaging-sampler property implies the standard list-
decoding property:

Corollary 5.31.
If Samp is a (δ, ε) boolean averaging sampler of
the form Samp(x)y = (y, Enc(x)y), then Enc is (1 − 1/q − ε, δN ) list-
decodable.

Note, however, that the typical settings of parameters of samplers
and list-decodable codes are very diﬀerent. With codes, we want the
alphabet size q to be as small as possible (e.g., q = 2) and the block-
length D to be linear or polynomial in the message length n = log N ,
so M = qD is also linear or polynomial in n = log N . In contrast, we
usually are interested in samplers for functions on exponentially large
domains (e.g., M = 2Ω(n)).

In Section 6, we will see a converse to Corollary 5.31 when the
alphabet size is small: if Enc is (1 − 1/q − ε, δN ), list-decodable, then
Samp is an (δ/ε, q · ε) averaging sampler.

For expanders, it will be convenient to state the list-decoding prop-
erty in terms of the following variant of vertex expansion, where we
only require that sets of size exactly K expand:

Deﬁnition 5.32. For K ∈ N, a bipartite multigraph G is an (= K, A)
vertex expander if all sets S consisting of K left-vertices, the neighbor-
hood N (S) is of size at least A · K.

Thus, G is a (K, A) vertex expander in the sense of Deﬁnition 4.3
iﬀ G is an (= K(cid:3), A) vertex expander for all positive integers K(cid:3) ≤ K.

Proposition 5.33. For K ∈ N, Γ : [N ] × [D] → [M ] is an (= K, A)
vertex expander iﬀ for every set T ⊂ [D] × [M ] such that |T | < KA,
we have:

|LISTΓ(T, 1)| < K.



<!-- pdf-page: 158 -->
5.4 Expanders from Parvaresh–Vardy Codes

155

Proof.

Γ not an (= K, A) expander

⇔ ∃S ⊂ [N ] s.t. |S| = K and |N (S)| < KA

⇔ ∃S ⊂ [N ] s.t. |S| ≥K and |N (S)| < KA

⇔ ∃T ⊂ [M ] s.t. |LIST(T, 1)| ≥K and |T | < KA,

where the last equivalence follows because if T = N (S), then S ⊂
LIST(T, 1), and conversely if S = LIST(T, 1) then N (S) ⊂ T .

On one hand, this list-decoding property seems easier to establish
than the ones for codes and samplers because we look at LIST(T, 1)
instead of LIST(T, µ(T ) +ε). On the other hand, to get expansion
(i.e., A >1), we require a very tight relationship between |T | and
|LIST(T, 1)|. In the setting of codes or samplers, we would not care
much about a factor of 2 loss in |LIST(T )|, as this just corresponds to
a factor of 2 in list size or error probability. But here it corresponds
to a factor of 2 loss in expansion, which can be quite signiﬁcant. In
particular, we cannot aﬀord it if we are trying to get A = (1 − ε) · D,
as we will be in the next section.

5.4 Expanders from Parvaresh–Vardy Codes

Despite the substantial diﬀerences in the standard settings of param-
eters between codes, samplers, and expanders, it can be very useful
to translates ideas and techniques from one object to the other using
the connections described in the previous section. In particular, in this
section we will see how to build graphs with extremely good vertex
expansion (A = (1 − ε)D) from Parvaresh–Vardy codes.

Consider the bipartite multigraph obtained from the Parvaresh–
Vardy codes (Construction 5.21) via the correspondence of Construc-
tion 5.27. That is, we deﬁne a neighbor function Γ : Fn
× Fq → Fq ×
q
Fm

q by

Γ(f, y) = [y, f0(y), f1(y), . . . , fm−1(y)],
where f (Y ) is a polynomial of degree at most n − 1 over Fq, and
we deﬁne fi(Y ) =f (Y )hi
mod E(Y ), where E is a ﬁxed irreducible

(5.9)



<!-- pdf-page: 159 -->
156 List-Decodable Codes

polynomial of degree n over Fq. (Note that we are using n − 1 instead
of d to denote degree of f .)

× Fq → Fm+1
Theorem 5.34. Let Γ : Fn
be the neighbor function
q
of the bipartite multigraph corresponding to the q-ary Parvaresh–
Vardy code of degree d = n − 1, power h, and redundancy m via Con-
struction 5.27. Then Γ is a (Kmax, A) expander for Kmax = hm and
A = q − nhm.

q

q

Proof. Let K be any integer less than or equal to Kmax = hm, and let
A = q − nmh. By Proposition 5.33, it suﬃces to show that for every
set T ⊂ Fm+1

of size at most AK − 1, we have |LIST(T )| ≤K − 1.

We begin by doing the proof for K = Kmax = hm, and later describe
the modiﬁcations to handle smaller values of K. The proof goes along
the same lines as the list-decoding algorithm for the Parvaresh–Vardy
codes from Section 5.2.3.

Step 1: Find a low-degree Q vanishing on T . We ﬁnd a nonzero
polynomial Q(Y, Z0, . . . , Zm−1) of degree at most dY = A − 1 in its
ﬁrst variable Y and at most h − 1 in each of the remaining variables
such that Q(z) = 0 for all z ∈ T . (Compare this to Q(y, r(y)) = 0 for
all y ∈ Fq in the list-decoding algorithm, which corresponds to taking
T = Tr.)

This is possible because

A · hm = AK > |T |.

Moreover, we may assume that Q is not divisible by E(Y ). If it is,
we can divide out all the factors of E(Y ), which will not aﬀect the
conditions Q(z) = 0 since E has no roots (being irreducible).

Step 2: Argue that each f (Y ) ∈ LIST(T, 1) is a “root” of a
related univariate polynomial Q∗. First, we argue as in the list-
decoding algorithm that if f ∈ LIST(T, 1), we have

Q(Y, f0(Y ), . . . , fm−1(Y )) = 0.

This is ensured because

q > A − 1 +nmh.



<!-- pdf-page: 160 -->
5.4 Expanders from Parvaresh–Vardy Codes

157

(In the list-decoding algorithm, the left-hand side of this inequality was
εq, since we were bounding |LIST(Tr, ε)|.)

Once we have this, we can reduce both sides modulo E(Y ) and

deduce

0 =Q(Y, f 0(Y ), f1(Y ), . . . , fm−1(Y )) mod E(Y )

= Q(Y, f (Y ), f (Y )h2

, . . . , f (Y )hm−1

) modE (Y )

Thus, if we deﬁne the univariate polynomial

Q∗(Z) =Q(Y, Z, Z h, . . . , Zhm−1

) modE (Y ),

then f (Y ) is a root of Q∗ over the ﬁeld Fq[Y ]/E(Y ).

Observe that Q∗ is nonzero because Q is not divisible by E(Y ) and

has degree at most h − 1 in each Zi. Thus,

|LIST(T, 1)| ≤deg(Q ∗) ≤ h − 1 + (h − 1) · h + (h − 1) · h2
+ · · · + (h − 1) · hm−1 = K − 1.

(Compare this to the list-decoding algorithm, where our primary goal
was to eﬃciently enumerate the elements of LIST(T, ε), as opposed to
bound its size.)

Handling smaller values of K. We further restrict Q(Y, Z1, . . .,
Zm) to only have nonzero coeﬃcients on monomials of the form Y iMonj
(Z1, . . . , Zm) for 0 ≤ i ≤ A − 1 and 0 ≤ j ≤ K − 1 ≤ hm − 1, where
and j = j0 + j1h + · · · + jm−1hm−1
Monj(Z1, . . . , Zm) =Z j0
1
is the base-h representation of j. Note that this gives us AK > |T |
monomials, so Step 1 is possible. Moreover Mj(Z, Zh, Zh2
) =
Zj, so the degree of Q∗ is at most K − 1, and we get the desired list-size
bound in Step 3.

, . . . , Zhm−1

· · · Zjm−1
m

Setting parameters, we have:

Theorem 5.35. For every constant α > 0, every N ∈ N, K ≤ N , and
ε >0, there is an explicit ( K, (1 − ε)D) expander with N left-vertices,
M right-vertices, left-degree D = O((log N )(log K)/ε)1+1/α and M ≤
D2 · K1+α. Moreover, D is a power of 2.



<!-- pdf-page: 161 -->
158 List-Decodable Codes

Proof. Let n = log N and k = log Kmax. Let h = (cid:15)(2nk/ε)1/α(cid:16) and let q
be the power of 2 in the interval (h1+α/2, h1+α].

Set m = (cid:15)(log Kmax)/(log h)(cid:16), so that hm−1 ≤ Kmax ≤ hm. Then,
by Theorem 5.34, the graph Γ : Fn
deﬁned in (5.9) is
q
an (hm, A) expander for A = q − nhm. Since Kmax ≤ hm, it is also a
(Kmax, A) expander.

× Fq → Fm+1

q

Note that the number of left-vertices in Γ is qn ≥ N , and the number

of right-vertices is

M = qm+1 ≤ q2 · h(1+α)·(m−1) ≤ q2 · K1+α
max .

The degree is

D = q ≤ h1+α = O(nk/ε)1+1/α = O((log N )(log Kmax)/ε)1+1/α.

To see that the expansion factor A = q − nhm ≥ q − nhk is at least

(1 − ε)D = (1 − ε)q, note that

nhk ≤ (ε/2) · h1+α ≤ εq,

where the ﬁrst inequality holds because hα ≥ 2nk/ε.

Finally, the construction is explicit because a description of Fq for q
a power of 2 (i.e., an irreducible polynomial of degree log q over F2)
as well as an irreducible polynomial E(Y ) of degree n over Fq can be
found in time poly(n, log q) = poly(log N, log D).

These expanders are of polylogarithmic rather than constant degree.
But the expansion is almost as large as possible given the degree
(A = (1 − ε) · D), and the size of the right-hand side is almost as
small as possible (in a (K, A) expander, we must have M ≥ KA =
(1 − ε)KD). In particular, these expanders can be used in the data
structure application of Problem 4.10 — storing a K-sized subset of [N ]
using K1.01 · polylog(N ) bits in such a way that membership can be
probabilistically tested by reading 1 bit of the data structure. (An eﬃ-
cient solution to that application actually requires more than the graph
being explicit in the usual sense, but also that there are eﬃcient algo-
rithms for ﬁnding all left-vertices having at least some δ fraction neigh-
bors in a given set T ⊂ [M ] of right vertices, but the expanders above



<!-- pdf-page: 162 -->
5.5 Exercises

159

can be shown to have that property by a variant of the list-decoding
algorithm above.)

A deﬁciency of the expander of Theorem 5.35 is that the size of the
right-hand side is polynomial in K and D (for constant α), whereas the
optimal bound is M = O(KD/ε). Achieving the latter, while keeping
the left-degree polylogarithmic, is an open problem:

Open Problem 5.36. Construct (= K, A) bipartite expanders with N
left-vertices, degree D = poly(log N ), expansion A = 0.99D, and M =
O(KD) right-hand vertices.

We remark that a construction where D is quasipolynomial in log N

is known.

5.5 Exercises

Problem 5.1 (Limits of List Decoding). Show that if there exists
a q-ary code C ⊂ Σˆn of rate ρ that is (δ, L) list-decodable, then
ρ ≤ 1 − Hq(δ, ˆn) + (logq L)/ˆn.

Problem 5.2 (Concatenated Codes). For codes Enc1 : {1, . . . ,
N } →Σ n1
2 , their concatenation Enc : {1, . . . ,
1
N } →Σ n1n2

and Enc2 : Σ1 → Σn2
is deﬁned by

2

Enc(m) = Enc2(Enc1(m)1)Enc2(Enc1(m)2) · · · Enc2(Enc1(m)n1).

This is typically used as a tool for reducing alphabet size, e.g., with
Σ2 = {0, 1}.

(1) Prove that if Enc1 has minimum distance δ1 and Enc2 has
minimum distance δ2, then Enc has minimum distance at
least δ1δ2.

(2) Prove that if Enc1 is (1 − ε1, (cid:6)1) list-decodable and Enc2 is
(δ2, (cid:6)2) list-decodable, then Enc is ((1 − ε1(cid:6)2) · δ2, (cid:6)1(cid:6)2) list-
decodable.



<!-- pdf-page: 163 -->
160 List-Decodable Codes

(3) By concatenating a Reed–Solomon code and a Hadamard
code, show that for every n ∈ N and ε >0, there is a (fully)
explicit code Enc : {0, 1}n → {0, 1}ˆn with blocklength ˆn =
O(n2/ε2) with minimum distance at least 1/2 − ε. Further-
more, show that with blocklength ˆn = poly(n, 1/ε), we can
obtain a code that is (1/2 − ε, poly(1/ε)) list-decodable in
polynomial time. (Hint: the inner code can be decoded by
brute force.)

Problem 5.3(List Decoding implies Unique Decoding for Ran-
dom Errors).

(1) Suppose that C ⊂ {0, 1}ˆn is a code with minimum distance
at least 1/4 and rate at most αε2 for a constant α > 0, and
we transmit a codeword c ∈ C over a channel in which each
bit is ﬂipped with probability 1/2 − 2ε. Show that if α is a
suﬃciently small constant (independent of ˆn and ε), then all
but exponentially small probability over the errors, c will be
the unique codeword at distance at most 1/2 − ε from the
received word r.

(2) Using Problem 5.2, deduce that for every ε >0 and n ∈ N,
there is an explicit code of blocklength ˆn = poly(n, 1/ε) that
can be uniquely decoded from (1/2 − 2ε) random errors as
above in polynomial time.

Problem 5.4 (Linear Codes). For a prime power q, aq -ary code
C ⊂ Fˆn
q is called linear if C is a linear subspace of Fˆn
q . That is, for every
u, v ∈ C and α ∈ Fq, we haveu + v ∈ C and αu ∈ C.

(1) Verify that the Hadamard, Reed–Solomon, and Reed–Muller

codes are all linear.

(2) Show that if C is linear, then the minimum distance of C
equals the minimum weight of C, which is deﬁned to be
minc∈C\{0} |{i : ci (cid:1)= 0}|/ˆn.



<!-- pdf-page: 164 -->
5.5 Exercises

161

(3) Show that if C is a subspace of dimension n, then its rate is
n/ˆn and it has an encoding function Enc : Fn
q that is a
q
linear map. Moreover, the encoding function can be made to
have the property that there is a set S ⊂ [ˆn] of n coordinates
such that Enc(m)|S = m for every m ∈ Fˆn
q . (Here c|S is the
projection of c onto the coordinates in S.) Such encodings are
called systematic, and will be useful when we study locally
decodable codes in Section 7.

→ Fˆn

(4) Find explicit systematic encodings for the Hadamard and

Reed–Solomon codes.

(5) Show that the nonconstructive bound of Theorem 5.8, Part 1,
can be achieved by a linear code. That is, for all prime powers
q, integers n, ˆn ∈ N, and δ ∈ (0, 1 − 1/q), there exists a linear
q-ary code of block length ˆn, minimum distance at least δ,
and rate at least ρ = n/ˆn provided ρ ≤ 1 − Hq(δ, ˆn). (Hint:
chose a random linear map Enc : Fn
q and use Part 2.)
q

→ Fˆn

Problem 5.5 (LDPC Codes). Given a bipartite multigraph G with
N left-vertices and M right-vertices, we can obtain a linear code C ⊂
{0, 1}N (where we view {0, 1} as the ﬁeld of two elements) by:

C = {c ∈ {0, 1}N : ∀ j ∈ [M ] ⊕i∈Γ(j) ci = 0},

where Γ(j) denotes the set of neighbors of vertex j. When G has small
left-degree D (e.g., D = O(1)), then C is called a low-density parity
check (LDPC) code.

(1) Show that C has rate at least 1 − M/N .
(2) Show that if G is a (K, A) expander for A > D/2, then C has

minimum distance at least δ = K/N .

(3) Show that if G is a (K, (1 − ε)D) expander for a suﬃciently
small constant ε, then C has a polynomial-time δ-decoder
for δ = (1 − 3ε) · K/N . Assume that G is given as input to
the decoder. (Hint: given a received word r ∈ {0, 1}n, ﬂip all
coordinates of r for which at least 2/3 of the neighboring



<!-- pdf-page: 165 -->
162 List-Decodable Codes

parity checks are not satisﬁed, and argue that the number of
errors decreases by a constant factor. It may be useful to use
the results of Problem 4.10.)

By a probabilistic argument like Theorem 4.4, graphs G as above exist
with D = O(1), K = Ω(N ), M = (1 − Ω(1))N , arbitrarily small con-
stant ε >0, and N → ∞, and in fact explicit constructions are known.
This yields explicit LDPC codes with constant rate and constant dis-
tance (“asymptotically good LDPC codes”).

Problem 5.6 (Improved list decoding of Reed–Solomon
Codes).

(cid:7)

(cid:7)

(1) Show that there is a polynomial-time algorithm for list
decoding the Reed–Solomon codes of degree d over Fq up to
distance 1 −
2d/q, improving the 1 − 2
d/q bound from
Theorem 5.19. (Hint: do not use ﬁxed upper bounds on the
individual degrees of the interpolating polynomial Q(Y, Z),
but rather allow as many monomials as possible.)
(2) (*) Improve the list-decoding radius further to 1 −

d/q by
using the following “method of multiplicities.” First, require
the interpolating polynomial Q(Y, Z) to have a zero of mul-
tiplicity s at each point (y, r(y)) — that is, the polyno-
mial Q(Y + y, Z + r(y)) should have no monomials of degree
smaller than s. Second, use the fact that a univariate poly-
nomial R(Y ) of degree t can have at most t roots, counting
multiplicities.

(cid:7)

Problem 5.7 (Twenty Questions). In the game of 20 questions, an
oracle has an arbitrary secret s ∈ {0, 1}n and the aim is to determine the
secret by asking the oracle as few yes/no questions about s as possible.
It is easy to see that n questions are necessary and suﬃcient. Here we
consider a variant where the oracle has two secrets s1, s2 ∈ {0, 1}n, and
can adversarially decide to answer each question according to either



<!-- pdf-page: 166 -->
5.6 Chapter Notes and References

163

s1 or s2. That is, for a question f : {0, 1}n → {0, 1}, the oracle may
answer with either f (s1) orf (s2). Here it turns out to be impossible
to pin down either of the secrets with certainty, no matter how many
questions we ask, but we can hope to compute a small list L of secrets
such that |L ∩ {s1, s2}| (cid:1)= 0. (In fact, |L| can be made as small as 2.)
This variant of twenty questions apparently was motivated by problems
in Internet traﬃc routing.

(1) Let Enc : {0, 1}n → {0, 1}ˆn be a code such that every two
codewords in Enc agree in at least a 1/2 − ε fraction of posi-
tions and that Enc has a polynomial-time (1/4 +ε, (cid:6)) list-
decoding algorithm. Show how to solve the above problem in
polynomial time by asking the ˆn questions {fi} deﬁned by
fi(x) = Enc(x)i.

(2) Taking Enc to be the code constructed in Problem 1, deduce

that ˆn = poly(n) questions suﬃces.

5.6 Chapter Notes and References

Standard texts on coding theory include MacWilliams–Sloane [282]
and the Handbook of Coding Theory [313]. The lecture notes of
Sudan [379] present coding theory with an algorithmic perspective,
and Guruswami [184] gives a thorough treatment of list decoding.

The ﬁeld of coding theory began with Shannon’s seminal 1948
paper [361], which proposed the study of stochastic error models and
proved that a random error-correcting code achieves an optimal rate-
distance tradeoﬀ with high probability. The study of decoding from
worst-case errors began a couple of years later with the work of
Hamming [199]. The notion of list decoding was proposed indepen-
dently in the late 1950s, in the work of Elias [129] and Wozencraft [420].
The nonconstructive bound for the tradeoﬀ between rate and min-
imum distance of Theorem 5.8 (Part 1) is due to Gilbert [151],
and its extension to linear codes in Problem 5.4 (Part 5) is due to
Varshamov [406]; together they are known as the Gilbert–Varshamov
Bound. For more on the algebraic geometric codes and how they
can be used to beat the Gilbert–Varshamov Bound, see the text by



<!-- pdf-page: 167 -->
164 List-Decodable Codes

Stichtenoth [375]. The nonconstructive bound for list decoding of The-
orem 5.8 (Part 2) is due to Elias [131], and it has been extended to
linear codes in [186, 187, 428]. The Johnson Bound (Proposition 5.10)
was proven for binary codes by Johnson [224, 225]. An optimized form
of the bound can be found in [191].

The binary (q = 2) case of Reed–Muller codes was introduced inde-
pendently by Reed [324] and Muller [293] in the mid-50s. Reed–Solomon
codes were introduced in 1960 by Reed and Solomon [325]. Polyno-
mial time unique-decoding algorithms for Reed–Solomon Codes include
those of Peterson [308] and Berlekamp [65]. The ﬁrst nontrivial list
decoding algorithm was given by Goldreich and Levin [168]; while
their algorithm is stated in the language of “hardcore bits for one-
way functions,” it can be viewed as an eﬃcient “local” list-decoding
algorithm for the Hadamard Code. (Local decoding algorithms are dis-
cussed in Section 7.) The list-decoding algorithm for Reed–Solomon
Codes of Theorem 5.19 is from the seminal work of Sudan [378], which
sparked a resurgence in the study of list decoding. The improved
decoding algorithm of Problem 5.6, Part 2 is due to Guruswami and
Sudan [189]. Parvaresh–Vardy codes and their decoding algorithm are
from [306]. Folded Reed–Solomon Codes and their capacity-achieving
list-decoding algorithm are due to Guruswami and Rudra [188]. (In all
cases, our presentation uses a simpliﬁed setting of parameters compared
to the original algorithms.) The list size, decoding time, and alphabet
size of Folded Reed–Solomon Codes have recently been improved in
[125, 185, 194], with the best parameters to date being achieved in the
randomized construction of [194], while [125] give a fully deterministic
construction.

The list-decoding views of expanders and samplers emerged out
of work on randomness extractors (the subject of Section 6). Speciﬁ-
cally, a close connection between extractors and expanders was under-
stood already at the time that extractors were introduced by Nisan
and Zuckerman [303]. An equivalence between extractors and averag-
ing samplers was established by Zuckerman [427] (building on previous
connections between other types of samplers and expanders [107, 365]).
A connection between list-decodable codes and extractors emerged in
the work of Trevisan [389], and the list-decoding view of extractors



<!-- pdf-page: 168 -->
5.6 Chapter Notes and References

165

was crystallized by Ta-Shma and Zuckerman [383]. The list-decoding
formulation of vertex expansion and the construction of expanders
from Parvaresh–Vardy codes is due to Guruswami, Umans, and Vad-
han [192].

Code concatenation (Problem 5.2) was introduced by Forney [140],
who used it to construct explicit, eﬃciently decodable binary codes
that achieve capacity for random errors. Eﬃcient list-decoding algo-
rithms for the concatenation of a Reed–Solomon code with a Hadamard
code were given in [190]. Low-density parity check (LDPC) codes
(Problem 5.5) were introduced by Gallager [148]. The use of expan-
sion to analyze such codes and their decoding algorithm comes from
Sipser and Spielman [367]. Explicit expanders suitable for Problem 5.5
were given by [92]. The surveys of Guruswami [183, 184] describe the
state of the art in expander-based constructions of codes and in LDPC
codes, respectively.

The question of Problem 5.7 (Twenty Questions) was posed in [102],
motivated by Internet traﬃc routing applications. The solution using
list decoding is from [20].



<!-- pdf-page: 169 -->
6

Randomness Extractors

Randomness extractors are functions that extract almost-uniform bits
from sources of biased and correlated bits. The original motivation for
extractors was to simulate randomized algorithms with weak random
sources as might arise in nature. This motivation is still compelling,
but extractors have taken on a much wider signiﬁcance in the years
since they were introduced. They have found numerous applications
in theoretical computer science beyond this initial motivating one,
in areas from cryptography to distributed algorithms to hardness of
approximation. More importantly from the perspective of this survey,
they have played a major unifying role in the theory of pseudoran-
domness. Indeed, the links between the various pseudorandom objects
we are studying in this survey (expander graphs, randomness extrac-
tors, list-decodable codes, pseudorandom generators, samplers) were
all discovered through work on extractors (even though now we ﬁnd it
more natural to present these links in the language of list decoding, as
introduced in Section 5.3).

166



<!-- pdf-page: 170 -->
6.1 Motivation and Deﬁnition

167

6.1 Motivation and Deﬁnition

6.1.1 Deterministic Extractors

Typically, when we design randomized algorithms or protocols, we
assume that all algorithms/parties have access to sources of perfect
randomness, i.e., bits that are unbiased and completely independent.
However, when we implement these algorithms, the physical sources of
randomness to which we have access may contain biases and correla-
tions. For example, we may use low-order bits of the system clock, the
user’s mouse movements, or a noisy diode based on quantum eﬀects.
While these sources may have some randomness in them, the assump-
tion that the source is perfect is a strong one, and thus it is of interest
to try and relax it.

Ideally, what we would like is a compiler that takes any algorithm
A that works correctly when fed perfectly random bits Um, and pro-
duces a new algorithm A(cid:3) that will work even if it is fed random bits
X ∈ {0, 1}n that come from a “weak” random source. For example, if
A is a BPP algorithm, then we would like A(cid:3) to also run in probabilis-
tic polynomial time. One way to design such compilers is to design a
randomness extractor Ext : {0, 1}n → {0, 1}m such that Ext(X) is dis-
tributed uniformly in {0, 1}m.

IID-Bit Sources. A simple version of this question was already
considered by von Neumann. He looked at sources that consist of
boolean random variables X1, X2, . . . , Xn ∈ {0, 1} that are independent
but biased. That is, for every i, Pr [Xi = 1] = δ for some unknown δ.
How can such a source be converted into a source of independent, unbi-
ased bits? Von Neumann proposed the following extractor: Break all
the variables in pairs and for each pair output 0 if the outcome was
01, 1 if the outcome was 10, and skip the pair if the outcome was 00
or 11. This will yield an unbiased random bit after 1/(2δ(1 − δ)) pairs
on average.

Independent-Bit Sources. Lets now look at a bit more interesting
class of sources in which all the variables are still independent but the
bias is no longer the same. Speciﬁcally, for every i, Pr [Xi = 1] = δi and



<!-- pdf-page: 171 -->
168 Randomness Extractors

0 < δ ≤ δi ≤ 1 − δ for some constant δ > 0. How can we deal with such
a source?

It can be shown that when we take a parity of (cid:6) bits from such
an independent-bit source, the result approaches an unbiased coin
(cid:16)
− 1/2| = 2−Ω((cid:4)). The
ﬂip exponentially fast in (cid:6), i.e., | Pr
result is not a perfect coin ﬂip but is as good as one for almost all
purposes.

i=1Xi = 1

⊕(cid:4)

(cid:17)

Let’s be more precise about the problems we are studying. A source
on {0, 1}n is simply a random variable X taking values in {0, 1}n. In
each of the above examples, there is an implicit class of sources being
studied. For example, IndBitsn,δ is the class of sources X on {0, 1}n
where the bits Xi are independent and satisfy δ ≤ Pr[Xi = 1]≤ 1 − δ.
We could deﬁne IIDBitsn,δ to be the same with the further restric-
tion that all of the Xis are identically distributed, i.e., Pr[Xi = 1] =
Pr[Xj = 1] for all i, j, thereby capturing von Neumann sources.

Deﬁnition 6.1 (deterministic extractors). 1 Let C be a class of
sources on {0, 1}n. An ε-extractor for C is a function Ext : {0, 1}n →
{0, 1}m such that for every X ∈ C, Ext(X) is “ε-close” to Um.

Note that we want a single function Ext that works for all sources
in the class. This captures the idea that we do not want to assume
we know the exact distribution of the physical source we are using,
but only that it comes from some class. For example, for IndBitsn,δ,
we know that the bits are independent and none are too biased, but
not the speciﬁc bias of each bit. Note also that we only allow the
extractor one sample from the source X. If we want to allow mul-
tiple independent samples, then this should be modelled explicitly in
our class of sources; ideally we would like to minimize the independence
assumptions used.

We still need to deﬁne what we mean for the output to be ε-close

to Um.

1 Such extractors are called deterministic or seedless to contrast with the probabilistic or
seeded randomness extractors we will see later.



<!-- pdf-page: 172 -->
6.1 Motivation and Deﬁnition

169

Deﬁnition 6.2.For random variables X and Y taking values in U, their
statistical diﬀerence (also known as variation distance) is ∆(X, Y ) =
maxT ⊂U | Pr[X ∈ T ] − Pr[Y ∈ T ]|. We say that X and Y are ε-close if
∆(X, Y ) ≤ ε.

Intuitively, any event in X happens in Y with the same proba-
bility ±ε. This is perhaps the most natural measure of distance for
probability distributions (much more so than the (cid:6)2 distance we used
in the study of random walks). In particular, it satisﬁes the following
natural properties.

Lemma 6.3(properties of statistical diﬀerence). Let X, Y, Z, X1,
X2, Y1, Y2 be random variables taking values in a universe U. Then,
(1) ∆(X, Y ) ≥ 0, with equality iﬀ X and Y are identically dis-

tributed,

(2) ∆(X, Y ) ≤ 1, with equality iﬀ X and Y have disjoint sup-

ports,

(3) ∆(X, Y ) = ∆(Y, X),
(4) ∆(X, Z) ≤ ∆(X, Y ) + ∆(Y, Z),
(5) for every function f , we have ∆(f (X), f (Y )) ≤ ∆(X, Y ),
(6) ∆((X1, X2), (Y1, Y2)) ≤ ∆(X1, Y1) + ∆(X2, Y2) if X1 and X2,

as well as Y1 and Y2, are independent, and

(7) ∆(X, Y ) = 1
2

· |X − Y |1, where | · |1 is the (cid:6)1 distance. (Thus,
X is ε-close to Y iﬀ we can transform X into Y by “shifting”
at most an ε fraction of probability mass.)

We now observe that extractors according to this deﬁnition give us

the “compilers” we want.

Proposition 6.4. Let A(w; r) be a randomized algorithm such that
A(w; Um) has error probability at most γ, and let Ext : {0, 1}n →
{0, 1}m be an ε-extractor for a class C of sources on {0, 1}n. Deﬁne
A(cid:3)(w; x) =A(w ; Ext(x)). Then for every source X ∈ C, A(cid:3)(w; X) has
error probability at most γ + ε.



<!-- pdf-page: 173 -->
170 Randomness Extractors

This application identiﬁes some additional properties we’d like from
our extractors. We’d like the extractor itself to be eﬃciently computable
(e.g., polynomial time). In particular, to get m almost-uniform bits
out, we should need at most n = poly(m) bits from the weak random
source.

We can cast our earlier extractor for sources of independent bits in

this language:

Proposition 6.5. For every constant δ > 0, every n, m ∈ N, there is
a polynomial-time computable function Ext : {0, 1}n → {0, 1}m that is
an ε-extractor for IndBitsn,δ, with ε = m · 2−Ω(n/m).

In particular, taking n = m2, we get exponentially small error with

a source of polynomial length.

Proof. Ext breaks the source into m blocks of length (cid:17)n/m(cid:18) and out-
puts the parity of each block.

Unpredictable-Bit Sources (aka Santha–Vazirani Sources).
Another interesting class of sources, which looks similar to the pre-
vious example is the class UnpredBitsn,δ of unpredictable-bit sources.
These are the sources that for every i, every x1, . . . , xn ∈ {0, 1} and some
constant δ > 0, satisfy

δ ≤ Pr [Xi = 1 | X1 = x1, X2 = x2, . . . , Xi−1 = xi−1] ≤ 1 − δ

The parity extractor used above will be of no help with this source since
the next bit could be chosen in a way that the parity will be equal to 1
with probability δ. Indeed, there does not exist any nontrivial extractor
for these sources — the best we can do is output the ﬁrst bit:

Proposition 6.6. For every n ∈ N, δ > 0, and ﬁxed extraction func-
tion Ext : {0, 1}n → {0, 1} there exists a source X ∈ UnpredBitsn,δ such
that either Pr [Ext(X) = 1] ≤ δ or Pr [Ext(X) = 1] ≥ 1 − δ. That is,
there is no ε-extractor for UnpredBitsn,δ for ε <1/2 − δ.



<!-- pdf-page: 174 -->
6.1 Motivation and Deﬁnition

171

The proof is left as an exercise (Problem 6.6).
Nevertheless, as we will see, the answer to the question whether we
can simulate BPP algorithms with unpredictable sources will be “yes”!
Indeed, we will even be able to handle a much more general class of
sources, introduced in the next section.

6.1.2 Entropy Measures and General Weak Sources

Intuitively, to extract m almost-uniform bits from a source, the source
must have at least “m bits of randomness” in it. (In particular, its
support cannot be much smaller than 2m.) Ideally, this is all we would
like to assume about a source. Thus, we need some measure of how much
randomness is in a random variable; this can be done using various
notions of entropy described below.

Deﬁnition 6.7 (entropy measures). Let X be a random variable.
Then

• the Shannon entropy of X is:
!

HSh (X) = E

R←X

x
• the R´enyi entropy of X is:

(cid:20)

H2(X) = log

R←X
• the min-entropy of X is:

E
x

log

1
Pr [X = x]

"

.

1

[Pr [X = x]]

(cid:21)

= log

1
CP(X)

, and

H∞(X) = min

x

where all logs are base 2.

(cid:6)

log

1
Pr [X = x]

,

R´enyi entropy H2(X) should not be confused with the binary
entropy function H2(δ) from Deﬁnition 5.6. Indeed, the q-ary entropy
Hq(δ) is equal to the Shannon entropy of a random variable that equals
1 with probability 1 − δ and is uniformly distributed in {2, . . . , q} with
probability δ.

 


<!-- pdf-page: 175 -->
172 Randomness Extractors

All the three measures satisfy the following properties we would

expect from a measure of randomness:

Lemma 6.8 (properties of entropy). For each of the entropy mea-
sures H ∈ {HSh , H2, H∞} and random variables X, Y , we have:

• H(X) ≥ 0, with equality iﬀ X is supported on a single

element,

• H(X) ≤ log |Supp(X)|, with equality iﬀ X is uniform on

Supp(X),

• if X, Y are independent, then H((X, Y )) = H(X) + H(Y ),
• for every deterministic function f , we have H(f (X)) ≤ H(X),

and

• for every X, we have H∞(X) ≤ H2(X) ≤ HSh (X).

To illustrate the diﬀerences between the three notions, consider a
source X such that X = 0n with probability 0.99 and X = Un with
probability 0.01. Then HSh (X) ≥ 0.01n (contribution from the uniform
distribution), H2(X) ≤ log(1/0.992) < 1 and H∞(X) ≤ log(1/0.99) < 1
(contribution from 0n). Note that even though X has Shannon entropy
linear in n, we cannot expect to extract bits that are close to uniform or
carry out any useful randomized computations with one sample from X,
because it gives us nothing useful 99% of the time. Thus, we should use
the stronger measures of entropy given by H2 or H∞.

Then why is Shannon entropy so widely used in information theory
results? The reason is that such results typically study what happens
when you have many independent samples from the source (whereas we
only allow one sample). In the case of many samples, it turns out that
the source is “close” to one where the min-entropy is roughly equal
to the Shannon entropy. Thus the distinction between these entropy
measures becomes less signiﬁcant. Moreover, Shannon entropy satisﬁes
many nice identities that make it quite easy to work with. Min-entropy
and R´enyi entropy are much more delicate.



<!-- pdf-page: 176 -->
6.1 Motivation and Deﬁnition

173

We will consider the task of extracting randomness from sources

where all we know is a lower bound on the min-entropy:

Deﬁnition 6.9. A random variable X is a k-source if H∞(X) ≥ k, i.e.,
if Pr [X = x] ≤ 2−k.

A typical setting of parameters is k = δn for some ﬁxed δ, e.g.,
0.01. We call δ the min-entropy rate. Some diﬀerent ranges that are
commonly studied (and are useful for diﬀerent applications): k =
polylog(n), k = nγ for a constant γ ∈ (0, 1), k = δn for a constant
δ ∈ (0, 1), and k = n − O(1). The middle two (k = nγ and k = δn) are
the most natural for simulating randomized algorithms with weak ran-
dom sources.

Examples of k-sources:

• k random and independent bits, together with n − k ﬁxed
bits (in an arbitrary order). These are called oblivious bit-
ﬁxing sources.

• k random and independent bits, and n − k bits that depend
arbitrarily on the ﬁrst k bits. These are called adaptive bit-
ﬁxing sources.

• Unpredictable-bit sources with bias parameter δ. These are

k-sources with k = log(1/(1 − δ)n) = Θ(δn).

• Uniform distribution on a set S ⊂ {0, 1}n with |S| = 2k.

These are called ﬂat k-sources.

It turns out that ﬂat k-sources are really representative of general

k-sources.

Lemma 6.10. Every k-source is a convex combination of ﬂat k-sources
(cid:4)
(provided that 2k ∈ N), i.e., X =
pi = 1 and
all the Xi are ﬂat k-sources.

piXi with 0 ≤ pi ≤ 1,

(cid:4)

That is, we can think of any k-source as being obtained by ﬁrst selecting
a ﬂat k-source Xi according to some distribution (given by the pis) and



<!-- pdf-page: 177 -->
174 Randomness Extractors

then selecting a random sample from Xi. This means that if we can
compile probabilistic algorithms to work with ﬂat k-sources, then we
can compile them to work with any k-source.

Proof. Let X be a k-source on [N ]. We can view X as partitioning a
circle of unit circumference into N (half-open) intervals, where the tth
interval has length exactly Pr[X = t]. (If we associate the points on the
circle with [0, 1), then the tth interval is [Pr[X < t], Pr[X ≤ t]).) Now
consider a set S of K points spaced evenly on the circle. Then since
each interval is half-open and has length at most 1/K, each interval
contains at most one point from S, so the uniform distribution on the
set T (S) ={t : S ∩ It (cid:1)= ∅} is a ﬂat k-source. Moreover, if we perform a
uniformly random rotation of S on the circle to obtain a rotated set R
and then choose a uniformly random element of T (R), the probability
that we output any value t ∈ [N ] is exactly the length of It, which equals
Pr[X = t]. Thus we have decomposed X as a convex combination of ﬂat
k-sources. (Speciﬁcally, X =
T pT UT , where the sum is over subsets
T ⊆ [N ] of size K, and pT = PrR[T (R) =T ].)

(cid:4)

(cid:4)

We also sketch another proof of Lemma 6.10 that can be more
easily generalized to other classes of sources. We can view a random
variable X taking values in [N ] as anN -dimensional vector, where
X(i) is the probability mass of i. Then X is a k-source if and only if
X(i) ∈ [0, 2−k] for every i ∈ [N ] and
i X(i) = 1. The set of vectors
X satisfying these linear inequalities is a convex polytope in RN . By
basic linear programming theory, all of the points in the polytope are
convex combinations of its vertices, which are deﬁned to be the points
that make a maximal subset of the inequalities tight. By inspection, the
vertices of the polytope of k-sources are those sources where X(i) = 2−k
for 2k values of i and X(i) = 0 for the remaining values of i; these are
simply the ﬂat k-sources.

6.1.3 Seeded Extractors

Proposition 6.6 tells us that it is impossible to have deterministic
extractors for unpredictable sources. Here we consider k-sources, which
are more general than unpredictable sources, and hence it is also



<!-- pdf-page: 178 -->
6.1 Motivation and Deﬁnition

175

impossible to have deterministic extractors for them. The impossibility
result for k-sources is stronger and simpler to prove.

Proposition 6.11. For any Ext : {0, 1}n → {0, 1} there exists an
(n − 1)-source X so that Ext(X) is constant.

Proof. There exists b ∈ {0, 1} so that |Ext−1(b)| ≥2 n/2 = 2n−1. Then
let X be the uniform distribution on Ext−1(b).

On the other hand, if we reverse the order of quantiﬁers, allowing the
extractor to depend on the source, it is easy to see that good extractors
exist and in fact a randomly chosen function will be a good extractor
with high probability.

Proposition 6.12. For every n, k, m ∈ N, every ε >0, and every ﬂat
k-source X, if we choose a random function Ext : {0, 1}n → {0, 1}m with
m = k − 2 log(1/ε) − O(1), then Ext(X) will be ε-close to Um with
probability 1 − 2−Ω(Kε2), where K = 2k.

(In this section, we will make extensive use of the convention that
capital variables are 2 raised to the power of the corresponding lower-
case variable, such as K = 2k above.)

Proof. Choose our extractor randomly. We want it to have following
property: for all T ⊂ [M ], | Pr[Ext(X) ∈ T ] − Pr[Um ∈ T ]| ≤ε. Equiva-
lently, |{x ∈ Supp(X) : Ext(x) ∈ T }|/K diﬀers from the density µ(T )
by at most ε. For each point x ∈ Supp(X), the probability that
Ext(x) ∈ T is µ(T ), and these events are independent. By the Chernoﬀ
Bound (Theorem 2.21) for each ﬁxed T , this condition holds with prob-
ability at least 1 − 2−Ω(Kε2). Then the probability that condition is
violated for at least one T is at most 2M 2−Ω(Kε2), which is less than 1
for m = k − 2 log(1/ε) − O(1).

Note that the failure probability is doubly-exponentially small in k.
Naively, one might hope that we could get an extractor that’s good for
all ﬂat k-sources by a union bound. But the number of ﬂat k-sources



<!-- pdf-page: 179 -->
176 Randomness Extractors

(cid:1)

(cid:2)

N
K

≈ N K (where N = 2n), which is unfortunately a larger double-
is
exponential in k. We can overcome this gap by allowing the extractor
to be “slightly” probabilistic, i.e., allowing the extractor a seed con-
sisting of a small number of truly random bits in addition to the weak
random source. We can think of this seed of truly random bits as a
random choice of an extractor from family of extractors. This leads to
the following crucial deﬁnition:

Deﬁnition 6.13 (seeded extractors). A function Ext : {0, 1}n ×
{0, 1}d → {0, 1}m is a (k, ε)-extractor if for every k-source X on {0, 1}n,
Ext(X, Ud) isε-close to Um.

(Sometimes we will refer to extractors Ext : [N ] × [D] → [M ] whose
domain and range do not consist of bit-strings. These are deﬁned in the
natural way, requiring that Ext(X, U[D]) isε-close to U[M ].)

The goal is to construct extractors that minimize d and maximize m.

We prove the following theorem.

Theorem 6.14. For every n ∈ N, k ∈ [0, n] and ε >0, there exists
a (k, ε)-extractor Ext : {0, 1}n × {0, 1}d → {0, 1}m with m = k + d −
2 log(1/ε) − O(1) and d = log(n − k) + 2 log(1/ε) +O (1).

One setting of parameters to keep in mind (for our application of
simulating randomized algorithms with a weak source) is k = δn, with δ
a ﬁxed constant (e.g., δ = 0.01), and ε a ﬁxed constant (e.g., ε = 0.01).

Proof. We use the Probabilistic Method. By Lemma 6.10, it suﬃces for
Ext to work for ﬂat k-sources. Choose the extractor Ext at random.
Then the probability that the extractor fails is at most the number of
ﬂat k-sources times the probability Ext fails for a ﬁxed ﬂat k-source.
By the above proposition, the probability of failure for a ﬁxed ﬂat k-
source is at most 2−Ω(KDε2), since (X, Ud) is a ﬂat (k + d)-source) and
m = k + d − 2 log( 1
ε ) − O(1). Thus the total failure probability is at
most

(cid:14)

(cid:15)

N
K

· 2−Ω(KDε2) ≤

(cid:14)

(cid:15)

N e
K

K

2−Ω(KDε2).



<!-- pdf-page: 180 -->
6.1 Motivation and Deﬁnition

177

than 1 if Dε2 ≥ c log(N e/K) =c·
The latter expression is
(n − k) +c (cid:3) for constants c, c(cid:3). This is equivalent to d ≥ log(n − k) +
2 log( 1

less

ε ) +O (1).

It turns out that both bounds (on m and d) are individually tight

up to the O(1) terms.

Recall that our motivation for extractors was to simulate random-
ized algorithms given only a weak random source, so allowing a truly
random seed may seem to defeat the purpose. However, if the seed is
of logarithmic length as in Theorem 6.14, then instead of selecting it
randomly, we can enumerate all possibilities for the seed and take a
majority vote.

Proposition 6.15. Let A(w; r) be a randomized algorithm for
computing a function f such that A(w; Um) has error probability
at most γ (i.e., Pr[A(w; Um) (cid:1)= f (w)] ≤ γ]), and let Ext : {0, 1}n ×
{0, 1}d → {0, 1}m be a (k, ε)-extractor. Deﬁne

A(cid:3)(w; x) = maj
y∈{0,1}d

{A(w; Ext(x, y))}.

Then for every k-source X on {0, 1}n, A(cid:3)(w; X) has error probability
at most 2 · (γ + ε).

Proof. The probability that A(w; Ext(X, Ud)) is incorrect is not more
than the probability A(w; Um) is incorrect plus ε,
i.e., γ + ε, by
the deﬁnition of statistical diﬀerence. Then the probability that
majy A(w, Ext(X, y)) is incorrect is at most 2 · (γ + ε), because each
error of majy A(w; Ext(x, y)) corresponds to A(w; Ext(x, Ud)) erring
with probability at least 1/2.

Note that the enumeration incurs a 2d factor slowdown in the sim-
ulation. Thus, to retain running time poly(m), we want to construct
extractors where (a) d = O(log n); (b) Ext is computable in polynomial
time; and (c) m = nΩ(1).

We remark that the error probability in Proposition 6.15 can actu-
ally be made exponentially small by using an extractor that is designed
for slightly lower min-entropy. (See Problem 6.2.)



<!-- pdf-page: 181 -->
178 Randomness Extractors

We note that even though seeded extractors suﬃce for simulating
randomized algorithms with only a weak source, they do not suﬃce
for all applications of randomness in theoretical computer science. The
trick of eliminating the random seed by enumeration does not work, for
example, in cryptographic applications of randomness. Thus the study
of deterministic extractors for restricted classes of sources remains a
very interesting and active research direction. We, however, will focus
on seeded extractors, due to their many applications and their connec-
tions to the other pseudorandom objects we are studying.

6.2 Connections to Other Pseudorandom Objects

As mentioned earlier, extractors have played a unifying role in the
theory of pseudorandomness, through their close connections with a
variety of other pseudorandom objects. In this section, we will see two
of these connections. Speciﬁcally, how by reinterpreting them appropri-
ately, extractors can be viewed as providing families of hash functions,
and as being a certain type of highly expanding graphs.

6.2.1 Extractors as Hash Functions

Proposition 6.12 says that for any subset S ⊂ [N ] of size K, if we choose
a completely random hash function h : [N ] → [M ] for M   K, then h
will map the elements of S almost-uniformly to [M ]. Equivalently, if
we let H be distributed uniformly over all functions h : [N ] → [M ] and
X be uniform on the set S, then (H, H(X)) is statistically close to
(H, U[M ]), where we use the notation UT to denote the uniform distri-
bution on a set T . Can we use a smaller family of hash functions than
the set of all functions h : [N ] → [M ]? This gives rise to the following
variant of extractors.

Deﬁnition 6.16 (strong extractors). Extractor Ext : {0, 1}n ×
{0, 1}d → {0, 1}m is a strong (k, ε)-extractor if
for every k-source
X on {0, 1}n, (Ud, Ext(X, Ud)) is ε-close to (Ud, Um). Equivalently,
Ext(cid:3)(x, y) = (y, Ext(x, y)) is a standard (k, ε)-extractor.



<!-- pdf-page: 182 -->
6.2 Connections to Other Pseudorandom Objects

179

The nonconstructive existence proof of Theorem 6.14 can be

extended to establish the existence of very good strong extractors:

Theorem 6.17. For every n, k ∈ N and ε >0 there exists a
strong (k, ε)-extractor Ext : {0, 1}n × {0, 1}d → {0, 1}m with m = k −
2 log(1/ε) − O(1) and d = log(n − k) + 2 log(1/ε) +O (1).

Note that the output length is m ≈ k instead of m ≈ k + d; intu-
itively a strong extractor needs to extract randomness that is indepen-
dent of the seed and thus can only get the k bits from the source.

We see that strong extractors can be viewed as very small families of
hash functions having the almost-uniform mapping property mentioned
above. Indeed, our ﬁrst explicit construction of extractors is obtained
by using pairwise independent hash functions.

Theorem 6.18 (Leftover Hash Lemma). If H = {h : {0, 1}n →
{0, 1}m} is a pairwise independent (or even 2-universal) family of hash
functions where m = k − 2 log(1/ε), then Ext(x, h) def= h(x) is a strong
(k, ε)-extractor. Equivalently, Ext(x, h) = (h, h(x)) is a standard (k, ε)-
extractor.

Note that the seed length equals the number of random bits required
to choose h R← H, which is at least n by Problem 3.5.2 This is far
from optimal; for the purposes of simulating randomized algorithms we
would like d = O(log n). However, the output length of the extractor is
m = k − 2 log(1/ε), which is optimal up to an additive constant.

Proof. Let X be an arbitrary k-source on {0, 1}n, H as above, and
H R← H. Let d be the seed length. We show that (H, H(X)) is ε-close
to Ud × Um in the following three steps:

(1) We show that the collision probability of (H, H(X)) is close

to that of Ud × Um.

2 Problem 3.5 refers to pairwise independent families, but a similar argument shows that
universal families require Ω(n) random bits. (Instead of constructing orthogonal vectors,
we construct vectors that have nonpositive dot product.)



<!-- pdf-page: 183 -->
180 Randomness Extractors

(2) We note that this is equivalent to saying that the (cid:6)2 distance

between (H, H(X)) and Ud × Um is small.

(3) Then we deduce that the statistical diﬀerence is small, by
recalling that the statistical diﬀerence equals half of the (cid:6)1
distance, which can be (loosely) bounded by the (cid:6)2 distance.

of

(1): By

deﬁnition, CP(H, H(X)) = Pr[(H, H(X)) =
Proof
(H (cid:3), H (cid:3)(X (cid:3)))], where (H (cid:3), X (cid:3))
independent of and identically
is
distributed to (H, X). Note that (H, H(X)) = (H (cid:3), H (cid:3)(X)) if and only
if H = H (cid:3) and either X = X (cid:3) or X (cid:1)= X (cid:3) but H(X) =H (X (cid:3)). Thus

CP(H, H(X)) = CP(H) · (CP(X) + Pr[H(X) =H (X (cid:3)) | X (cid:1)= X (cid:3)])
(cid:15)

(cid:14)

≤ 1
D

·

1
K

+

1
M

≤ 1 +ε 2
DM

.

To see the penultimate inequality, note that CP(H) = 1/D because
there are D hash functions, CP(X) ≤ 1/K because H∞(X) ≥ k, and
Pr [H(X) =H (X (cid:3)) |X (cid:1)= X (cid:3)] ≤ 1/M by 2-universality.

Proof of (2):

(cid:21)(H, H(X)) − Ud × Um(cid:21)2 = CP(H, H(X)) − 1
DM
ε2
DM

≤ 1 +ε 2
DM

− 1
DM

=

.

Proof of (3): Recalling that the statistical diﬀerence between two

random variables X and Y is equal to 1
2

|X − Y |1, we have:

∆((H, H(X)), Ud × Um) =

· |(H, H(X)) − Ud × Um|
1

1
2
√

· (cid:21)(H, H(X)) − Ud × Um(cid:21)
(cid:30)

≤

≤

=

DM
2

√

DM
2

·

ε
2

.

ε2
DM

Thus, we have in fact obtained a strong (k, ε/2)-extractor.



<!-- pdf-page: 184 -->
6.2 Connections to Other Pseudorandom Objects

181

The proof above actually shows that Ext(x, h) =h(x ) extracts with
respect to collision probability, or equivalently, with respect to the
(cid:6)2-norm. This property may be expressed in terms of R´enyi entropy
H2(Z) def= log(1/CP(Z)). Indeed, we can deﬁne Ext : {0, 1}n× {0, 1}d −→
{0, 1}m to be a (k, ε) R´enyi-entropy extractor if H2(X) ≥ k implies
H2(Ext(X, Ud)) ≥ m − ε (or H2(Ud, Ext(X, Ud)) ≥ m + d − ε for strong
R´enyi-entropy extractors). Then the above proof shows that pairwise-
independent hash functions yield strong R´enyi-entropy extractors.

In general,

it turns out that an extractor with respect to
R´enyi entropy must have seed length d ≥ min{m/2, n − k} −O (1) (as
opposed to d = O(log n)); this explains why the seed length in the above
extractor is large. (See Problem 6.4.)

6.2.2 Extractors versus Expanders

Extractors have a natural interpretation as graphs. Speciﬁcally, we can
interpret an extractor Ext : {0, 1}n × {0, 1}d −→ {0, 1}m as the neigh-
bor function of a bipartite multigraph G = ([N ], [M ], E) with N = 2n
left-vertices, M = 2m right-vertices, and left-degree D = 2d,3 where the
rth neighbor of left-vertex u is Ext(u, r). Typically n % m, so the graph
is very unbalanced. It turns out that the extraction property of Ext
is related to various “expansion” properties of G. In this section, we
explore this relationship.

Let Ext : {0, 1}n × {0, 1}d −→ {0, 1}m be a (k, ε)-extractor and
G = ([N ], [M ], E) the associated graph. Recall that it suﬃces to
examine Ext with respect to ﬂat k-sources: in this case, the extractor
property says that given a subset S of size K = 2k on the left, a
random neighbor of a random element of S should be close to uniform
on the right. In particular, if S ⊂ [N ] is a subset on the left of size K,
then |N (S)| ≥(1 − ε)M . This property is just like vertex expansion,
except that it ensures expansion only for sets of size exactly K, not
any size ≤ K. Recall that we call such a graph an (= K, A) vertex
expander (Deﬁnition 5.32). Indeed, this gives rise to the following
weaker variant of extractors.

3 This connection is the reason we use d to denote the seed length of an extractor.



<!-- pdf-page: 185 -->
182 Randomness Extractors

Deﬁnition 6.19 (dispersers). A function Disp : {0, 1}n × {0, 1}d →
{0, 1}m is a (k, ε)-disperser if
for every k-source X on {0, 1}n,
Disp(X, Ud) has a support of size at least (1 − ε) · 2m.

While extractors can be used to simulate BPP algorithms with a
weak random source, dispersers can be used to simulate RP algorithms
with a weak random source. (See Problem 6.2.)

Then, we have:

Proposition 6.20. Let n, m, d ∈ N, K = 2k ∈ N, and ε >0. A func-
tion Disp : {0, 1}n × {0, 1}d → {0, 1}m is a (k, ε)-disperser iﬀ the
corresponding bipartite multigraph G = ([N ], [M ], E) with left-degree
D is an (= K, A) vertex expander for A = (1 − ε) · M/K.

Note that extractors and dispersers are interesting even when
M   K, so the expansion parameter A may be less than 1. Indeed,
A <1 is interesting for vertex “expanders” when the graph is highly
imbalanced. Still, for an optimal extractor, we have M = Θ(ε2KD)
(because m = k + d − 2 log(1/ε) − Θ(1)), which corresponds
to
expansion factor A = Θ(ε2D). (An optimal disperser actually gives
A = Θ(D/ log(1/ε)).) Note this is smaller than the expansion factor of
D/2 in Ramanujan graphs and D − O(1) in random graphs; the reason
is that those expansion factors are for “small” sets, whereas here we
are asking for sets to expand to almost the entire right-hand side.

Now let’s look for a graph-theoretic property that is equivalent
to the extraction property. Ext is a (k, ε)-extractor iﬀ for every set
S ⊂ [N ] of size K,

∆(Ext(US, U[D]), U[M ]) = max
T ⊂[M ]
− Pr[U[M ] ∈ T ]| ≤ε,

| Pr[Ext(US, U[D]) ∈ T ]

where US denotes the uniform distribution on S. This inequality
may be expressed in graph-theoretic terms as follows. For every



<!-- pdf-page: 186 -->
6.2 Connections to Other Pseudorandom Objects

183

(cid:16)

set T ⊂ [M ],

(cid:12)
(cid:12)
(cid:12)Pr

⇔

⇔

(cid:17)

(cid:16)

− Pr

U[M ] ∈ T

(cid:17)(cid:12)
(cid:12)
(cid:12) ≤ ε

(cid:12)
(cid:12)
(cid:12)
(cid:12) ≤ ε

Ext(US, U[D]) ∈ T
(cid:12)
(cid:12)
(cid:12)
(cid:12)
(cid:12)
(cid:12)
(cid:12)
(cid:12)

e(S, T )
|S|D
e(S, T )
N D

|T |
M

− µ(S)µ(T )

−

(cid:12)
(cid:12)
(cid:12)
(cid:12) ≤ εµ(S),

where e(S, T ) is the number of edges from S to T (as in Deﬁnition 4.13).

Thus, we have:

Proposition 6.21. A function Ext : {0, 1}n × {0, 1}d → {0, 1}m is a
(k, ε)-extractor iﬀ the corresponding bipartite multigraph G = ([N ],
[M ], E) with left-degree D has the property that |e(S, T )/N D−
µ(S)µ(T )| ≤εµ(S ) for every S ⊂ [N ] of size K and every T ⊂ [M ].

Note that this is very similar to the Expander Mixing Lemma
(Lemma 4.15), which states that if a graph G has spectral expansion λ,
then for all sets S, T ⊂ [N ] we have
(cid:12)
(cid:12)
(cid:12)
(cid:12)

− µ(S)µ(T )

(cid:12)
(cid:12)
(cid:12)
(cid:12) ≤ λ

µ(S)µ(T ).

(cid:7)

e(S, T )
N D
(cid:7)

µ(S)µ(T ) ≤ εµ(S) for all S ⊂ [N ] of size K and
It follows that if λ
all T ⊂ [N ], then G gives rise to a (k, ε)-extractor (by turning G into a
D-regular bipartite graph with N vertices on each side in the natural
way). It suﬃces for λ ≤ ε ·

K/N for this to work.

(cid:7)

(cid:7)

We can use this connection to turn our explicit construction of spec-
tral expanders into an explicit construction of extractors. To achieve
λ ≤ ε ·
K/N , we can take an appropriate power of a constant-degree
expander. Speciﬁcally, if G0 is a D0-regular expander on N vertices with
bounded second eigenvalue, we can consider the tth power of G0, G =
N/K)) = O(n − k + log(1/ε)). The degree
Gt
of G is D = Dt
0, sod = log D = O(t). This yields the following result:

0, where t = O(log((1/ε)

(cid:7)

Theorem 6.22. For
(k, ε)-extractor
explicit
d = O(n − k + log(1/ε)).

every n, k ∈ N and ε >0,

there
Ext : {0, 1}n × {0, 1}d −→ {0, 1}n

is an
with



<!-- pdf-page: 187 -->
184 Randomness Extractors

Note that the seed length is signiﬁcantly better than in the
construction from pairwise-independent hashing when k is close to
n, sayk = n − O(n) (i.e., K = N 1−o(1)). The output length is n,
which is much larger than the typical output length for extractors
(usually m   n). Using a Ramanujan graph (rather than an arbitrary
constant-degree expander), the seed length can be improved to
d = n − k + 2 log(1/ε) +O (1), which yields an optimal output length
n = k + d − 2 log(1/ε) − O(1).

Another way of proving Theorem 6.22 is to use the fact that a
random step on an expander decreases the (cid:6)2 distance to uniform, like
in the proof of the Leftover Hash Lemma. This analysis shows that
we actually get a R´enyi-entropy extractor; and thus explains the large
seed length d ≈ n − k.

The following table summarizes the main diﬀerences between

“classic” expanders and extractors.

Table 6.1. Diﬀerences between “classic” expanders and extractors.

Expanders

Extractors

Measured by vertex or spectral

Measured by min-entropy/

expansion

Typically constant degree

statistical diﬀerence
Typically logarithmic or

poly-logarithmic degree

All sets of size at most K expand All sets of size exactly (or at

least) K expand

Typically balanced

Typically unbalanced, bipartite

graphs

6.2.3 List Decoding View of Extractors

In this section, we cast extractors into the same list-decoding frame-
work that we used to capture list-decodable codes, samplers, and
expanders (in Section 5.3). Recall that all of these objects could be
syntactically described as functions Γ : [N ] × [D] → [M ], and their
properties could be captured by bounding the sizes of sets of the
form LISTΓ(T, ε) def= {x : Pry[Γ(x, y) ∈ T ] > ε} for T ⊂ [M ]. We also



<!-- pdf-page: 188 -->
6.2 Connections to Other Pseudorandom Objects

185

considered a generalization to functions f : [M ] → [0, 1] where we
deﬁned LISTΓ(f, ε) def= LISTΓ(f, ε) ={x : Ey[f (Γ(x, y))] > ε}.

Conveniently, an extractor Ext : {0, 1}n × {0, 1}d → {0, 1}m already
meets the syntax of a function Γ : [N ] × [D] → [M ] (matching our
convention that N = 2n, D = 2d, M = 2m). The extraction property
can be described in the list-decoding framework as follows:

Proposition 6.23. Let Γ = Ext : [N ] × [D] → [M ], let K = 2k ∈ N,
and ε ∈ [0, 1].

(1) If Ext is a (k, ε) extractor, then for every f : [M ] → [0, 1], we

have

|LISTΓ(f, µ(f ) +ε)| < K.

(2) Suppose that for every T ⊂ [M ], we have

|LISTΓ(T, µ(T ) +ε)| ≤K.

Then Ext is a (k + log(1/ε), 2ε) extractor.

Proof.

(1) Suppose for contradiction that |LISTΓ(f, µ(f ) +ε)| ≥K .
Let X be uniformly distributed over LISTΓ(f, µ(f ) +ε).
Then X is a k-source, and

E[f (Ext(X, U[D]))] = E
R←X

x

[f (Ext(x, U[D]))]

> µ(f ) +ε

= E[f (U[M ])] + ε.

By Problem 6.1, this implies that Ext(X, U[D]) and U[M ]
are ε-far, contradicting the hypothesis that Ext is a (k, ε)
extractor.

(2) Let X be any (k + log(1/ε))-source. We need to show that
Ext(X, U[D]) is 2ε-close to U[M ]. That is, we need to show
that for every T ⊂ [M ], Pr[Ext(X, U[D]) ∈ T ] ≤ µ(T ) + 2ε.



<!-- pdf-page: 189 -->
186 Randomness Extractors

So let T be any subset of [M ]. Then

Pr[Ext(X, U[D]) ∈ T ]

≤ Pr[X ∈ LIST(T, µ(T ) +ε)]

+ Pr[Ext(X, U[D]) ∈ T |X /∈ LIST(T, µ(T ) +ε)]
≤ |LIST(T, µ(T ) +ε)| ·2 −(k+log(1/ε)) + (µ(T ) +ε)
≤ K · 2−(k+log(1/ε)) + µ(T ) +ε
= µ(T ) + 2ε.

The proposition does not give an exact list-decoding characterization
of extractors, as the two parts are not exactly converses of each other.
One diﬀerence is the extra log(1/ε) bits of entropy and the factor of 2
in ε appearing in Part 6.23. These are typically insigniﬁcant diﬀerences
for extractors; indeed even an optimal extractor loses Θ(log(1/ε)) bits
of entropy (cf. Theorem 6.14). A second diﬀerence is that Part 6.23
shows that extractors imply bounds on |LIST(f, µ(f ) +ε)| even for
fractional functions f , whereas Part 6.23 only requires bounds on
|LIST(T, µ(T ) +ε)| to deduce the extractor property. This only makes
the result stronger, and indeed we will utilize this below.

Notice that the conditions characterizing extractors here are iden-
tical to the ones characterizing averaging samplers in Proposition 5.30.
Actually, the condition in Part 6.23 is the one characterizing averaging
samplers, whereas the condition in Part 6.23 is the one characterizing
boolean averaging samplers. Thus we have:

Corollary 6.24. Let Ext : [N ] × [D] → [M ] and Samp : [N ] → [M ]D
be such that Ext(x, y) = Samp(x)y. Then:

(1) If Ext is a (k, ε) extractor, then Samp is a (K/N, ε) averaging

sampler, where K = 2k.

(2) If Samp is a (K/N, ε) boolean averaging sampler, then Ext

is a (k + log(1/ε), 2ε) extractor.

(3) If Samp is a (δ, ε) boolean averaging sampler, then Samp is

a (δ/ε, 2ε) averaging sampler.



<!-- pdf-page: 190 -->
6.2 Connections to Other Pseudorandom Objects

187

Thus, the only real diﬀerence between extractors and averaging
samplers is one of perspective, and both perspectives can be useful.
For example, in samplers, we measure the error probability δ = K/N =
2k/2n, whereas in extractors we measure the min-entropy threshold k
on its own. Thus, the sampler perspective can be more natural when
δ is relatively large compared to 1/N , and the extractor perspective
when δ becomes quite close to 1/N . Indeed, an extractor for min-
entropy k = o(n) corresponds to a sampler with error probability δ =
1/2(1−o(1))n, which means that each of the n bits of randomness used
by the sampler reduces the error probability by almost a factor of 2!

We can now also describe the close connection between strong
extractors and list-decodable codes when the alphabet size/output
length is small.

Proposition 6.25. Let Ext : [N ] × [D] → [M ] and Enc : [N ] → [M ]D
be such that Ext(x, y) = Enc(x)y, and let K = 2k ∈ N.

(1) If Ext

is

a

strong

(k, ε)

extractor,

then Enc

is

(1 − 1/M − ε, K) list-decodable.

(2) If Enc is (1 − 1/M − ε, K) list-decodable, then Ext is a

(k + log(1/ε), M · ε) strong extractor.

Proof.

(1) Follows from Corollaries 5.31 and 6.24.
(2) Let X be a (k + log(1/ε))-source and Y = U[D]. Then the
statistical diﬀerence between (Y, Ext(X, Y )) and Y × U[M ]
equals

∆((Y, Ext(X, Y )), Y × U[M ])

= E
R←Y
y
= E
R←Y
y
≤ M
2

y

[∆(Ext(X, y), U[M ])]

[∆(Enc(X)y, U[M ])]

(cid:11)

E
R←Y

max
z

Pr[Enc(X)y = z] − 1/M

,

(cid:13)



<!-- pdf-page: 191 -->
188 Randomness Extractors

where the last inequality follows from the (cid:6)1 formulation of
statistical diﬀerence.
So if we deﬁne r ∈ [M ]D by setting ry to be the value z
maximizing Pr[Enc(X)y = z] − 1/M , we have:

∆((Y, Ext(X, Y )), Y × U[M ])

· (Pr[(Y, Enc(X)Y ) ∈ Tr] − 1/M ),

· (Pr[X ∈ LIST(Tr, 1/M + ε)] + ε)

· (2−(k+log(1/ε)) · K + ε)

≤ M
2
≤ M
2
≤ M
2
≤ M · ε.

Note that the quantitative relationship between extractors and
list-decodable codes given by Proposition 6.25 deteriorates extremely
fast as the output length/alphabet size increases. Nevertheless, the
list-decoding view of extractors as given in Proposition 6.23 turns out
to be quite useful.

6.3 Constructing Extractors

In the previous sections, we have seen that very good extractors
exist — extracting almost all of the min-entropy from a source with
only a logarithmic seed length. But the explicit constructions we have
seen (via universal hashing and spectral expanders) are still quite far
from optimal in seed length, and in particular cannot be used to give
a polynomial-time simulation of BPP with a weak random source.

Fortunately, much better extractor constructions are known —
ones that extract any constant fraction of the min-entropy using
a logarithmic seed length, or extract all of the min-entropy using
a polylogarithmic seed length. In this section, we will see how to
construct such extractors.

6.3.1 Block Sources

We introduce a useful model of sources that has more structure than
an arbitrary k-source:



<!-- pdf-page: 192 -->
6.3 Constructing Extractors

189

Deﬁnition 6.26. A random variable X = (X1, X2, . . . , Xt) is a (k1, k2,
. . . , kt) block source if for every x1, . . . , xi−1, Xi|X1=x1,...,Xi−1=xi−1 is a
ki-source. If k1 = k2 = · · · = kt = k, then we call X a t × k block source.

Note that a (k1, k2, . . . , kt) block source is also a (k1 + · · · + kt)-
source, but it comes with additional structure — each block is
guaranteed to contribute some min-entropy. Thus, extracting random-
ness from block sources is an easier task than extracting from general
sources.

The study of block sources has a couple of motivations.

• They are a natural and plausible model of sources in their
own right. Indeed, they are more general than unpredictable-
bit sources of Section 6.1.1: if X ∈ UnpredBitsn,δ is broken
into t blocks of length (cid:6) = n/t, then the result is a t × δ(cid:3)(cid:6)
block source, where δ(cid:3) = log(1/(1 − δ)).

• We can construct extractors for general weak sources by
converting a general weak source into a block source. We
will see how to do this later in the section.

We now illustrate how extracting from block sources is easier than
from general sources. The idea is that we can extract almost-uniform
bits from later blocks that are essentially independent of earlier blocks,
and hence use these as a seed to extract more bits from the earlier
blocks. Speciﬁcally, for the case of two blocks we have the following:

Lemma 6.27. Let Ext1 : {0, 1}n1 × {0, 1}d1 → {0, 1}m1 be a (k1, ε1)-
extractor, and Ext2 : {0, 1}n2 × {0, 1}d2 → {0, 1}m2 be a (k2, ε2)-
extractor with m2 ≥ d1. Deﬁne Ext(cid:3)((x1, x2), y2) = (Ext1(x1, y1), z2),
where (y1, z2) is obtained by partitioning Ext2(x2, y2) into a preﬁx y1
of length d1 and a suﬃx z2 of length m2 − d1.

Then for every (k1, k2) block source X = (X1, X2) taking values
in {0, 1}n1 × {0, 1}n2, it holds that Ext(cid:3)(X, Ud2) is (ε1 + ε2)-close to
Um1 × Um2−d1.



<!-- pdf-page: 193 -->
190 Randomness Extractors

Proof. Since X2 is a k2-source conditioned on any value of X1 and Ext2
is a (k2, ε2)-extractor, it follows that (X1, Y1, Z2) = (X1, Ext2(X2, Ud2))
is ε2-close to (X1, Um2) = (X1, Ud1, Um2−d1).

Thus, (Ext1(X1, Y1), Z2) isε 2-close to (Ext1(X1, Ud1), Um2−d1),
which is ε1-close to (Um1, Um2−d1) because X1 is a k1-source and Ext1
is a (k1, ε1)-extractor.

By the triangle inequality, Ext(cid:3)(X, Ud2) = (Ext1(X1, Y1), Z2) is

(ε1 + ε2)-close to (Um1, Um2−d1).

The beneﬁt of this composition is that the seed length of Ext(cid:3)
depends only one of the extractors (namely Ext2) rather than being
the sum of the seed lengths. (If this is reminiscent of the zig–zag
product, it is because they are closely related — see Section 6.3.5).
Thus, we get to extract from multiple blocks at the “price of one.”
Moreover, since we can take d1 = m2, which is typically much larger
than d2, the seed length of Ext(cid:3) can even be smaller than that of Ext1.
The lemma extends naturally to extracting from many blocks:

Lemma 6.28. For i = 1, . . . , t, let Exti : {0, 1}ni × {0, 1}di → {0, 1}mi
be a (ki, εi)-extractor, and suppose that mi ≥ di−1 for every i = 1, . . . , t,
where we deﬁne d0 = 0. Deﬁne Ext(cid:3)((x1, . . . , xt), yt) = (z1, . . . , zt), where
for i = t, . . . , 1, we inductively deﬁne (yi−1, zi) to be a partition of
Exti(xi, yi) into a di−1-bit preﬁx and a (mi − di−1)-bit suﬃx.

Then for every (k1, . . . , kt) block source X = (X1, . . . , Xt) taking
values in {0, 1}n1 × · · · {0, 1}nt, it holds that Ext(cid:3)(X, Udt) isε-close to
Um for ε =

(cid:4)
t
i=1(mi − di−1).

(cid:4)
t
i=1 εi and m =

We remark that this composition preserves “strongness.” If each of
the Extis correspond to strong extractors in the sense that their seeds
are preﬁxes of their outputs, then Ext(cid:3) will also correspond to a strong
extractor. If in addition d1 = d2 = · · · = dt, then this construction can
be seen as simply using the same seed to extract from all blocks.

Already with this simple composition, we can simulate BPP with
an unpredictable-bit source (even though deterministic extraction
from such sources is impossible by Proposition 6.6). As noted above,
by breaking an unpredictable-bit source X with parameter δ into



<!-- pdf-page: 194 -->
6.3 Constructing Extractors

191

blocks of length (cid:6), we obtain a t × k block source for t = n/(cid:6), k = δ(cid:3)(cid:6),
and δ(cid:3) = log(1/(1 − δ)).

Suppose that δ is a constant. Set (cid:6) = (10/δ(cid:3)) log n, so that X
is a t × k block source for k = 10 log n, and deﬁne ε = n−2. Let-
ting Ext : {0, 1}(cid:4) × {0, 1}d → {0, 1}d+m be the (k, ε) extractor using
universal hash functions (Theorem 6.18), we have:

d = O((cid:6)) =O (log n)

and

m = k − 2 log

1
ε

− O(1) > k/2

Composing Ext with itself t times as in Lemma 6.27, we obtain
Ext(cid:3) : {0, 1}t·(cid:4) × {0, 1}d → {0, 1}d+t·m such that Ext(cid:3)(X, Ud)
isε (cid:3)-
for ε(cid:3) = 1/n. (Speciﬁcally, Ext(cid:3)((x1, . . . , xt), h) =
close to uniform,
(h, h(x1), . . . , h(xt)).) This tells us that Ext(cid:3) essentially extracts half of
the min-entropy from X, given a random seed of logarithmic length.
Plugging this extractor into the construction of Proposition 6.15 gives
us the following result.

Theorem 6.29. For every constant δ > 0, we can simulate BPP
with an unpredictable-bit source of parameter δ. More precisely, for
every L ∈ BPP and every constant δ > 0, there is a polynomial-time
algorithm A and a polynomial q such that for every w ∈ {0, 1}∗ and
every source X ∈ UnpredBitsq(|w|),δ, the probability that A(w; X) errs
is at most 1/|w|.

6.3.2 Reducing General Sources to Block Sources

Given the results of the previous section, a common approach to
constructing extractors for general k-sources is to reduce the case of
general k-sources to that of block sources.

One approach to doing this is as follows. Given a k-source X of
length n, where k = δn, pick a (pseudo)random subset S of the bits of
X, and let W = X|S be the bits of X in those positions. If the set S
is of size (cid:6), then we expect that W will have at least roughly δ(cid:6) bits of
min-entropy (with high probability over the choice of S). Moreover,
W reveals at most (cid:6) bits of information, so if (cid:6) < δn, intuitively there



<!-- pdf-page: 195 -->
192 Randomness Extractors

should still be min-entropy left in X. (This is justiﬁed by Lemma 6.30
below.) Thus, the pair (W, X) should be a block source. This approach
can be shown to work for appropriate ways of sampling the set S, and
recursive applications of it formed the original approach to construct-
ing good extractors (and is still useful in various contexts today). The
fact mentioned above, that conditioning on a string of length (cid:6) reduces
min-entropy by at most (cid:6) bits, is given by the following lemma (which
is very useful when working with min-entropy).

Lemma 6.30 (chain rule for min-entropy). If (W, X) are two
jointly distributed random variables, where (W, X) is ak -source and
|Supp(W )| ≤2 (cid:4), then for every ε >0, it holds that with probability at
least 1 − ε over w R← W , X|W =w is a (k − (cid:6) − log(1/ε))-source.

The proof of this lemma is left as an exercise (Problem 6.1).
This is referred to as the “chain rule” for min-entropy by anal-
ogy with the chain rule for Shannon entropy, which states that
HSh (X|W ) = HSh (W, X) − HSh (W ), where the conditional Shan-
non entropy is deﬁned to be HSh (X|W ) = E
[HSh (X|W =w)].
w
length at most (cid:6), we have
Thus,
HSh (X|W ) ≥ k − (cid:6). The chain rule for min-entropy is not quite as
clean; we need to assume that W has small support (rather than just
small min-entropy) and we lose log(1/ε) bits of additional min-entropy.
(The log(1/ε) bits of entropy can be saved by using an appropriate
notion of conditional min-entropy; see Problems 6.7 and 6.8.)

if HSh (W, X) ≥ k and W is of

R←W

Another approach, which we will follow, is based on the observation
that every source of high min-entropy rate (namely, greater than 1/2)
is (close to) a block source, as shown by the lemma below. Thus, we
will try to convert arbitrary sources into ones of high min-entropy rate.

Lemma 6.31. If X is an (n − ∆)-source of length n, and X = (X1, X2)
is a partition of X into blocks of lengths n1 and n2, then for every ε >0,
(X1, X2) isε-close to some ( n1 − ∆, n2 − ∆ − log(1/ε)) block source.

Consider ∆ = αn for a constant α < 1/2, and n1 = n2 = n/2. Then
each block contributes min-entropy at least (1/2 − α)n. The proofs of
Lemmas 6.30 and 6.31 are left as exercises (Problem 6.1).



<!-- pdf-page: 196 -->
6.3 Constructing Extractors

193

6.3.3 Condensers

The previous section left us with the problem of converting a general
k-source into one of high min-entropy rate. We will do this via the
following kind of object:

Deﬁnition 6.32. A function Con : {0, 1}n × {0, 1}d → {0, 1}m is a
k →ε k(cid:3) condenser if for every k-source X on {0, 1}n, Con(X, Ud) is
ε-close to some k(cid:3)-source. Con is lossless if k(cid:3) = k + d.

If k(cid:3)/m > k/n, then the condenser increases the min-entropy rate,
intuitively making extraction an easier task. Indeed, condensers with
k(cid:3) = m are simply extractors themselves.

Like extractors,

it is often useful to view condensers graph-
theoretically. Speciﬁcally, we think of Con as the neighbor function of
a bipartite multigraph G with N = 2n left vertices, left degree D = 2d,
and M = 2m right vertices.

The lossless condensing property of Con turns out to be equivalent

to G having vertex expansion close to the degree:

Proposition 6.33. Let n, d, m ∈ N, K = 2k ∈ N, and ε >0. A function
Con : {0, 1}n × {0, 1}d → {0, 1}m is a k →ε k + d lossless condenser if
and only if the corresponding bipartite multigraph G = ([N ], [M ], E)
of left degree D is an (= K, (1 − ε)D) vertex expander.

Proof. ⇒: Let S ⊂ [N ] be any set of size K. Then US is a
k-source,
to a ( k + d)-source. This
implies
that
Supp(Con(US, Ud)) = N (S) completes the proof.

|Supp(Con(US, Ud))| ≥(1 − ε) · 2k+d. Noting

so Con(US, Ud)

isε-close

that

⇐: By Lemma 6.10,

it suﬃces to prove that for every subset
S ⊂ [N ] of size K, it holds that Con(US, Ud) isε-close to a ( k + d)-
source. By expansion, we know that |N (S)| ≥(1 − ε) · KD. Since
there are only KD edges leaving S, by redirecting εKD of the edges,
we can ensure that they all go to KD distinct vertices in [M ]. The
uniform distribution on these KD vertices is a (k + d)-source that is
ε-close to Con(US, Ud).



<!-- pdf-page: 197 -->
194 Randomness Extractors

Recall that vertex expansion normally corresponds to the disperser
property (see Proposition 6.20), which is weaker than extraction and
condensing. Indeed, vertex expansion generally does not guarantee
much about the distribution induced on a random neighbor of a set
S, except that its support is large. However, in case the expansion is
very close to the degree (A = (1 − ε) · D), then the distribution must
be nearly ﬂat (as noted in the above proof).

By applying Proposition 6.33 to the expanders based on Parvaresh–

Vardy codes (Theorem 5.35), we get the following lossless condenser:

Theorem 6.34. For every constant α > 0, for all positive integers
n ≥ k and all ε >0, there is an explicit

k →ε k + d

condenser Con : {0, 1}n × {0, 1}d → {0, 1}m

lossless
O(log n + log(1/ε)) and m = (1 + α)k + O(log(n/ε)).

with

d =

Note that setting α to be a small constant, we obtain an output

min-entropy rate arbitrarily close to 1.

Problem 6.5 gives a simple extractor Ext for high min-entropy rate
when the error parameter ε is constant. Applying that extractor to the
output of the above condenser, we obtain extractors with a seed length
of d = O(log n) that extract Ω(k) almost-uniform bits (with constant
error ε) from sources of any desired min-entropy k. In the next section,
we will use the above condenser to give an eﬃcient construction of
extractors for arbitrary values of ε.

We remark that the fact that having output min-entropy rate
bounded away from 1 is not inherent for lossless condensers. Non-
constructively, there exist lossless condensers with output length m =
k + d + log(1/ε) +O (1), and Open Problem 5.36 about expanders
can be restated in the language of lossless condensers as follows:

Open Problem 6.35. Give an explicit construction of a k →ε k + d
lossless condenser Con : {0, 1}n × {0, 1}d → {0, 1}m with d = O(log n),
m = k + d + O(1), and ε = 0.01.



<!-- pdf-page: 198 -->
6.3 Constructing Extractors

195

If we had such a condenser, then we could get extractors that
extract all but O(1) bits of the min-entropy by then applying extractors
based on spectral expanders (Theorem 6.22).

6.3.4 The Extractor

In this section, we will use the ideas outlined in the previous section —
namely condensing and block-source extraction — to construct an
extractor that is optimal up to constant factors.

Theorem 6.36. For all positive integers n ≥ k and all ε >0, there
is an explicit (k, ε) extractor Ext : {0, 1}n × {0, 1}d → {0, 1}m with
m ≥ k/2 and d = O(log(n/ε)).

We will use the following building block, constructed in Problem 6.9.

Lemma 6.37. For every constant t >0 and all positive integers
n ≥ k and all ε >0, there is an explicit ( k, ε) extractor Ext :
{0, 1}n × {0, 1}d → {0, 1}m with m ≥ k/2 and d = k/t + O(log(n/ε)).

The point is that this extractor has a seed length that is an
arbitrarily large constant factor (approximately t/2) smaller than its
output length. Thus, if we use it as Ext2 in the block-source extraction
of Lemma 6.27, the resulting seed length will be smaller than that of
Ext1 by an arbitrarily large constant factor. (The seed length of the
composed extractor Ext(cid:3) in Lemma 6.27 is the same of that as Ext2,
which will be a constant factor smaller than its output length m2,
which we can take to be equal to the seed length d1 of Ext1.)

for

Overview of
the Construction. Note that
small min-
entropies k, namely k = O(log(n/ε)), the extractor we want is already
given by Lemma 6.37 with seed length d smaller than the output
length m by any constant factor. (If we allow d ≥ m, then extraction
is trivial — just output the seed.) Thus, our goal will be to recursively
construct extractors for large min-entropies using extractors for smaller
min-entropies. Of course, if Ext : {0, 1}n × {0, 1}d → {0, 1}m is a (k0, ε)



<!-- pdf-page: 199 -->
196 Randomness Extractors

extractor, say with m = k0/2, then it is also a (k, ε) extractor for every
k ≥ k0. The problem is that the output length is only k0/2 rather than
k/2. Thus, we need to increase the output length. This can be achieved
by simply applying extractors for smaller min-entropies several times:

Lemma 6.38. Suppose Ext1: {0, 1}n × {0, 1}d1 → {0, 1}m1 is a (k1, ε1)
extractor and Ext2 : {0, 1}n × {0, 1}d2 → {0, 1}m2 is a (k2, ε2) extractor
for k2 = k1 − m1 − log(1/ε3). Then Ext(cid:3) : {0, 1}n × {0, 1}d1+d2 →
{0, 1}m1+m2 deﬁned by Ext(cid:3)(x, (y1, y2)) = (Ext1(x, y1), Ext2(x, y2)) is a
(k1, ε1 + ε2 + ε3) extractor.

The proof of this lemma follows from Lemma 6.30. After condi-
tioning a k1-source X on W = Ext1(X, Ud1), X still has min-entropy
at least k1 − m1 − log(1/ε3) =k 2 (except with probability ε3), and
thus Ext2(X, Ud2) can extract an additional m2 almost-uniform bits.

ε1 = ε2 = ε3 = ε ≥ 2−0.1k,

To see how we might apply this, consider setting k1 = 0.8k and
k2 = k1 − m1 − log(1/ε3) ∈
m1 = k1/2,
[0.3k, 0.4k], and m2 = k2/2. Then we obtain a (k, 3ε) extractor Ext(cid:3)
with output length m = m1 + m2 > k/2 from two extractors for
min-entropies k1, k2 that are smaller than k by a constant factor, and
we can hope to construct the latter two extractors recursively via the
same construction.

Now, however, the problem is that the seed length grows by
a constant factor in each level of recursion (e.g., if d1 = d2 = d in
Lemma 6.38, we get seed length 2d rather than d). Fortunately, block
source extraction using the extractor of Lemma 6.37 gives us a method
to reduce the seed length by a constant factor. (The seed length of the
composed extractor Ext(cid:3) in Lemma 6.27 is the same of that as Ext2,
which will be a constant factor smaller than its output length m2,
which we can take to be equal to the seed length d1 of Ext1. Thus, the
seed length of Ext(cid:3) will be a constant factor smaller than that of Ext1.)
In order to apply block source extraction, we ﬁrst need to convert our
source to a block source; by Lemma 6.31, we can do this by using the
condenser of Theorem 6.34 to make its entropy rate close to 1.

One remaining issue is that the error ε still grows by a con-
stant factor in each level of recursion. However, we can start with



<!-- pdf-page: 200 -->
6.3 Constructing Extractors

197

polynomially small error at the base of the recursion and there are only
logarithmically many levels of recursion, so we can aﬀord this blow-up.
We now proceed with the proof details. It will be notationally
convenient to do the steps in the reverse order from the description
above — ﬁrst we will reduce the seed length by a constant factor via
block-source extraction, and then apply Lemma 6.38 to increase the
output length.

Proof of Theorem 6.36. Fix n ∈ N and ε0 > 0. Set d = c log(n/ε0)
for an error parameter ε0 and a suﬃciently large constant c to be
determined in the proof below. (To avoid ambiguity, we will keep
the dependence on c explicit throughout the proof, and all big-Oh
notation hides universal constants independent of c.) For k ∈ [0, n], let
i(k) be the smallest nonnegative integer i such that k ≤ 2i · 8d. This
will be the level of recursion in which we handle min-entropy k; note
that i(k) ≤ log k ≤ log n.

For

every k ∈ [0, n], we will

construct an explicit Extk :
{0, 1}n × {0, 1}d → {0, 1}k/2
for an
appropriate sequence ε0 ≤ ε1 ≤ ε2 · · · . Note that we require the seed
length to remain d and the fraction of min-entropy extracted to remain
1/2 for all values of k. The construction will be by induction on i(k).

is a (k, εi(k)) extractor,

that

i(k) = 0, i.e., k ≤ 8d. The construction of Extk follows
Base Case:
from Lemma 6.37, setting t = 9 and taking c to be a suﬃciently large
constant.

Inductive Case: We construct Extk for i(k) ≥ 1 from extractors
Extk(cid:2) with i(k(cid:3)) < i(k) as follows. Given a k-source X of length n,
Extk works as follows.

(1) We apply the condenser of Theorem 6.34 to convert X into
a source X (cid:3) that is ε0-close to a k-source of length (9/8)k +
O(log(n/ε0)). This requires a seed of length O(log(n/ε0)).

(2) We divide X (cid:3)

into two equal-sized halves (X1, X2). By
Lemma 6.31, (X1, X2) is 2ε0-close to a 2 × k(cid:3) block source for

k(cid:3) = k/2 − k/8 − O(log(n/ε0)).



<!-- pdf-page: 201 -->
198 Randomness Extractors

that

i(k(cid:3)) < i(k). Since

i(k) ≥ 1, we also have
Note
k(cid:3) ≥ 3d − O(log(n/ε0)) ≥ 2d, for a suﬃciently large choice
of the constant c.

(3) Now we apply block-source extraction as in Lemma 6.27.
We take Ext2 to be a (2d, ε0) extractor from Lemma 6.37
with parameter t = 16, which will give us m2 = d output
length d2 = (2d)/16 + O(log(n/ε0)).
bits using a seed of
For Ext1, we use our recursively constructed Extk(cid:2), which
has seed length d, error εi(k(cid:2)), and output length k(cid:3)/2 ≥ k/6
(where the latter inequality holds for a suﬃciently large
choice of the constant c, because k > 8d >8c log(1/ε)).

All

so far has

in all, our extractor

seed length at most
error at most εi(k)−1 + O(ε0), and output
d/8 +O (log(n/ε0)),
length at least k/6. This would be suﬃcient for our induction except
that the output length is only k/6 rather than k/2. We remedy this
by applying Lemma 6.38.

the

extractor above

With one application of the extractor above, we extract at least
m1 = k/6 bits of
the source min-entropy. Then with another
application of
for min-entropy threshold
k2 = k − m1 − log(1/ε0) = 5k/6 − log(1/ε0), by Lemma 6.38, we
extract another (5k/6 − log(1/ε0))/6 bits and so on. After four applica-
tions, we have extracted all but (5/6)4 · k + O(log(1/ε0)) ≤ k/2 bits of
the min-entropy. Our seed length is then 4 · (d/8 +O (log(n/ε0))) ≤ d
and the total error is εi(k) = O(εi(k)−1).

Solving the recurrence for the error, we get εi = 2O(i) · ε0 ≤
poly(n) · ε0, so we can obtain error ε by setting ε0 = ε/poly(n). As far
as explicitness, we note that computing Extk consists of four evalua-
tions of our condenser from Theorem 6.34, four evaluations of Extk(cid:2)
for values of k(cid:3) such that i(k(cid:3)) < (i(k) − 1), four evaluations of the
explicit extractor from Lemma 6.37, and simple string manipulations
that can be done in time poly(n, d). Thus, the total computation time
is at most 4i(k) · poly(n, d) = poly(n, d).

Repeatedly

applying Lemma

from
Theorem 6.36, we can extract any constant fraction of the min-entropy
using a logarithmic seed length, and all the min-entropy using a
polylogarithmic seed length.

extractors

using

6.38



<!-- pdf-page: 202 -->
6.3 Constructing Extractors

199

Corollary 6.39. The following holds for every constant α > 0.
For every n ∈ N, k ∈ [0, n], and ε >0, there is an explicit ( k, ε)
extractor Ext : {0, 1}n × {0, 1}d → {0, 1}m with m ≥ (1 − α)k and
d = O(log(n/ε)).

Corollary 6.40. For every n ∈ N, k ∈ [0, n], and ε >0, there is
(k, ε) extractor Ext : {0, 1}n × {0, 1}d → {0, 1}m with
an explicit
m = k − O(log(1/ε)) and d = O(log k · log(n/ε)).

We remark that the above construction can be modiﬁed to yield
strong extractors achieving the same output lengths as above (so the
entropy of the seed need not be lost in Corollary 6.40).

A summary of the extractor parameters we have seen is in the

following table.

Table 6.2. Parameters for some constructions of (k, 0.01) extractors.

Method

Seed Length d

Output Length m

Optimal and Nonconstructive
Necessary for BPP

log(n − k) +O (1)
O(log n)

k + d − O(1)
kΩ(1)

Simulation

Spectral Expanders
Pairwise Independent

Hashing
Corollary 6.39

Corollary 6.40

O(n − k)
O(n)

O(log n)

O(log2 n)

n
k + d − O(1)

(1 − γ)k,
any constant γ > 0
k − O(1)

While Theorem 6.36 and Corollary 6.39 give extractors that are
optimal up to constant factors in both the seed length and output
length, it remains an important open problem to get one or both of
these to be optimal to within an additive constants while keeping the
other optimal to within a constant factor.

Open Problem 6.41. Give an explicit construction of (k, 0.01) extrac-
tors Ext : {0, 1}n × {0, 1}d → {0, 1}m with seed length d = O(log n)
and output length m = k + d − O(1).



<!-- pdf-page: 203 -->
200 Randomness Extractors

By using the condenser of Theorem 6.34, it suﬃces to achieve
the above for high min-entropy rate, e.g., k = 0.99n. Alternatively,
a better condenser construction would also resolve the problem.
(See Open Problem 6.35.) We note that there is a recent construc-
tion of extractors with seed length d = O(log n) and output length
m = (1 − 1/polylog(n))k (improving the output length of m = Ω(k) of
Corollary 6.39, in the case of constant or slightly subconstant error).

Open Problem 6.42. Give an explicit construction of (k, 0.01) extrac-
tors Ext : {0, 1}n × {0, 1}d → {0, 1}m with seed length d = log n + O(1)
and m = Ω(k) (or even m = kΩ(1)).

One of the reasons that these open problems are signiﬁcant is that,
in many applications of extractors, the resulting complexity depends
exponentially on the seed length d and/or the entropy loss k + d − m.
(An example is the simulation of BPP with weak random sources given
by Proposition 6.15.) Thus, additive constants in these parameters
corresponds to constant multiplicative factors in complexity.

Another open problem is more aesthetic in nature. The construc-
tion of Theorem 6.36 makes use of the condenser of Theorem 6.36, the
Leftover Hash Lemma (Theorem 6.18) and the composition techniques
of Lemmas 6.27 and 6.38 in a somewhat complex recursion. It is of
interest to have a construction that is more direct. In addition to the
aesthetic appeal, such a construction would likely be more practical
to implement and provide more insight into extractors. In Chapter 7,
we will see a very direct construction based on a connection between
extractors and pseudorandom generators, but its parameters will
be somewhat worse than Theorem 6.36. Thus the following remains
open:

Open Problem 6.43. Give a “direct” construction of (k, ε) extractors
Ext : {0, 1}n × {0, 1}d → {0, 1}m with seed length d = O(log(n/ε)) and
m = Ω(k).



<!-- pdf-page: 204 -->
6.3 Constructing Extractors

201

6.3.5 Block-Source Extraction versus the Zig–Zag Product

To further highlight the connections between extractors and expanders,
extraction method of
here we describe how the block-source
Section 6.3.1 (which we used in the main extractor construction
of Theorem 6.36) is closely related to the zig–zag graph product
of Section 4.3.2.3 (which we used in the expander construction of
Theorem 4.39).

Recall the block-source extraction method of Lemma 6.27: We
deﬁne Ext(cid:3) : {0, 1}n1+n2 × {0, 1}d2 → {0, 1}m1 by Ext(cid:3)((x1, x2), y2) =
Ext1(x1, Ext2(x2, y2)). (Here we consider the special case that m2 = d1.)
Viewing the extractors as bipartite graphs, the left-vertex set is
[N1] × [N2] and the left-degree is D2. A random step from a vertex
(x1, x2) ∈ [N1] × [N2] corresponds to taking a random step from x2 in
G2 to obtain a right-hand vertex y1 ∈ {0, 1}m2, which we view as an
edge label y for G1. We then move to the yth neighbor of x1.

This is just like the ﬁrst two steps of the zig–zag graph product.
Why do we need a third step in the zig–zag product? It is because of
the slightly diﬀerent goals in the two settings. In a (spectral) expander,
we consider an arbitrary initial distribution that does not have too
much (R´enyi) entropy, and need to add entropy to it. In a block-source
extractor, our initial distribution is constrained to be a block source
(so both blocks have a certain amount of min-entropy), and our goal
is to produce an almost-uniform output (even if we end up with less
bits than the initial entropy).

Thus,

in the zig–zag setting, we must consider the following

extreme cases (that are ruled out for block sources):

• The second block has no entropy given the ﬁrst. Here, the
step using G2 will add entropy, but not enough to make
y1 close to uniform. Thus, we have no guarantees on the
behavior of the G1-step, and we may lose entropy with
it. For this reason, we keep track of the edge used in the
G1-step — that is, we remember b1 such that x1 is the b1th
neighbor of z1 = Ext(x1, y1). This ensures that the (edge-
rotation) mapping (x1, y1) (cid:14)→ (z1, b1) is a permutation and
does not lose any entropy. We can think of b1 as a “buﬀer”



<!-- pdf-page: 205 -->
202 Randomness Extractors

that retains any extra entropy in (x1, y1) that did not get
extracted into z1. So a natural idea is to just do block source
extraction, but output (z1, b1) rather than just z1. However,
this runs into trouble with the next case.

• The ﬁrst block has no entropy but the second block is
completely uniform given the ﬁrst. In this case, the G2 step
cannot add any entropy and the G1 step does not add any
entropy because it is a permutation. However, the G1 step
transfers entropy into z1. So if we add another expander-step
from b1 at the end, we can argue that it will add entropy.
This gives rise to the 3-step deﬁnition of the zig–zag product.

While we analyzed the zig–zag product with respect to spectral
expansion (i.e., R´enyi entropy), it is also possible to analyze it in
terms of a condenser-like deﬁnition (i.e., outputting distributions
ε-close to having some min-entropy). It turns out that a variant
of the zig–zag product for condensers leads to a construction of
constant-degree bipartite expanders with expansion (1 − ε) · D for
the balanced (M = N ) or nearly balanced (e.g., M = Ω(N )) case.
However, as mentioned in Open Problems 4.43, 4.44, and 5.36, there
are still several signiﬁcant open problems concerning the explicit
construction of expanders with vertex expansion close to the degree,
achieving expansion D − O(1) in the nonbipartite case, and achieving
a near-optimal number of right-hand vertices.

6.4 Exercises

Problem 6.1 (Min-entropy and Statistical Diﬀerence).

(1) Prove that for every two random variables X and Y ,

∆(X, Y ) = max

f

| E[f (X)] − E[f (Y )]| =

1
2

· |X − Y |1,

where the maximum is over all
(Hint: ﬁrst
| E[f (X)] − E[f (Y )]|.)

identify the

[0, 1]-valued functions f .
that maximize

functions f



<!-- pdf-page: 206 -->
6.4 Exercises

203

(2) Suppose that (W, X) are jointly distributed random variables
where (W, X) is ak -source and |Supp(W )| ≤2 (cid:4). Show that
for every ε >0, with probability at least 1 − ε over w R← W ,
we have X|W =w is a (k − (cid:6) − log(1/ε))-source.

(3) Suppose that X is an (n − ∆)-source taking values in {0, 1}n,
and we let X1 consist of the ﬁrst n1 bits of X and X2 the
remaining n2 = n − n1 bits. Show that for every ε >0,
(X1, X2) isε-close to some ( n1 − ∆, n2 − ∆ − log(1/ε))
block source.

Problem 6.2 (Simulating Randomized Algorithms with Weak
Sources).

error probability at most 1/3 (i.e.,

(1) Let A(w; r) be a randomized algorithm for computing
a function f using m random bits such that A(w; Um)
has
every
for
w, Pr[A(w; Um) (cid:1)= f (w)] ≤ 1/3)
let Ext: {0, 1}n×
{0, 1}d → {0, 1}m be a (k, 1/7)-extractor. Deﬁne A(cid:3)(w; x) =
majy∈{0,1}d{A(w; Ext(x; y)}
arbitrarily).
Show that for every (k + t)-source X, A(cid:3)(w; X) has error
probability at most 2−t.

(breaking

and

ties

(2) Let A(w; r) be a randomized algorithm for deciding a
language L using m random bits such that A(w; Um) has
one-sided error probability at most 1/2 (i.e., if w ∈ L, then
Pr[A(w; Um) = 1] ≥ 1/2 and if w /∈ L, then Pr[A(w; Um) =
1] = 0) and let Disp: {0, 1}n × {0, 1}d → {0, 1}m be a (k, 1/3)-
disperser. Show how to decide L with one-sided error at most
2−t given a single sample from a (k + t)-source X (with no
other randomness) and running A and Disp each 2d times.

Problem 6.3 (Almost-Universal Hashing). A family H of func-
tions mapping domain [N ] to [M ] is said to have collision probability



<!-- pdf-page: 207 -->
204 Randomness Extractors

at most δ if for every x1 (cid:1)= x2 ∈ [N ], we have

[H(x1) =H (x2)] ≤ δ.

Pr
R←H

H

H has is ε-almost universal
if it has collision probability at most
(1 + ε)/M . (Note that this is a relaxation of the notion of ε-almost
pairwise independence from Problem 3.4.)

(1) Show that if a family H = {h : [N ] → [M ]} is ε2-almost
universal, Ext(x, h) def= h(x) is a (k, ε) strong extractor for
k = m + 2 log(1/ε) +O (1), where m = log M .

(2) Use Problem 3.4 to deduce

every n ∈ N,
k ≤ n, and ε >0,
strong extractor
Ext : {0, 1}n × {0, 1}d → {0, 1}m with d = O(k + log(n/ε))
and m = k − 2 log(1/ε) − O(1).

is a (k, ε )

there

that

for

(3) Given a family H of functions mapping [N ] to [M ], we can
obtain a code Enc : [N ] → [M ]|H| by Enc(x)h = h(x), and
conversely. Show that H has collision probability at most δ
iﬀ Enc has minimum distance at least 1 − δ.

(4) Use the above connections and the list-decoding view
of extractors (Proposition 6.23) to prove the Johnson
if a code Enc : [N ] → [M ]ˆn
Bound for small alphabets:
has minimum distance at least 1 − 1/M − γ/M , then it is
(1 − 1/M −

γ, O(M/γ)) list-decodable.

√

(R´enyi

Problem 6.4
{0, 1}n × {0, 1}d → {0, 1}m a (k, ε) R´enyi extractor if
source X on {0, 1}n of R´enyi entropy at least k,
Ext(X, Ud) has R´enyi entropy at least m − ε.

extractors). Call

a

function Ext :
for every
it holds that

(1) Prove that a (k, ε) R´enyi extractor is also a (k, O(

√

ε))

extractor.

(2) Show that for every n, k, m ∈ N with m ≤ n and ε >0,
there exists a (k, ε) R´enyi extractor Ext : {0, 1}n × {0, 1}d →
{0, 1}m with d = O(min{n − k + log(1/ε), m/2 + log(n/ε)}).



<!-- pdf-page: 208 -->
6.4 Exercises

205

(3) Show that if Ext : {0, 1}n × {0, 1}d → {0, 1}m is a (k, 1)
R´enyi extractor, then d ≥ min{n − k, m/2} −O (1). (Hint:
consider a k-source that is uniform over {x : ∃yExt(x, y) ∈ T }
for an appropriately chosen set T .)

Problem 6.5 (Extractors versus Samplers). Use the connection
between extractors and averaging samplers to do the following:

(1) Prove that for all constants ε, α > 0, there is a constant β < 1
such that for all n, there is an explicit (βn, ε) extractor Ext :
{0, 1}n × {0, 1}d → {0, 1}m with d ≤ log n and m ≥ (1 − α)n.
(2) Prove that for every m ∈ N, ε, δ > 0, there exists a (non-
(δ, ε) averaging sampler Samp : {0, 1}n →
n = m + 2 log(1/ε) + log(1/δ) +O (1)

constructive)
({0, 1}m)t
random bits and t = O((1/ε2) · log(1/δ)) samples.

using

(1) Suppose we are given a constant-error BPP algorithm that
uses r = r(n) random bits on inputs of length n. Show how,
using the explicit extractor of Theorem 6.36, we can reduce
its error probability to 2−(cid:4) using O(r) +(cid:6)
random bits,
for any polynomial (cid:6) = (cid:6)(n). (Note that this improves the
r + O((cid:6)) given by expander walks for (cid:6) % r.) Conclude that
every problem in BPP has a randomized polynomial-time
algorithm that only errs for 2q0.01
choices of its q = q(n)
random bits.

Problem 6.6 (Extracting from Unpredictable-Bit Sources).

(1) Let X be a source taking values in {0, 1}n such that
for all x, y, Pr[X = x]/ Pr[X = y] ≤ (1 − δ)/δ. Show that
X ∈ UnpredBitsn,δ.

(2) Prove that for every function Ext : {0, 1}n → {0, 1} and
there exists a source X ∈ UnpredBitsn,δ
or

every δ > 0,
with parameter

such that Pr[Ext(X) = 1] ≤ δ

δ



<!-- pdf-page: 209 -->
206 Randomness Extractors

Pr[Ext(X) = 0] ≥ 1 − δ.
consider
(Hint:
X that is uniform on Ext−1(b) with probability 1 − δ and is
uniform on Ext−1(b) with probability δ.)

b ∈ {0, 1},

for

(3) (*) Show how to extract from sources in UnpredBitsn,δ
using a seeded extractor with a seed of constant length.
That is, the seed length should not depend on the length
n of the source, but only on the bias parameter δ and the
statistical diﬀerence ε from uniform desired. The number of
bits extracted should be Ω(δn).

Problem 6.7 (Average Min-Entropy). While there is no single
“correct” deﬁnition of conditional min-entropy, in this problem you
will explore one deﬁnition that is useful and has nice properties. For
two jointly distributed random variables (X, Y ) deﬁne
(cid:20)

(cid:21)

H∞(Y |X) = log

1

E
x

R←X

[maxy Pr[Y = y|X = x]]

.

(1) Prove that H∞(Y |X) = log(1/ maxP Pr[P (X) =Y ]), where
the maximum is over functions P from the domain of X
to the domain of Y . So average min-entropy captures the
unpredictability of Y from X.

(2) Show that if H∞(Y |X) ≥ k, then with probability at least
1 − ε over x R← X, we have H∞(Y |X=x) ≥ k − log(1/ε).

(3) Show

that

log |Supp(X)|.

H∞(Y ) ≥ H∞(Y |X) ≥ H∞(X, Y ) −

(4) Use the previous two items to deduce Problem 6.1, Part 6.1.
(5) Give an example showing that H∞(Y |X) can be much
smaller than H∞(Y ) − H∞(X). Speciﬁcally, construct n-bit
random variables where H∞(Y ) =n but H∞(Y |X) and
H∞(X) are both O(1).

Problem 6.8 (Average Min-Entropy Extractors). A function
Ext : {0, 1}n × {0, 1}d → {0, 1}m is a (k, ε) average min-entropy



<!-- pdf-page: 210 -->
6.4 Exercises

207

extractor if for every two jointly distributed random variables (X, Y )
such that X takes values in {0, 1}n and H∞(X|Y ) ≥ k, we have
(Ext(X, Ud), Y ) isε-close to ( Um, Y ), where Ud and Um are taken to be
independent of (X, Y ). By Problem 6.7, Part 6.7, it follows that if Ext
is a (k, ε) extractor, then it is a (k + log(1/ε), 2ε) average min-entropy
extractor. Below, you will show how to avoid the log(1/ε) entropy loss
from this reduction.

(1) (*) Show that

if Ext : {0, 1}n × {0, 1}d → {0, 1}m is a
(k, ε)-extractor with k ≤ n − 1, then for every t >0, Ext
is a (k − t, 2t+1 · ε)-extractor. (Hint: for a statistical test
T ⊆ {0, 1}m, relate the (k − t)-sources X maximizing the
distinguishing advantage | Pr[Ext(X, Ud) ∈ T ] − Pr[Um ∈ T ]|
to the k-sources maximizing the distinguishing advantage.)
(2) Show that if Ext : {0, 1}n × {0, 1}d → {0, 1}m is a (k, ε)-
extractor, then Ext is a (k, 3ε) average min-entropy extractor.
(3) Use these results and Problem 6.3 to improve Corollary‘6.40,
for every n ∈ N, k ≤ n, and ε >0, an
and construct,
extractor Ext : {0, 1}n × {0, 1}d → {0, 1}m
(k, ε)
explicit
with seed length d = O((log k) · (log(n/ε))) and output
length m = k + d − 2 log(1/ε) − O(1).

(The

Building-Block

Problem 6.9
Lemma 6.37: Show that for every constant
itive integers n ≥ k and all ε >0,
there is an explicit
extractor Ext : {0, 1}n × {0, 1}d → {0, 1}m with m ≥ k/2
d = k/t + O(log(n/ε)).
source with blocks of length k/O(t) +O (log(n/ε)).)

Extractor). Prove
t >0 and all pos-
(k, ε)-
and
into a block

convert

source

(Hint:

the

Problem 6.10 (Encryption and Deterministic Extraction). A
(one-time) encryption scheme with key length n and message length
m consists of an encryption function Enc : {0, 1}n × {0, 1}m → {0, 1}(cid:4)
and a decryption function Dec : {0, 1}n × {0, 1}(cid:4) → {0, 1}m such that
Dec(k, Enc(k, u)) = u for every k ∈ {0, 1}n and u ∈ {0, 1}m. Let K be



<!-- pdf-page: 211 -->
208 Randomness Extractors

a random variable taking values in {0, 1}n. We say that (Enc, Dec)
is (statistically) ε-secure with respect to K if for every two messages
u, v ∈ {0, 1}m, we have ∆(Enc(K, u), Enc(K, v)) ≤ ε. For example, the
one-time pad, where n = m = (cid:6) and Enc(k, u) =k ⊕ u = Dec(k, u) is
0-secure (a.k.a perfectly secure) with respect to the uniform distri-
bution K = Um. For a class C of sources on {0, 1}n, we say that the
encryption scheme (Enc, Dec) is ε-secure with respect to C if Enc is
ε-secure with respect to every K ∈ C.

(1) Show that

if

there exists a deterministic ε-extractor
Ext : {0, 1}n → {0, 1}m for C, then there exists an 2ε-secure
encryption scheme with respect to C.

(2) Conversely, use the following steps to show that if there
exists an ε-secure encryption scheme (Enc, Dec) with
respect to C, where Enc : {0, 1}n × {0, 1}m → {0, 1}(cid:4), then
there exists a deterministic 2ε-extractor Ext: {0, 1}n →
{0, 1}m−2 log(1/ε)−O(1)
for C, provided m ≥ log n + 2 log
(1/ε) +O (1).
(a) For each ﬁxed key k ∈ {0, 1}n, deﬁne a source Xk on
{0, 1}(cid:4) by Xk = Enc(k, Um), and let C(cid:3) be the class
of all these sources (i.e., C(cid:3) = {Xk : k ∈ {0, 1}n}).
Show that there exists a deterministic ε-extractor
Ext(cid:3) : {0, 1}(cid:4) → {0, 1}m−2 log(1/ε)−O(1) for C(cid:3), provided
m ≥ log n + 2 log(1/ε) +O (1).

(b) Show that if Ext(cid:3) is a deterministic ε-extractor for C(cid:3)
and Enc is ε-secure with respect to C, then Ext(k) =
Ext(cid:3)(Enc(k, 0m)) is a deterministic 2ε-extractor for C.

Thus, a class of sources can be used for secure encryption iﬀ it is
deterministically extractable.

Problem 6.11 (Extracting from Symbol-Fixing Sources*). A
generalization of a bit-ﬁxing source is a symbol-ﬁxing source X taking
values in Σn for some alphabet Σ, where subset of the coordinates of X
are ﬁxed and the rest are uniformly distributed and independent ele-
ments of Σ. For Σ = {0, 1, 2} and k ∈ [0, n], give an explicit ε-extractor



<!-- pdf-page: 212 -->
6.5 Chapter Notes and References

209

Ext : Σn → {0, 1}m for the class of symbol-ﬁxing sources on Σn with
min-entropy at least k, with m = Ω(k) and ε = 2−Ω(k). (Hint: use a
random walk on a consistently labelled 3-regular expander graph.)

6.5 Chapter Notes and References

Surveys on randomness extractors and their applications are given by
Nisan and Ta-Shma [301] and Shaltiel [352, 354].

The study of randomness extraction goes back to von Neu-
mann [416], who gave the deterministic extractor described in the text
for IID-bit sources. (See [130, 307] for improvements in the extraction
rate.) The study of extraction was renewed by Blum [69], who showed
how to extend von Neumann’s method to extract perfectly uniform
bits from a source generated by a ﬁnite-state Markov chain. Santha
and Vazirani [346] proposed the model of unpredictable-bit sources,
suggested that an extractor need only produce an output that is sta-
tistically close to uniform (rather than perfectly uniform), and proved
that there is no deterministic extractor for a single unpredictable-bit
source even under this relaxation (Proposition 6.6; the proof we give
in Problem 6.6 is from [334]). Vazirani and Vazirani [407] showed
that nevertheless every problem in BPP can be solved in polynomial
time given a single unpredictable-bit source (Theorem 6.29.) Chor and
Goldreich [96] generalized this result to block sources, in the process
introducing min-entropy to the literature on randomness extraction.
Cohen and Wigderson [107] showed how to simulate BPP with any
source of suﬃciently high min-entropy rate. This was strengthened to
any constant entropy rate by Zuckerman [426], and polynomially small
entropy rate in [343, 28].

The notion of seeded extractor we focus on in this section (Deﬁ-
nitions 6.13,6.16) was introduced by Nisan and Zuckerman [303], who
also gave the ﬁrst construction of extractors with polylogarithmic seed
length (building on [426]). A form of the Leftover Hash Lemma (for
ﬂat distributions, and where the quality of the output distribution
is measured with entropy rather than statistical diﬀerence) was
ﬁrst proven by Bennett, Brassard, and Robert [63]. The version in
Theorem 6.18 is due to Impagliazzo, Levin, and Luby [197], and the



<!-- pdf-page: 213 -->
210 Randomness Extractors

proof we give is due to Rackoﬀ [217]. The connection between the
Leftover Hash Lemma and the Johnson Bound in Problem 3.4 is
due to Ta-Shma and Zuckerman [383], with the equivalence between
almost-universal hashing and minimum distance being from [67]. The
extractor parameters of Problem 3.4 were ﬁrst obtained in [155, 372].
The study of deterministic extractors has also remained active,
motivated by applications in cryptography and other settings where
enumerating seeds does not work. Bit-ﬁxing sources, ﬁrst studied
in [63, 98, 409], received particular attention for their applications
to maintaining security when an adversary learns some bits of a
cryptographic secret key [90]. (There has been work on protecting
against even more severe forms of leakage, surveyed in [175].) The
deterministic extractor for symbol-ﬁxing sources in Problem 6.11 is
from [232]. Problem 6.10 (encryption requires deterministic extraction)
is due to Bosley and Dodis [77]. For a discussion of deterministic
extraction for other models of sources, see Section 8.2.

The relevance of bipartite expanders to simulating randomized
algorithms with weak sources is due to Cohen and Wigderson [107],
who studied dispersers and generalizations of them (as graphs rather
than functions). The expander-based extractor of Theorem 6.22 is due
to Goldreich and Wigderson [174]. The connection between extractors
and list-decodable codes emerged in the work of Trevisan [389], and
the list-decoding view of extractors (Proposition 6.23) was crystallized
by Ta-Shma and Zuckerman [383]. The equivalence between extractors
and averaging samplers (Corollary 6.24) is due to Zuckerman [427]
(building on previous connections between other types of samplers and
expanders/dispersers [365, 107]).

The notion of entropy was introduced by Shannon in his seminal
paper [361] that gave rise to the ﬁeld of information theory. The many
properties of Shannon entropy and related quantities and their appli-
cations to communications theory are covered in the textbook [110].
Therefore, the fact that Shannon entropy converges to min-entropy (up
to a vanishing statistical distance) when we take independent samples
is called the Asymptotic Equipartition Property. R´enyi entropy
(indeed the entropies Hα for all α ∈ (0, ∞)) were introduced in [335].



<!-- pdf-page: 214 -->
6.5 Chapter Notes and References

211

The fact that every k-source is a convex combination of ﬂat k-sources
(Lemma 6.10) is implicit in [96]. Our proof is due to Kalai [230].

The optimal nonconstructive bounds for extractor parameters
(Theorem 6.14) were identiﬁed by Radhakrishnan and Ta-Shma [315],
who proved a matching lower bound on seed length and upper bound
on output length.

The method for extracting from block sources given by Lemmas 6.27
and 6.28 was developed over a series of works [96, 410, 426]; the form
we use is from [303]. The ﬁrst method described in Section 6.3.2 for
converting general weak sources to block sources is from the original
papers of Nisan and Zuckerman [426, 303] (see [402] for a tighter
analysis). The observation that high min-entropy sources can be
partitioned into block sources, and the beneﬁts of this for constructing
extractors, is due to Goldreich and Wigderson [174]. Lossless con-
densers were ﬁrst introduced by Raz and Reingold [319] (formulated in
a slightly diﬀerent manner), and the general deﬁnition of condensers
is from Reingold, Shaltiel, and Wigderson [328]. The equivalence of
lossless condensing and vertex expansion close to the degree is from
Ta-Shma, Umans, and Zuckerman [382]. The extractor construction of
Section 6.3.4 is due to Guruswami, Umans, and Vadhan [192]. (Earlier
papers had results similar to Theorem 6.36 with some restrictions on
the parameters, such as k = Ω(n) [427] and 1/ε subpolynomial [272].)
Recently, Dvir, Kopparty, Saraf, and Sudan [124] constructed extrac-
tors that have logarithmic seed length and extract a 1 − O(1) fraction
of the min-entropy (for constant or slightly subconstant error).

The zig–zag product for extractors and condensers described in

Section 6.3.5 is from [332, 92].

Problem 6.2 (achieving exponentially small error when simulating

BPP with a weak source) is from [426].



<!-- pdf-page: 215 -->
7

Pseudorandom Generators

7.1 Motivation and Deﬁnition

In the previous sections, we have seen a number of
derandomization results:

interesting

• Derandomizing speciﬁc algorithms, such as the ones for

MaxCut and Undirected S-T Connectivity;

• Giving explicit (eﬃcient, deterministic) constructions of
various pseudorandom objects, such as expanders, extrac-
tors, and list-decodable codes, as well as showing various
relations between them;

• Reducing the randomness needed for certain tasks, such
as sampling and amplifying the success probability of
randomized algorithm; and

• Simulating BPP with any weak random source.

However, all of these still fall short of answering our original
motivating question, of whether every randomized algorithm can be
eﬃciently derandomized. That is, does BPP = P?

As we have seen, one way to resolve this question in the positive is
to use the following two-step process: First show that the number of

212



<!-- pdf-page: 216 -->
7.1 Motivation and Deﬁnition

213

random bits for any BPP algorithm can be reduced from poly(n) to
O(log n), and then eliminate the randomness entirely by enumeration.
Thus, we would like to have a function G that stretches a seed
of d = O(log n) truly random bits into m = poly(n) bits that “look
random.” Such a function is called a pseudorandom generator. The
question is how we can formalize the requirement that the output
should “look random” in such a way that (a) the output can be used
in place of the truly random bits in any BPP algorithm, and (b) such
a generator exists.

Some candidate deﬁnitions for what it means for the random

variable X = G(Ud) to “look random” include the following:

• Information-theoretic or statistical measures: For example,
we might measure entropy of G(Ud), its statistical diﬀerence
from the uniform distribution, or require pairwise indepen-
dence. All of these fail one of the two criteria. For example,
it is impossible for a deterministic function to increase
entropy from O(log n) to poly(n). And it is easy to construct
algorithms that fail when run using random bits that are
only guaranteed to be pairwise independent.

• Kolmogorov complexity: A string x “looks random” if it is
incompressible (cannot be generated by a Turing machine
with a description of length less than |x|). An appealing
aspect of this notion is that it makes sense of the randomness
in a ﬁxed string (rather than a distribution). Unfortunately,
it is not suitable for our purposes. Speciﬁcally, if the function
G is computable (which we certainly want) then all of its
outputs have Kolmogorov complexity d = O(log n) (just
hardwire the seed into the TM computing G), and hence are
very compressible.

• Computational indistinguishability: This is the measure we
will use. Intuitively, we say that a random variable X “looks
random” if no eﬃcient algorithm can distinguish X from a
truly uniform random variable. Another perspective comes
from the deﬁnition of statistical diﬀerence:

∆(X, Y ) = max

T

| Pr[X ∈ T ] − Pr[Y ∈ T ]|.



<!-- pdf-page: 217 -->
214 Pseudorandom Generators

With computational indistinguishability, we simply restrict
the max to be taken only over “eﬃcient” statistical tests T —
that is, T s for which membership can be eﬃciently tested.

7.1.1 Computational Indistinguishability

Deﬁnition 7.1 (computational
indistinguishability). Random
variables X and Y taking values in {0, 1}m are (t, ε) indistinguishable
if for every nonuniform algorithm T running in time at most t, we have

| Pr[T (X) = 1] − Pr[T (Y ) = 1]| ≤ε.

The left-hand side above is called also the advantage of T .

Recall that a nonuniform algorithm is an algorithm that may have
some nonuniform advice hardwired in. (See Deﬁnition 3.10.) If the
algorithm runs in time t we require that the advice string is of length at
most t. Typically, to make sense of complexity measures like running
time,
it is necessary to use asymptotic notions, because a Turing
machine can encode a huge lookup table for inputs of any bounded size
in its transition function. However, for nonuniform algorithms, we can
avoid doing so by using Boolean circuits as our nonuniform model of
computation. Similarly to Fact 3.11, every nonuniform Turing machine
algorithm running in time t(n) can be simulated by a sequence of
Boolean circuit Cn of size ˜O(t(n)) and conversely every sequence of
Boolean circuits of size s(n) can be simulated by a nonuniform Turing
machine running in time ˜O(s(n)). Thus, to make our notation cleaner,
from now on, by “nonuniform algorithm running in time t,” we mean
“Boolean circuit of size t,” where we measure the size by the number
of AND and OR gates in the circuit. (For convenience, we don’t
count the inputs and negations in the circuit size.) Note also that in
Deﬁnition 7.1 we have not speciﬁed whether the distinguisher is deter-
ministic or randomized; this is because a probabilistic distinguisher
achieving advantage greater than ε can be turned into a deterministic
distinguisher achieving advantage greater than ε by nonuniformly
ﬁxing the randomness. (This is another example of how “nonuniformity
is more powerful than randomness,” like in Corollary 3.12.)



<!-- pdf-page: 218 -->
7.1 Motivation and Deﬁnition

215

It is also of interest to study computational indistinguishability

and pseudorandomness against uniform algorithms.

Deﬁnition 7.2 (uniform computational
indistinguishability).
Let Xm, Ym be some sequences of random variables on {0, 1}m (or
{0, 1}poly(m)). For functions t : N → N and ε : N → [0, 1], we say that
{Xm} and {Ym} are (t(m), ε(m)) indistinguishable for uniform algo-
rithms if for all probabilistic algorithms T running in time t(m), we
have that

| Pr[T (Xm) = 1] − Pr[T (Ym) = 1]| ≤ε(m)

for all suﬃciently large m, where the probabilities are taken over Xm,
Ym and the random coin tosses of T .

We will focus on the nonuniform deﬁnition in this survey, but will

mention results about the uniform deﬁnition as well.

7.1.2 Pseudorandom Generators

Deﬁnition 7.3. A deterministic function G : {0, 1}d → {0, 1}m is a
(t, ε) pseudorandom generator (PRG) if

(1) d < m, and
(2) G(Ud) and Um are (t, ε) indistinguishable.

Also, note that we have formulated the deﬁnition with respect
to nonuniform computational indistinguishability, but an analogous
uniform deﬁnition can be given.

People attempted to construct pseudorandom generators long
before this deﬁnition was formulated. Their generators were tested
against a battery of statistical tests (e.g., the number of 1s and 0s are
approximately the same, the longest run is of length O(log m), etc.),
but these ﬁxed set of tests provided no guarantee that the generators
will perform well in an arbitrary application (e.g., in cryptography
or derandomization). Indeed, most classical constructions (e.g., linear



<!-- pdf-page: 219 -->
216 Pseudorandom Generators

congruential generators, as implemented in the standard C library)
are known to fail in some applications.

Intuitively, the above deﬁnition guarantees that the pseudorandom
bits produced by the generator are as good as truly random bits for all
eﬃcient purposes (where eﬃcient means time at most t). In particular,
we can use such a generator for derandomizing any algorithm of
running time at most t. For the derandomization to be eﬃcient, we
will also need the generator to be eﬃciently computable.

Deﬁnition 7.4. We say a sequence of generators {Gm : {0, 1}d(m) →
{0, 1}m} is computable in time t(m) if there is a uniform and deter-
ministic algorithm M such that for every m ∈ N and x ∈ {0, 1}d(m),
we have M (m, x) =G m(x) and M (m, x) runs in time at most t(m). In
addition, M (m) (with no second input) should output the value d(m)
in time at most t(m).

Note that even when we deﬁne the pseudorandomness property of
the generator with respect to nonuniform algorithms, the eﬃciency
requirement refers to uniform algorithms. As usual, for readability, we
will usually refer to a single generator G : {0, 1}d(m) → {0, 1}m, with it
being implicit that we are really discussing a family {Gm}.

Theorem 7.5. Suppose that for all m there exists an (m, 1/8)
pseudorandom generator G : {0, 1}d(m) → {0, 1}m computable in time
t(m). Then BPP ⊂

c DTIME(2d(nc) · (nc + t(nc))).

(cid:8)

Proof. Let A(x; r) be aBPP algorithm that on inputs x of length n,
can be simulated by Boolean circuits of size at most most nc, using coin
tosses r. Without loss of generality, we may assume that |r| = nc. (It will
often be notationally convenient to assume that the number of random
bits used by an algorithm equals its running time or circuit size, so as
to avoid an extra parameter. However, most interesting algorithms will
only actually read and compute with a smaller number of these bits, so
as to leave time available for computation. Thus, one should actually
think of an algorithm as only reading a preﬁx of its random string r.)



<!-- pdf-page: 220 -->
7.1 Motivation and Deﬁnition

217

The idea is to replace the random bits used by A with pseudoran-
dom bits generated by G, use the pseudorandomness property to show
that the algorithm will still be correct with high probability, and ﬁnally
enumerate over all possible seeds to obtain a deterministic algorithm.

Claim 7.6. For every x of
probability smaller than 1/2.

length n, A(x; G(Ud(nc))) errs with

Proof of Claim:
Suppose that there exists some x on which
A(x; G(Ud(nc))) errs with probability at least 1/2. Then T (·) =A(x, ·)
is a Boolean circuit of size at most nc that distinguishes G(Ud(nc))
from Unc with advantage at least 1/2 − 1/3 > 1/8. (Notice that we are
using the input x as nonuniform advice; this is why we need the PRG
to be pseudorandom against nonuniform tests.)

Now, enumerate over all seeds of length d(nc) and take a majority
vote. There are 2d(nc) of them, and for each we have to run both G
and A.

Notice that we can aﬀord for the generator G to have running time
t(m) = poly(m) or event(m) = poly( m) · 2O(d(m)) without aﬀecting
the time of the derandomization by than more than a polynomial
amount. In particular, for this application, it is OK if the generator
runs in more time than the tests it fools (which are time m in this
theorem). That is, for derandomization, it suﬃces to have G that is
mildly explicit according to the following deﬁnition:

Deﬁnition 7.7.

(1) A generator G : {0, 1}d(m) → {0, 1}m is mildly explicit if it is

computable in time poly(m, 2d(m)).

(2) A generator G : {0, 1}d(m) → {0, 1}m is fully explicit if it is

computable in time poly(m).

These deﬁnitions are analogous to the notions of mildly explicit
and fully explicit for expander graphs in Section 4.3. The truth table



<!-- pdf-page: 221 -->
218 Pseudorandom Generators

of a mildly explicit generator can be constructed in time polynomial in
its size (which is of size m · 2d(m)), whereas a fully explicit generator
can be evaluated in time polynomial in its input and output lengths
(like the neighbor function of a fully explicit expander).

Theorem 7.5 provides a tradeoﬀ between the seed length of the
PRG and the eﬃciency of the derandomization. Let’s look at some
typical settings of parameters to see how we might simulate BPP in
the diﬀerent deterministic time classes (see Deﬁnition 3.1):

#

(1) Suppose that for every constant ε >0, there is an ( m, 1/8)
mildly explicit PRG with seed length d(m) =m ε. Then
BPP ⊂
is
known that SUBEXP is a proper subset of EXP, this is
already a nontrivial improvement on the current inclusion
BPP ⊂ EXP (Proposition 3.2).

ε>0 DTIME(2nε

) def= SUBEXP.

Since

it

(2) Suppose

that

there

is
length

an (m, 1/8) mildly

explicit
d(m) = polylog(m). Then

seed

PRG with
BPP ⊂

(cid:8)

c DTIME(2logc m) def= ˜P.

(3) Suppose that there is an (m, 1/8) mildly explicit PRG with

seed length d(m) =O (log m). Then BPP = P.

Of course, all of these derandomizations are contingent on the
question of whether PRGs exist. As usual, our ﬁrst answer is yes but
the proof is not very helpful — it is nonconstructive and thus does not
provide for an eﬃciently computable PRG:

Proposition 7.8. For all m ∈ N and ε >0, there exists a (nonexplicit)
(m, ε) pseudorandom generator G : {0, 1}d → {0, 1}m with seed length
d = O(log m + log(1/ε)).

is

by

the

proof

Proof. The
probabilistic method. Choose
G : {0, 1}d → {0, 1}m at random. Now, ﬁx a time m algorithm, T .
The probability (over the choice of G) that T distinguishes G(Ud)
from Um with advantage ε is at most 2−Ω(2dε2), by a Chernoﬀ
bound. There are 2poly(m) nonuniform algorithms running in time m
(i.e., circuits of size m). Thus, union-bounding over all possible T ,



<!-- pdf-page: 222 -->
7.2 Cryptographic PRGs

219

we get that the probability that there exists a T breaking G
is at most 2poly(m)2−Ω(2dε2), which is less than 1 for d being
O(log m + log(1/ε)).

Note that putting together Proposition 7.8 and Theorem 7.5 gives
us another way to prove that BPP ⊂ P/poly (Corollary 3.12): just let
the advice string be the truth table of an (nc, 1/8) PRG (which can be
described by 2d(nc) · nc = poly(n) bits), and then use that PRG in the
proof of Theorem 7.5 to derandomize the BPP algorithm. However, if
you unfold both this proof and our previous proof (where we do error
reduction and then ﬁx the coin tosses), you will see that both proofs
amount to essentially the same “construction.”

7.2 Cryptographic PRGs

The theory of computational pseudorandomness discussed in this sec-
tion emerged from cryptography, where researchers sought a deﬁni-
tion that would ensure that using pseudorandom bits instead of truly
random bits (e.g., when encrypting a message) would retain security
against all computationally feasible attacks. In this setting, the gener-
ator G is used by the honest parties and thus should be very eﬃcient
to compute. On the other hand, the distinguisher T corresponds to an
attack carried about by an adversary, and we want to protect against
adversaries that may invest a lot of computational resources into trying
to break the system. Thus, one is led to require that the pseudorandom
generators be secure even against distinguishers with greater running
time than the generator. The most common setting of parameters in the
theoretical literature is that the generator should run in a ﬁxed polyno-
mial time, but the adversary can run in an arbitrary polynomial time.

Deﬁnition 7.9. A generator Gm : {0, 1}d(m) → {0, 1}m is a crypto-
graphic pseudorandom generator if:

(1) Gm is fully explicit. That is, there is a constant b such that

Gm is computable in time mb.



<!-- pdf-page: 223 -->
220 Pseudorandom Generators

(2) Gm is an (mω(1), 1/mω(1)) PRG. That is, for every constant
c, Gm is an (mc, 1/mc) pseudorandom generator for all
suﬃciently large m.

Due to space constraints and the fact that such generators are
covered in other texts (see the Chapter Notes and References), we will
not do an in-depth study of cryptographic generators, but just survey
what is known about them.

The ﬁrst question to ask is whether such generators exist at all.
It is not hard to show that cryptographic pseudorandom generators
cannot exist unless P (cid:1)= NP,
indeed unless NP (cid:1)⊂ P/poly. (See
Problem 7.3.) Thus, we do not expect to establish the existence of such
generators unconditionally, and instead need to make some complexity
assumption. While it would be wonderful to show that NP (cid:1)⊂ P/poly
implies the existence of cryptographic pseudorandom generators, that
too seems out of reach. However, we can base them on the very
plausible assumption that there are functions that are easy to evaluate
but hard to invert.

Deﬁnition 7.10. fn : {0, 1}n → {0, 1}n is a one-way function if:

(1) There is a constant b such that fn is computable in time nb

for suﬃciently large n.

(2) For every constant c and every nonuniform algorithm A

running in time nc:

Pr[A(fn(Un)) ∈ f −1

n (fn(Un))] ≤ 1
nc

for all suﬃciently large n.

Assuming the existence of one-way functions seems stronger than
the assumption NP (cid:1)⊂ P/poly. For example,
it is an average-case
complexity assumption, as it requires that f is hard to invert when
evaluated on random inputs. Nevertheless, there are a number of
candidate functions believed to be one-way. The simplest is integer
multiplication: fn(x, y) =x · y, where x and y are n/2-bit numbers.



<!-- pdf-page: 224 -->
7.2 Cryptographic PRGs

221

Inverting this function amounts to the integer factorization problem,
for which no eﬃcient algorithm is known.

A classic and celebrated result in the foundations of cryptography
is that cryptographic pseudorandom generators can be constructed
from any one-way function:

Theorem 7.11. The following are equivalent:

(1) One-way functions exist.
(2) There exist cryptographic pseudorandom generators with

seed length d(m) =m − 1.

(3) For every constant ε >0, there exist cryptographic pseudo-

random generators with seed length d(m) =m ε.

Corollary 7.12. If one-way functions exist, then BPP ⊂ SUBEXP.

What about getting a better derandomization? The proof of the
above theorem is more general quantitatively. It takes any one-way
function f(cid:4) : {0, 1}(cid:4) → {0, 1}(cid:4) and a parameter m, and constructs a gen-
erator Gm : {0, 1}poly((cid:4)) → {0, 1}m. The fact that Gm is pseudorandom
is proven by a reduction as follows. Assuming for contradiction that we
have an algorithm T that runs in time t and distinguishes Gm from uni-
form with advantage ε, we construct an algorithm T (cid:3) running in time
t(cid:3) = t · (m/ε)O(1) inverting f(cid:4) (say with probability 1/2). If t(cid:3) ≤ poly((cid:6)),
then this contradicts the one-wayness of f , and hence we conclude
that T cannot exist and Gm is a (t, ε) pseudorandom generator.

Quantitatively, if f(cid:4) is hard to invert by algorithms running in time
s((cid:6)) and we take m = 1/ε = s((cid:6))o(1), then we have t(cid:3) ≤ s((cid:6)) for every
t = poly(m) and suﬃciently large (cid:6). Thus, viewing the seed length d
of Gm as a function of m, we have d(m) = poly((cid:6)) = poly(s−1(mω(1))),
where mω(1) denotes any superpolynomial function of m.

Thus:

• If s((cid:6)) =(cid:6) ω(1), we can get seed length d(m) =m ε for any
desired constant ε >0 and BPP ⊂ SUBEXP (as discussed
above).



<!-- pdf-page: 225 -->
222 Pseudorandom Generators

• If s((cid:6)) = 2(cid:4)Ω(1)

(as is plausible for the factoring one-way
function), then we get seed length d(m) = poly(log m) and
BPP ⊂ ˜P.

But we cannot get seed length d(m) =O (log m), as needed for con-
cluding BPP = P, from this result. Even for the maximum possible
hardness s((cid:6)) = 2Ω((cid:4)), we get d(m) = poly(log m). In fact, Problem 7.3
shows that it is impossible to have a cryptographic PRG with seed
length O(log m) meeting Deﬁnition 7.9, where we require that Gm
be pseudorandom against all poly(m)-time algorithms. However, for
derandomization we only need Gm to be pseudorandom against a ﬁxed
poly-time algorithm, e.g., running in time t = m, and we would get such
generators with seed length O(log m) if the aforementioned construction
could be improved to yield seed length d = O((cid:6)) instead of d = poly((cid:6)).

Open Problem 7.13. Given a one-way function f : {0, 1}(cid:4) → {0, 1}(cid:4)
that is hard to invert by algorithms running in time s = s((cid:6)) and a
constant c, it is possible to construct a fully explicit (t, ε) pseudoran-
dom generator G : {0, 1}d → {0, 1}m with seed length d = O((cid:6)) and
pseudorandomness against time t = s · (ε/m)O(1)?

The best

known seed length for

is
d = ˜O((cid:6)3 · log(m/ε)/ log2 s), which is ˜O((cid:6)2) for the case that s = 2Ω((cid:4))
and m = 2Ω((cid:4)) as discussed above.

generator

such a

The above open problem has long been solved in the positive
for one-way permutations f : {0, 1}(cid:4) → {0, 1}(cid:4). In fact, the construc-
tion of pseudorandom generators from one-way permutations has a
particularly simple description:

Gm(x, r) = ((cid:19)x, r(cid:20), (cid:19)f (x), r(cid:20), (cid:19)f (f (x)), r(cid:20), . . . , (cid:19)f (m−1)(x), r(cid:20)),
where |r| = |x| = (cid:6) and (cid:19)·, ·(cid:20) denotes inner product modulo 2. One
intuition for this construction is the following. Consider the sequence
(f (m−1)(U(cid:4)), f (m−2)(U(cid:4)), . . . , f (U(cid:4)), U(cid:4)). By the fact that f is hard to
invert (but easy to evaluate) it can be argued that the i + 1’st compo-
nent of this sequence is infeasible to predict from the ﬁrst i components
except with negligible probability. Thus, it is a computational analogue



<!-- pdf-page: 226 -->
7.2 Cryptographic PRGs

223

of a block source. The pseudorandom generator then is obtained by
a computational analogue of block-source extraction, using the strong
extractor Ext(x, r) =(cid:19)x, r (cid:20). The fact that the extraction works in this
computational setting, however, is much more delicate and complex
to prove than in the setting of extractors, and relies on a “local
list-decoding algorithm” for the corresponding code (namely the
Hadamard code). See Problems 7.12 and 7.13. (We will discuss local
list decoding in Section 7.6.)

Pseudorandom Functions.
It turns out that a cryptographic pseu-
dorandom generator can be used to build an even more powerful
object — a family of pseudorandom functions. This is a family of func-
tions {fs : {0, 1}d → {0, 1}}
s∈{0,1}d such that (a) given the seed s, the
function fs can be evaluated in polynomial time, but (b) without the
seed, it is infeasible to distinguish an oracle for fs from an oracle to a
truly random function. Thus in some sense, the d-bit truly random seed
s is stretched to 2d pseudorandom bits (namely the truth table of fs)!
Pseudorandom functions have applications in several domains:

• Cryptography: When two parties share a seed s to a PRF,
they eﬀectively share a random function f : {0, 1}d → {0, 1}.
(By deﬁnition, the function they share is indistinguishable
from random by any poly-time third party.) Thus, in order
for one party to send a message m encrypted to the other,
they can simply choose a random r R← {0, 1}d, and send
(r, fs(r) ⊕ m). With knowledge of s, decryption is easy;
simply calculate fs(r) and XOR it to the second part of the
received message. However, the value fs(r) ⊕ m would look
essentially random to anyone without knowledge of s.
This is just one example; pseudorandom functions have vast
applicability in cryptography.

• Learning Theory: Here, PRFs are used mainly to prove neg-
ative results. The basic paradigm in computational learning
theory is that we are given a list of examples of a function’s
behavior, (x1, f (x2)), (x2, f (x2)), . . . , (xk, f (xk))), where the
xis are being selected randomly from some underlying
distribution, and we would like to predict what the func-



<!-- pdf-page: 227 -->
224 Pseudorandom Generators

tion’s value will be on a new data point xk+1 coming from
the same distribution.
Information-theoretically, correct
prediction is possible after a small number of samples (with
high probability), assuming that the function has a small
description (e.g.,
is computable by a poly-sized circuit).
However, it is computationally hard to predict the output
of a PRF fs on a new point xk+1 after seeing its value on
k points (and this holds even if the algorithm gets to make
“membership queries” — choose the evaluation points on
its own, in addition to getting random examples from some
underlying distribution). Thus, PRFs provide examples of
functions that are eﬃciently computable yet hard to learn.
• Hardness of Proving Circuit Lower Bounds: One main
approach to proving P (cid:1)= NP is
some
f ∈ NP doesn’t have polynomial size circuits (equivalently,
NP (cid:1)⊂ P/poly). This approach has had very limited suc-
cess — the only superpolynomial lower bounds that have
been achieved have been using very restricted classes of
circuits (monotone circuits, constant depth circuits, etc).
For general circuits, the best lower bound that has been
achieved for a problem in NP is 5n − O(n).
Pseudorandom functions have been used to help explain
why existing lower-bound techniques have so far not yielded
it has
superpolynomial circuit lower bounds. Speciﬁcally,
been shown that any suﬃciently “constructive” proof of
superpolynomial circuit lower bounds (one that would allow
us to certify that a randomly chosen function has no small cir-
cuits) could be used to distinguish a pseudorandom function
from truly random in subexponential time and thus invert
any one-way function in subexponential time. This is known
as the “Natural Proofs” barrier to circuit lower bounds.

to show that

7.3 Hybrid Arguments

In this section, we introduce a very useful proof method for working
with computational indistinguishability, known as the hybrid argument.



<!-- pdf-page: 228 -->
7.3 Hybrid Arguments

225

We use it to establish two important facts — that computational
indistinguishability is preserved under taking multiple samples, and
that pseudorandomness is equivalent to next-bit unpredictability.

7.3.1

Indistinguishability of Multiple Samples

indistin-
The following proposition illustrates that computational
guishability behaves like statistical diﬀerence when taking many
independent repetitions; the distance ε multiplies by at most the num-
ber of copies (cf. Lemma 6.3, Part 6). Proving it will introduce useful
techniques for reasoning about computational indistinguishability, and
will also illustrate how working with such computational notions can
be more subtle than working with statistical notions.

Proposition 7.14. If random variables X and Y are (t, ε) indistin-
guishable, then for every k ∈ N, X k and Y k are (t, kε) indistinguishable
(where X k represents k independent copies of X).

Note that when t = ∞, this follows from Lemma 6.3, Part 6; the
challenge here is to show that the same holds even when we restrict to
computationally bounded distinguishers.

Proof. We will prove the contrapositive:
if there is an eﬃcient
algorithm T distinguishing X k and Y k with advantage greater than
kε, then there is an eﬃcient algorithm T (cid:3) distinguishing X and Y
with advantage greater than ε. The diﬀerence in this proof from the
corresponding result about statistical diﬀerence is that we need to
preserve eﬃciency when going from T to T (cid:3). The algorithm T (cid:3) will
naturally use the algorithm T as a subroutine. Thus this is a reduction
in the same spirit as reductions used elsewhere in complexity theory
(e.g., in the theory of NP-completeness).

Suppose that there exists a nonuniform time t algorithm T such that

| Pr[T (X k) = 1] − Pr[T (Y k) = 1]| > kε.

(7.1)

We can drop the absolute value in the above expression without
loss of generality. (Otherwise we can replace T with its negation; recall
that negations are free in our measure of circuit size.)



<!-- pdf-page: 229 -->
226 Pseudorandom Generators

Now we will use a “hybrid argument.” Consider the hybrid
distributions Hi = X k−iY i, for i = 0, . . . , k. Note that H0 = X k and
Hk = Y k. Then Inequality (7.1) is equivalent to

k(cid:3)

i=1

Pr[T (Hi−1) = 1] − Pr[T (Hi) = 1] > kε,

since the sum telescopes. Thus, there must exist some i ∈ [k] such that
Pr[T (Hi−1) = 1] − Pr[T (Hi) = 1] > ε, i.e.,

Pr[T (X k−iXY i−1) = 1] − Pr[T (X k−iY Y i−1) = 1] > ε.

By averaging, there exists some x1, . . . xk−i and yk−i+2, . . . yk such

that

Pr[T (x1, . . . xk−i, X, yk−i+2, . . . yk) = 1]

− Pr[T (x1, . . . xk−i, Y, yk−i+2, . . . yk) = 1] > ε.
Then, deﬁne T (cid:3)(z) =T (x1, . . . xk−i, z, yk−i+2, . . . , yk). Note that T (cid:3)
is a nonuniform algorithm with advice i, x1, . . . , xk−i, yk−i+2, . . . yk
hardwired in. Hardwiring these inputs costs nothing in terms of circuit
size. Thus T (cid:3) is a nonuniform time t algorithm such that

Pr[T (cid:3)(X) = 1] − Pr[T (cid:3)(Y ) = 1] > ε,

contradicting the indistinguishability of X and Y .

While the parameters in the above result behave nicely, with (t, ε)
going to (t, kε), there are some implicit costs. First, the amount of
nonuniform advice used by T (cid:3) is larger than that used by T . This is
hidden by the fact that we are using the same measure t (namely circuit
size) to bound both the time and the advice length. Second, the result is
meaningless for large values of k (e.g., k = t), because a time t algorithm
cannot read more than t bits of the input distributions X k and Y k.

We note that there is an analogue of the above result for computa-
tional indistinguishability against uniform algorithms (Deﬁnition 7.2),
but it is more delicate, because we cannot simply hardwire i,
x1, . . . , xk−i, yk−i+2, . . . , yk as advice. Indeed, a direct analogue of
the proposition as stated is known to be false. We need to add the



<!-- pdf-page: 230 -->
7.3 Hybrid Arguments

227

additional condition that the distributions X and Y are eﬃciently
samplable. Then T (cid:3) can choose i R← [k] at random, and randomly
sample x1, . . . , xk−i

R← X, yk−i+2, . . . , yk

R← Y .

7.3.2 Next-Bit Unpredictability

In analyzing the pseudorandom generators that we construct, it will
be useful to work with a reformulation of the pseudorandomness
property, which says that given a preﬁx of the output, it should be
hard to predict the next bit much better than random guessing.

For notational convenience, we deviate from our usual conventions
and write Xi to denote the ith bit of random variable X, rather than
the ith random variable in some ensemble. We have:

Deﬁnition 7.15. Let X be a random variable distributed on {0, 1}m.
For t ∈ N and ε ∈ [0, 1], we say that X is (t, ε) next-bit unpredictable if
for every nonuniform probabilistic algorithm P running in time t and
every i ∈ [m], we have:

Pr[P (X1X2 · · · Xi−1) =X i] ≤ 1
2

+ ε,

where the probability is taken over X and the coin tosses of P .

Note that the uniform distribution X ≡ Um is (t, 0) next-bit
unpredictable for every t. Intuitively, if X is pseudorandom, it must
be next-bit unpredictable, as this is just one speciﬁc kind of test one
can perform on X. In fact the converse also holds, and that will be
the direction we use.

Proposition 7.16. Let X be a random variable taking values in
{0, 1}m. If X is a (t, ε) pseudorandom, then X is (t − O(1), ε) next-bit
unpredictable. Conversely, if X is (t, ε) next-bit unpredictable, then it
is (t, m · ε) pseudorandom.

Proof. Here U denotes an r.v. uniformly distributed on {0, 1}m and
Ui denotes the ith bit of U .



<!-- pdf-page: 231 -->
228 Pseudorandom Generators

pseudorandom ⇒ next-bit unpredictable. The proof
is by
reduction. Suppose for contradiction that X is not (t − 3, ε) next-bit
unpredictable, so we have a predictor P : {0, 1}i−1 → {0, 1} that
succeeds with probability at least 1/2 +ε. We construct an algorithm
T : {0, 1}m → {0, 1} that distinguishes X from Um as follows:
$

T (x1x2 · · · xm) =

1

0

if P (x1x2 · · · xi−1) =x i
otherwise.

T can be implemented with the same number of ∧ and ∨ gates as P ,
plus 3 for testing equality (via the formula (x ∧ y) ∨ (¬x ∧ ¬y)).

next-bit unpredictable ⇒ pseudorandom. Also by reduction.
Suppose X is not pseudorandom, so we have a nonuniform algorithm
T running in time t s.t.

Pr[T (X) = 1] − Pr[T (U ) = 1] > ε,

where we have dropped the absolute values without loss of generality
as in the proof of Proposition 7.14.

We

hybrid
X1X2 · · · XiUi+1Ui+2 · · · Um. Then Hm = X and H0 = U . We have:

argument.

Deﬁne

now

use

a

Hi =

m(cid:3)

i=1

(Pr[T (Hi) = 1] − Pr[T (Hi−1) = 1]) > ε,

since the sum telescopes. Thus, there must exist an i such that

Pr[T (Hi) = 1] − Pr[T (Hi−1) = 1] > ε/m.

This says that T is more likely to output 1 when we put Xi in the
ith bit than when we put a random bit Ui. We can view Ui as being
Xi with probability 1/2 and being Xi with probability 1/2. The only
advantage T has must be coming from the latter case, because in the
former case, the two distributions are identical. Formally,

ε/m < Pr[T (Hi) = 1] − Pr[T (Hi−1) = 1]

= Pr[T (X1 · · · Xi−1XiUi+1 · · · Um) = 1]



<!-- pdf-page: 232 -->
7.3 Hybrid Arguments

229

· Pr[T (X1 · · · Xi−1XiUi+1 · · · Um) = 1]
(cid:15)

· Pr[T (X1 · · · Xi−1XiUi+1 · · · Um) = 1]

(cid:14)

−

1
2

+

1
2

=

1
· (Pr[T (X1 · · · Xi−1XiUi+1 · · · Um) = 1]
2
− Pr[T (X1 · · · Xi−1XiUi+1 · · · Um) = 1]).

This motivates the following next-bit predictor: P (x1x2 · · · xi−1):

(1) Choose random bits ui, . . . , um
(2) Compute b = T (x1 · · · xi−1ui · · · um).
(3) If b = 1, output ui, otherwise output ui.

R← {0, 1}.

The intuition is that T is more likely to output 1 when ui = xi than
when ui = xi. Formally, we have:

Pr[P (X1 · · · Xi−1) =X i]

=

=

>

· (Pr[T (X1 · · · Xi−1UiUi+1 · · · Um) = 1|Ui = Xi]

1
2
+ Pr[T (X1 · · · Xi−1UiUi+1 · · · Um) = 0|Ui (cid:1)= Xi])
1
· (Pr[T (X1 · · · Xi−1XiUi+1 · · · Um) = 1]
2
+ 1 − Pr[T (X1 · · · Xi−1XiUi+1 · · · Um) = 1])
1
2

ε
m

+

.

Note that as described P runs in time t + O(m). Recalling that we are
using circuit size as our measure of nonuniform time, we can reduce the
running time to t as follows. First, we may nonuniformly ﬁx the coin
tosses ui, . . . , um of P while preserving its advantage. Then all P does
is run T on x1 · · · xi−1 concatenated with some ﬁxed bits and and either
output what T does or its negation (depending on the ﬁxed value of ui).
Fixing some input bits and negation can be done without increasing
circuit size. Thus we contradict the next-bit unpredictability of X.

We note that an analogue of this result holds for uniform distin-
guishers and predictors, provided that we change the deﬁnition of



<!-- pdf-page: 233 -->
230 Pseudorandom Generators

next-bit predictor to involve a random choice of i R← [m] instead of
a ﬁxed value of i, and change the time bounds in the conclusions to
be t − O(m) rather than t − O(1) and t. (We can’t do tricks like in
the ﬁnal paragraph of the proof.) In contrast to the multiple-sample
indistinguishability result of Proposition 7.14, this result does not
need X to be eﬃciently samplable for the uniform version.

7.4 Pseudorandom Generators from Average-Case Hardness

In Section 7.2, we surveyed cryptographic pseudorandom generators,
which have numerous applications within and outside cryptography,
including to derandomizing BPP. However, for derandomization, we
can use generators with weaker properties. Speciﬁcally, Theorem 7.5
only requires G : {0, 1}d(m) → {0, 1}m such that:

(1) G fools (nonuniform) distinguishers running in time m (as

opposed to all poly(m)-time distinguishers).

(2) G is computable in time poly(m, 2d(m)) (i.e., G is mildly
explicit). In particular, the PRG may take more time than
the distinguishers it is trying to fool.

Such a generator implies that every BPP algorithm can be deran-
domized in time poly(n) · 2d(poly(n)).

The beneﬁt of studying such generators is that we can hope to con-
struct them under weaker assumptions than used for cryptographic gen-
erators. In particular, a generator with the properties above no longer
seems to imply P (cid:1)= NP, much less the existence of one-way functions.
(The nondeterministic distinguisher that tests whether a string is
an output of the generator by guessing a seed needs to evaluate the
generator, which takes more time than the distinguishers are allowed.)
imply
nonuniform circuit lower bounds for exponential time, something that
is beyond the state of the art in complexity theory.

However, as shown in Problem 7.1, such generators still

Our goal in the rest of this section is to construct generators as
above from assumptions that are as weak as possible. In this section, we
will construct them from boolean functions computable in exponential
time that are hard on average (for nonuniform algorithms), and in the
section after we will relax this to only require worst-case hardness.



<!-- pdf-page: 234 -->
7.4 Pseudorandom Generators from Average-Case Hardness

231

7.4.1 Average-Case Hardness

A function is hard on average if it is hard to compute correctly on
randomly chosen inputs. Formally:

Deﬁnition 7.17. For s ∈ N and δ ∈ [0, 1], we say that a Boolean func-
tion f : {0, 1}(cid:4) → {0, 1} is (s, δ) average-case hard if for all nonuniform
probabilistic algorithms A running in time s,

Pr[A(X) =f (X)] ≤ 1 − δ,

where the probability is taken over X and the coin tosses of A.

Note that saying that f is (s, δ) hard for some δ > 0 (possibly
exponentially small) amounts to saying that f is worst-case hard.1
Thus, we think of average-case hardness as corresponding to values
of δ that are noticeably larger than zero, e.g., δ = 1/s.1 or δ = 1/3.
Indeed, in this section we will take δ = 1/2 − ε for ε = 1/s. That is, no
eﬃcient algorithm can compute f much better than random guessing.
A typical setting of parameters we use is s = s((cid:6)) somewhere in range
from (cid:6)ω(1) (slightly superpolynomial) to s((cid:6)) = 2α(cid:4)
for a constant
α > 0. (Note that every function is computable by a nonuniform
algorithm running in time roughly 2(cid:4), so we cannot take s((cid:6)) to be
any larger.) We will also require f to be computable in (uniform) time
2O((cid:4)) so that our pseudorandom generator will be computable in time
exponential in its seed length. The existence of such an average-case
hard function may seem like a strong assumption, but in later sections
we will see how to deduce it from a worst-case hardness assumption.

Now we show how to obtain a pseudorandom generator from

average-case hardness.

Proposition 7.18. If f : {0, 1}(cid:4) → {0, 1} is (t, 1/2 − ε) average-case
hard, then G(x) =x ◦ f (x) is a (t, ε) pseudorandom generator.

1 For probabilistic algorithms, the “right” deﬁnition of worst-case hardness is actually that
there exists an input x for which Pr[A(x) = f (x)] < 2/3, where the probability is taken
over the coin tosses of A. But for nonuniform algorithms two deﬁnitions can be shown to
be roughly equivalent. See Deﬁnition 7.34 and the subsequent discussion.



<!-- pdf-page: 235 -->
232 Pseudorandom Generators

We omit the proof of this proposition, but it follows from Prob-
lem 7.5, Part 2 (by setting m = 1, a = 0, and d = (cid:6) in Theorem 7.24).
Note that this generator includes its seed in its output. This is
impossible for cryptographic pseudorandom generators, but is feasible
(as shown above) when the generator can have more resources than
the distinguishers it is trying to fool.

Of course, this generator is quite weak, stretching by only one bit.

We would like to get many bits out. Here are two attempts:

• Use concatenation: Deﬁne G(x1 · · · xk) =x 1 · · · xkf (x1) · · ·
f (xk). This is a (t, kε) pseudorandom generator because
G(Uk(cid:4)) consists of k independent samples of a pseudorandom
distribution and thus computational indistinguishability is
preserved by Proposition 7.14. Note that already here we
are relying on nonuniform indistinguishability, because the
distribution (U(cid:4), f (U(cid:4))) is not necessarily samplable (in time
that is feasible for the distinguishers). Unfortunately, how-
ever, this construction does not improve the ratio between
output length and seed length, which remains very close to 1.
• Use
two
to
seed length by deﬁning
bits
same
G(cid:3)(x) =G(G(x )1···(cid:4))G(x)(cid:4)+1,
where G(x)1···(cid:4)
denotes
the ﬁrst (cid:6) bits of G(x). This works for cryptographic
pseudorandom generators, but not for the generators we are
considering here. Indeed, for the generator G(x) =xf (x) of
Proposition 7.18, we would get G(cid:3)(x) =xf (x)f (x), which is
clearly not pseudorandom.

composition: For
out using

example,

the

get

try

7.4.2 The Pseudorandom Generator

Our goal now is to show the following:

Theorem 7.19. For s : N → N, suppose that there is a function
f ∈ E = DTIME(2O((cid:4)))2 such that for every input length (cid:6) ∈ N, f

2 E should be contrasted with the larger class EXP = DTIME(2poly((cid:2))). See Problem 7.2.



<!-- pdf-page: 236 -->
7.4 Pseudorandom Generators from Average-Case Hardness

233

is (s((cid:6)), 1/2 − 1/s((cid:6))) average-case hard, where s((cid:6)) is computable in
time 2O((cid:4)). Then for every m ∈ N, there is a mildly explicit (m, 1/m)
pseudorandom generator G : {0, 1}d(m) → {0, 1}m with seed length
d(m) =O (s−1(poly(m))2/ log m) that is computable in time 2O(d(m)).

is

to

the

this

that

seed

Note

similar

length d(m) =
poly(s−1(poly(m))) mentioned in Section 7.2 for
constructing
cryptographic pseudorandom generators from one-way functions, but
the average-case assumption is incomparable (and will be weakened
further in the next section). In fact, it is known how to achieve a seed
length d(m) =O (s−1(poly(m))), which matches what is known for
constructing pseudorandom generators from one-way permutations as
well as the converse implication of Problem 7.1. We will not cover that
improvement here (see the Chapter Notes and References for pointers),
but note that for the important case of hardness s((cid:6)) = 2Ω((cid:4)), Theo-
rem 7.19 achieves seed length d(m) =O (O(log m)2/ log m) =O (log m)
and thus P = BPP. More generally, we have:

Corollary 7.20. Suppose that E has a (s((cid:6)), 1/2 − 1/s((cid:6))) average-
case hard function f : {0, 1}(cid:4) → {0, 1}.

(1) If s((cid:6)) = 2Ω((cid:4)), then BPP = P.
(2) If s((cid:6)) = 2(cid:4)Ω(1)
, then BPP ⊂ ˜P.
(3) If s((cid:6)) =(cid:6) ω(1), then BPP ⊂ SUBEXP.

The idea is to apply f repeatedly, but on slightly dependent inputs,
namely ones that share very few bits. The sets of seed bits used for
each output bit will be given by a design:

Deﬁnition 7.21. S1, . . . , Sm ⊂ [d] is an ((cid:6), a)-design if

(1) ∀ i, |Si| = (cid:6)
(2) ∀ i (cid:1)= j, |Si ∩ Sj| ≤a



<!-- pdf-page: 237 -->
234 Pseudorandom Generators

We want lots of sets having small

intersections over a small

universe. We will use the designs established by Problem 3.2:

Lemma 7.22. For every constant γ > 0 and every (cid:6), m ∈ N, there
exists an ((cid:6), a)-design S1, . . . , Sm ⊂ [d] with d = O( (cid:4)2
a ) and a = γ · log m.
Such a design can be constructed deterministically in time poly(m, d).

The important points are that intersection sizes are only logarith-
mic in the number of sets, and the universe size d is at most quadratic
in the set size (cid:6) (and can be linear in (cid:6) in case we take m = 2Ω((cid:4))).

Construction 7.23.
(Nisan–Wigderson Generator) Given a
function f : {0, 1}(cid:4) → {0, 1} and an ((cid:6), a)-design S1, . . . , Sm ⊂ [d], deﬁne
the Nisan–Wigderson generator G : {0, 1}d → {0, 1}m as

G(x) =f (x|S1)f (x|S2) · · · f (x|Sm)

where if x is a string in {0, 1}d and S ⊂ [d], then x|S is the string of
length |S| obtained from x by selecting the bits indexed by S.

Theorem 7.24. Let G : {0, 1}d → {0, 1}m be the Nisan–Wigderson
generator based on a function f : {0, 1}(cid:4) → {0, 1} and some ((cid:6), a)
design. If f is (s, 1/2 − ε/m) average-case hard, then G is a (t, ε)
pseudorandom generator, for t = s − m · a · 2a.

a = log m,

Theorem 7.19 follows from Theorem 7.24 by setting ε = 1/m
and
then
t = s((cid:6)) − m · a · 2a ≥ m, so we have an (m, 1/m) pseudorandom gen-
erator. The seed length is d = O((cid:6)2/ log m) =O (s−1(poly(m))2/ log m).

(cid:6) = s−1(m3),

observing

that

and

for

Proof. Suppose G is not a (t, ε) pseudorandom generator. By Proposi-
tion 7.16, there is a nonuniform time t next-bit predictor P such that

Pr[P (f (X|S1)f (X|S2) · · · f (X|Si−1)) = f (X|Si)] >

1
2

+

ε
m

,

(7.2)

for some i ∈ [m]. From P , we construct A that computes f with
probability greater than 1/2 +ε/m.



<!-- pdf-page: 238 -->
7.4 Pseudorandom Generators from Average-Case Hardness

235

Let Y = X|Si. By averaging, we can ﬁx all bits of X|
Si = z (where
Si
is the complement of S) such that the prediction probability
remains greater than 1/2 +ε/m (over Y and the coin tosses of the
predictor P ). Deﬁne fj(y) =f (x|Sj ) for j ∈ {1, . . . , i − 1}. (That is,
fj(y) forms x by placing y in the positions in Si and z in the others,
and then applies f to x|Sj ). Then

[P (f1(Y ) · · · fi−1(Y )) = f (Y )] >

Pr
Y

1
2

+

ε
m

.

Note that fj(y) depends on only |Si ∩ Sj| ≤a bits of y. Thus, we
can compute each fj with a look-up table, which we can include in the
advice to our nonuniform algorithm. Indeed, every function on a bits
can be computed by a boolean circuit of size at most a · 2a. (In fact,
size at most O(2a/a) suﬃces.)

Then, deﬁning A(y) =P (f1(y) · · · fi−1(y)), we deduce that A(y) can
be computed with error probability smaller than 1/2 − ε/m in nonuni-
form time less than t + m · a · 2a = s. This contradicts the hardness
of f . Thus, we conclude G is an (m, ε) pseudorandom generator.

Some additional remarks on this proof:

(1) This is a very general construction that works for any
average-case hard function f . We only used f ∈ E to deduce
G is computable in E.

(2) The reduction works for any nonuniform class of algorithms
logarithmically many bits can be

C where functions of
computed eﬃciently.

Indeed, in the next section we will use the same construction to
obtain an unconditional pseudorandom generator fooling constant-
depth circuits, and will later exploit the above “black-box” properties
even further.

As mentioned earlier, the parameters of Theorem 7.24 have been
improved in subsequent work, but the newer constructions do not have
the clean structure of Nisan–Wigderson generator, where the seed of
the generator is used to generate m random but correlated evaluation
points, on which the average-case hard function f is evaluated. Indeed,



<!-- pdf-page: 239 -->
236 Pseudorandom Generators

each output bit of the improved generators depends on the entire
truth-table of the function f , translating to a construction of signiﬁ-
cantly higher computational complexity. Thus the following remains an
interesting open problem (which would have signiﬁcance for hardness
ampliﬁcation as well as constructing pseudorandom generators):

Open Problem 7.25. For every (cid:6), s ∈ N, construct an explicit
generator H : {0, 1}O((cid:4)) → ({0, 1}(cid:4))m with m = sΩ(1) such that if f
is (s, 1/2 − 1/s) average-case hard and we deﬁne G(x) =f (H1(x))
f (H2(x)) · · · f (Hm(x)) where Hi(x), denotes the ith component of
H(x), then G is an (m, 1/m) pseudorandom generator.

7.4.3 Derandomizing Constant-depth circuits

Deﬁnition 7.26. An unbounded fan-in circuit C(x1, . . . , xn) has input
gates consisting of variables xi, their negations ¬xi, and the constants
0 and 1, as well as computation gates, which can compute the AND
or OR of an unbounded number of other gates (rather than just 2, as
in usual Boolean circuits).3 The size of such a circuit is the number of
computation gates, and the depth is the maximum of length of a path
from an input gate to the output gate.

AC0 is the class of functions f : {0, 1}∗ → {0, 1} for which there
exist constants c and k and a uniformly constructible sequence
of unbounded fan-in circuits (Cn)n∈N such that for all n, Cn has
size at most nc and depth at most k, and for all x ∈ {0, 1}n,
Cn(x) =f (x). Uniform constructibility means that there is an eﬃcient
(e.g., polynomial-time) uniform algorithm M such that for all n,
M (1n) =C n (where 1n denotes the number n in unary, i.e., a string of
n 1s). BPAC0 deﬁned analogously, except that Cn may have poly(n)
extra inputs, which are interpreted as random bits, and we require
Prr[Cn(x, r) =f (x)] ≥ 2/3.

3 Note that it is unnecessary to allow internal NOT gates, as these can always be pushed
to the inputs via DeMorgan’s Laws at no increase in size or depth.



<!-- pdf-page: 240 -->
7.4 Pseudorandom Generators from Average-Case Hardness

237

AC0 is one of the richest circuit classes for which we have

superpolynomial lower bounds:

Theorem 7.27. For all constant k ∈ N and every (cid:6) ∈ N, the func-
tion Par(cid:4) : {0, 1}(cid:4) → {0, 1} deﬁned by PAR(cid:4)(x1, . . . , x(cid:4)) =
is
(sk((cid:6)), 1/2 − 1/sk((cid:6)))-average-case hard for nonuniform unbounded
fan-in circuits of depth k and size sk((cid:6)) = 2Ω((cid:4)1/k).

%
(cid:4)
i=1 xi

The proof of this result is beyond the scope of this survey; see the

Chapter Notes and References for pointers.

In addition to having an average-case hard function against
AC0, we also need that AC0 can compute arbitrary functions on a
logarithmic number of bits.

Lemma 7.28. Every function g : {0, 1}a → {0, 1} can be computed
by a depth 2 circuit of size 2a.

Using these two facts with the Nisan–Wigderson pseudoran-
dom generator construction, we obtain the following pseudorandom
generator for constant-depth circuits.

poly(m)-time

Theorem 7.29. For every constant k and every m, there exists
(m, 1/m)-pseudorandom generator
a
Gm : {0, 1}logO(k) m → {0, 1}m fooling unbounded fan-in circuits of
depth k (and size m).

computable

Proof. This is proven similarly to Theorems 7.19 and 7.24, except
that we take f = PAR(cid:4) rather than a hard function in E, and we
observe that the reduction can be implemented in a way that increases
the depth by only an additive constant. Speciﬁcally, to obtain a
pseudorandom generator fooling circuits of depth k and size m, we
use the hardness of PAR(cid:4) against unbounded fan-in circuits of depth
k(cid:3) = k + 2 and size m2, where (cid:6) = t−1
m). Then the
seed length of G is O((cid:6)2/a) < O((cid:6)2) = logO(k) m.

k(cid:2) (m2) =O (logk(cid:2)



<!-- pdf-page: 241 -->
238 Pseudorandom Generators

We now follow the steps of the proof of Theorem 7.19 to go from
an adversary T of depth k violating the pseudorandomness of G to a
circuit A of depth k(cid:3) calculating the parity function PAR(cid:4).

If T has depth k, then it can be veriﬁed that the next-bit predictor
P constructed in the proof of Proposition 7.16 also has depth k. (Recall
that negations and constants can be propagated to the inputs so they
do not contribute to the depth.) Next, in the proof of Theorem 7.24,
we obtain A from P by A(y) =P (f1(y)f2(y) · · · fi−1(y)) for some
i ∈ {1, . . . , m} and where each fi depends on at most a bits of y. Now
we observe that A can be computed by a small constant-depth circuit
(if P can). Speciﬁcally, applying Lemma 7.28 to each fi, the size of
A is at most (m − 1) · 2a + m = m2 and the depth of A is at most
k(cid:3) = k + 2. This contradicts the hardness of PAR(cid:4).

Corollary 7.30. BPAC0 ⊂ ˜P.

0

With more work, this can be strengthened to actually put BPAC0
in &AC
, i.e., uniform constant-depth circuits of quasipolynomial size.
(The diﬃculty is that we use majority voting in the derandomization,
but small constant-depth circuits cannot compute majority. However,
they can compute an “approximate” majority, and this suﬃces.)

The above pseudorandom generator can also be used to give
a quasipolynomial-time derandomization of the randomized algo-
rithm we saw for approximately counting the number of satisfying
assignments to a DNF formula (Theorem 2.34); see Problem 7.4.

Improving the running time of either of these derandomizations to

polynomial is an intriguing open problem.

Open Problem 7.31.
BPAC0 ⊂ P.

Show that BPAC0 = AC0

or

even

Open Problem 7.32 (Open Problem 2.36, restated). Give a
deterministic polynomial-time algorithm for approximately counting
the number of satisfying assignments to a DNF formula.



<!-- pdf-page: 242 -->
7.5 Worst-Case/Average-Case Reductions and Locally Decodable Codes

239

We remark that it has recently been shown how to give an average-
case AC0 simulation of BPAC0 (i.e., the derandomized algorithm is
correct on most inputs); see Problem 7.5.

Another open problem is to construct similar, unconditional
pseudorandom generators as Theorem 7.29 for circuit classes larger
than AC0. A natural candidate is AC0[2], which is the same as AC0
but augmented with unbounded-fan-in parity gates. There are known
explicit functions f : {0, 1}(cid:4) → {0, 1} (e.g., Majority) for which every
AC0[2] circuit of depth k computing f has size at least sk((cid:6)) = 2(cid:4)Ω(1/k)
,
but unfortunately the average-case hardness is much weaker than
we need. These functions are only (sk((cid:6)), 1/2 − 1/O((cid:6)))-average-case
hard, rather than (sk((cid:6)), 1/2 − 1/sk((cid:6)))-average-case hard, so we can
only obtain a small stretch using Theorem 7.24 and the following
remains open.

Open Problem 7.33. For every constant k and every m, construct a
(mildly) explicit (m, 1/4)-pseudorandom generator Gm : {0, 1}mo(1) →
{0, 1}m fooling AC0[2] circuits of depth k and size m.

7.5 Worst-Case/Average-Case Reductions and

Locally Decodable Codes

In the previous section, we saw how to construct pseudorandom
generators from boolean functions that are very hard on average,
where every nonuniform algorithm running in time t must err with
probability greater than 1/2 − 1/t on a random input. Now we want
to relax the assumption to refer to worst-case hardness, as captured
by the following deﬁnition.

Deﬁnition 7.34. A function f : {0, 1}(cid:4) → {0, 1} is worst-case hard
for time t if, for all nonuniform probabilistic algorithms A running in
time t, there exists x ∈ {0, 1}(cid:4) such that Pr[A(x) (cid:1)= f (x)] > 1/3, where
the probability is over the coin tosses of A.

Note that, for deterministic algorithms A, the deﬁnition simply says
∃x A(x) (cid:1)= f (x). In the nonuniform case, restricting to deterministic



<!-- pdf-page: 243 -->
240 Pseudorandom Generators

algorithms is without loss of generality because we can always deran-
domize the algorithm using (additional) nonuniformity. Speciﬁcally,
following the proof that BPP ⊂ P/poly, it can be shown that if f
is worst-case hard for nonuniform deterministic algorithms running
in time t, then it is worst-case hard for nonuniform probabilistic
algorithms running in time t(cid:3) for some t(cid:3) = Ω(t/(cid:6)).

A natural goal is to be able to construct an average-case hard func-
tion from a worst-case hard function. More formally, given a function
f : {0, 1}(cid:4) → {0, 1} that is worst-case hard for time t = t((cid:6)), construct a
function ˆf : {0, 1}O((cid:4)) → {0, 1} such that ˆf is average-case hard for time
t(cid:3) = tΩ(1). Moreover, we would like ˆf to be in E if f is in E. (Whether we
can obtain a similar result for NP is a major open problem, and indeed
there are negative results ruling out natural approaches to doing so.)

Our approach to doing this will be via error-correcting codes.
Speciﬁcally, we will show that if ˆf is the encoding of f in an appropri-
ate kind of error-correcting code, then worst-case hardness of f implies
average-case hardness of ˆf .

Speciﬁcally, we view f as a message of length L = 2(cid:4), and apply an
error-correcting code Enc : {0, 1}L → Σ ˆL to obtain ˆf = Enc(f ), which
we view as a function ˆf : {0, 1}ˆ(cid:4) → Σ, where ˆ(cid:6) = log ˆL. Pictorially:

message f : {0, 1}(cid:4) → {0, 1} −→ Enc −→ codeword ˆf : {0, 1}ˆ(cid:4) → Σ .

(Ultimately, we would like Σ = {0, 1}, but along the way we will
discuss larger alphabets.)

Now we argue the average-case hardness of ˆf as follows. Suppose,
for contradiction, that ˆf is not δ average-case hard. By deﬁnition,
there exists an eﬃcient algorithm A with Pr[A(x) = ˆf (x)] > 1 − δ.
We may assume that A is deterministic by ﬁxing its coins. Then A
may be viewed as a received word in Σ ˆL, and our condition on A
becomes dH (A, ˆf ) < δ. So if Dec is a δ-decoding algorithm for Enc,
then Dec(A) =f . By assumption A is eﬃcient, so if Dec is eﬃcient,
then f may be eﬃciently computed everywhere. This would contradict
our worst-case hardness assumption, assuming that Dec(A) gives a
time t((cid:6)) algorithm for f . However, the standard notion of decoding
requires reading all 2ˆ(cid:4) values of the received word A and writing all 2(cid:4)



<!-- pdf-page: 244 -->
7.5 Worst-Case/Average-Case Reductions and Locally Decodable Codes

241

values of the message Dec(A), and thus Time(Dec(A)) % 2(cid:4). But every
function on (cid:6) bits can be computed in nonuniform time 2(cid:4), and even
in the uniform case we are mostly interested in t((cid:6))   2(cid:4). To solve this
problem we introduce the notion of local decoding.

δ-decoding

algorithm for

Deﬁnition 7.35. A local
code
Enc : {0, 1}L → Σ ˆL is a probabilistic oracle algorithm Dec with
the following property. Let f : [L] → {0, 1} be any message with
associated codeword ˆf = Enc(f ), and let g : [ ˆL] → Σ be such that
dH (g, ˆf ) < δ. Then for all x ∈ [L] we have Pr[Decg(x) =f (x)] ≥ 2/3,
where the probability is taken over the coins ﬂips of Dec.

a

In other words, given oracle access to g, we want to eﬃciently
compute any desired bit of f with high probability. So both the input
(namely g) and the output (namely f ) are treated implicitly; the
decoding algorithm does not need to read/write either in its entirety.
Pictorially:

g

oracle access

x

Dec

f(x)

it possible

This makes

even
polylogarithmic-time) decoding. Also, we note that the bound of 2/3
in the deﬁnition can be ampliﬁed in the usual way. Having formalized a
notion of local decoding, we can now make our earlier intuition precise.

sublinear-time

to have

(or

Proposition 7.36. Let Enc be an error-correcting code with local
δ-decoding algorithm Dec that runs in nonuniform time at most tDec
(meaning that Dec is an boolean circuit of size at most tDec equipped
with oracle gates), and let f be worst-case hard for nonuniform time
t. Then ˆf = Enc(f ) is (t(cid:3), δ) average-case hard, where t(cid:3) = t/tDec.



<!-- pdf-page: 245 -->
242 Pseudorandom Generators

Proof. We do everything as explained before except with DecA in place
of Dec(A), and now the running time is at most Time(Dec) · Time(A).
(We substitute each oracle gate in the circuit for Dec with the circuit
for A.)

We note that the reduction in this proof does not use nonuniformity
in an essential way. We used nonuniformity to ﬁx the coin tosses of A,
making it deterministic. To obtain a version for hardness against uni-
form probabilistic algorithms, the coin tosses of A can be chosen and
ﬁxed randomly instead. With high probability, the ﬁxed coins will not
increase As error by more than a constant factor (by Markov’s Inequal-
ity); we can compensate for this by replacing the (t(cid:3), δ) average-case
hardness in the conclusion with, say, (t(cid:3), δ/3) average-case hardness.

In light of the above proposition, our task is now to ﬁnd an error-
correcting code Enc : {0, 1}L → Σ ˆL with a local decoding algorithm.
Speciﬁcally, we would like the following parameters.

(1) We want ˆ(cid:6) = O((cid:6)), or equivalently ˆL = poly(L). This is
because we measure hardness as a function of input length
(which in turn translates to the relationship between output
length and seed length of pseudorandom generators obtained
via Theorem 7.19). In particular, when t = 2Ω((cid:4)), we’d like
to achieve t(cid:3) = 2Ω(ˆ(cid:4)). Since t(cid:3) < t in Proposition 7.36, this is
only possible if ˆ(cid:6) = O((cid:6)).

(2) We would like Enc to be computable in time 2O(ˆ(cid:4)) = poly( ˆL),
which is poly(L) if we satisfy the requirement ˆL = poly(L).
This is because we want f ∈ E to imply ˆf ∈ E.

(3) We would like Σ = {0, 1} so that ˆf is a boolean function, and
δ = 1/2 − ε so that ˆf has suﬃcient average-case hardness for
the pseudorandom generator construction of Theorem 7.24.
(4) Since ˆf will be average-case hard against time t(cid:3) = t/tDec, we
would want the running time of Dec to be tDec = poly((cid:6), 1/ε)
so that we can take ε = tΩ(1) and still have t(cid:3) = tΩ(1)/poly((cid:6)).

Of course, achieving δ = 1/2 − ε is not possible with our current
local unique decoding (which is only harder than the
notion of
standard notion of unique decoding), and thus in the next section



<!-- pdf-page: 246 -->
7.5 Worst-Case/Average-Case Reductions and Locally Decodable Codes

243

we will focus on getting δ to be just a ﬁxed constant. In Section 7.6,
we will introduce a notion of local list decoding, which will enable
decoding from distance δ = 1/2 − ε.

In our constructions, it will be more natural to focus on the task
of decoding codeword symbols rather than message symbols. That is,
we replace the message f with the codeword ˆf in Deﬁnition 7.35 to
obtain the following notion:

Deﬁnition 7.37(Locally Correctible Codes).4 A local δ-correcting
algorithm for a codeC ⊂ Σ ˆL is a probabilistic oracle algorithm Dec with
the following property. Let ˆf ∈ C be any codeword, and let g : [ ˆL] → Σ
be such that dH (g, ˆf ) < δ. Then for all x ∈ [ ˆL] we have Pr[Decg(x) =
ˆf (x)] ≥ 2/3, where the probability is taken over the coin ﬂips of Dec.

This implies the standard deﬁnition of locally decodable codes
under the (mild) constraint that the message symbols are explicitly
included in the codeword, as captured by the following deﬁnition (see
also Problem 5.4).

Deﬁnition 7.38 (Systematic Encodings). An encoding algo-
rithm Enc : {0, 1}L → C for a codeC ⊂ Σ ˆL is systematic if there is
a polynomial-time computable function I : [L] → [ ˆL] such that for
all f ∈ {0, 1}L, ˆf = Enc(f ), and all x ∈ [L], we have ˆf (I(x)) = f (x),
where we interpret 0 and 1 as elements of Σ in some canonical way.

Informally, this means that the message f can be viewed as the

restriction of the codeword ˆf to the coordinates in the image of I.

Lemma 7.39. If Enc : {0, 1}L → C is systematic and C has a local δ-
correcting algorithm running in time t, then Enc has a local δ-decoding
algorithm (in the standard sense) running in time t + poly(log L).

Proof. If Dec1 is the local corrector for C and I the mapping in the
deﬁnition of systematic encoding, then Decg
1(I(x)) is a local
decoder for Enc.

2(x) = Decg

4 In the literature, these are often called self-correctible codes.



<!-- pdf-page: 247 -->
244 Pseudorandom Generators

7.5.1 Local Decoding Algorithms

Hadamard Code. Recall the Hadamard code of message length
m, which consists of the truth tables of all Z2-linear functions
c : {0, 1}m → {0, 1} (Construction 5.12).

Proposition 7.40. The Hadamard code C ⊂ {0, 1}2m
of message
length m has a local (1/4 − ε)-correcting algorithm running in time
poly(m, 1/ε).

Proof. We are given oracle access to g : {0, 1}m → {0, 1} that is at
distance less than 1/4 − ε from some (unknown) linear function c, and
we want to compute c(x) at an arbitrary point x ∈ {0, 1}m. The idea
is random self-reducibility: we can reduce computing c at an arbitrary
point to computing c at uniformly random points, where g is likely
to give the correct answer. Speciﬁcally, c(x) =c(x ⊕ r) ⊕ c(r) for
every r, and both x ⊕ r and r are uniformly distributed if we choose
r R← {0, 1}m. The probability that g diﬀers from c at either of these
points is less than 2 · (1/4 − ε) = 1/2 − 2ε. Thus g(x ⊕ r) ⊕ g(r) gives
the correct answer with probability noticeably larger than 1/2. We can
amplify this success probability by repetition. Speciﬁcally, we obtain
the following local corrector:

for Hadamard Code).
Algorithm 7.41 (Local Corrector
Input: An oracle g : {0, 1}m → {0, 1}, x ∈ {0, 1}m, and a parame-
ter ε >0

(1) Choose r1, . . . , rt
(2) Query g(ri) and g(ri ⊕ x) for each i = 1, . . . , t.
(3) Output maj1≤i≤t

{g(ri) ⊕ g(ri ⊕ x)}.

R← {0, 1}m, for t = O(1/ε2).

If dH (g, c) < 1/4 − ε, then this algorithm will output c(x) with

probability at least 2/3.

This local decoding algorithm is optimal in terms of its decoding
distance (arbitrarily close to 1/4) and running time (logarithmic in



<!-- pdf-page: 248 -->
7.5 Worst-Case/Average-Case Reductions and Locally Decodable Codes

245

the blocklength), but the problem is that the Hadamard code has
exponentially small rate.

Reed–Muller Code. Recall that the q-ary Reed–Muller code of
degree d and dimension m consists of all multivariate polynomials
→ Fq of total degree at most d. (Construction 5.16.) This code
p : Fm
q
has minimum distance δ = 1 − d/q. Reed–Muller Codes are a common
generalization of both Hadamard and Reed–Solomon codes, and thus
we can hope that for an appropriate setting of parameters, we will
be able to get the best of both kinds of codes. That is, we want to
combine the eﬃcient local decoding of the Hadamard code with the
good rate of Reed–Solomon codes.

Theorem 7.42. The q-ary Reed–Muller Code of degree d and
dimension m has a local 1/12-correcting algorithm running in time
poly(m, q) provided d ≤ q/9 and q ≥ 36.

Note the running time of the decoder is roughly the mth root
of the block length ˆL = qm. When m = 1, our decoder can query
the entire string and we simply obtain a global decoding algorithm
for Reed–Solomon Codes (which we already know how to achieve
from Theorem 5.19). But for large enough m, the decoder can only
access a small fraction of the received word. (In fact, one can improve
the running time to poly(m, d, log q), but the weaker result above is
suﬃcient for our purposes.)

The key idea behind the decoder is to do restrictions to random
lines in Fm. The restriction of a Reed–Muller codeword to such a line
is a Reed–Solomon codeword, and we can aﬀord to run our global
Reed–Solomon decoding algorithm on the line.

Formally, for x, y ∈ Fm, we deﬁne the (parameterized) line through
x in direction y as the function (cid:6)x,y : F → Fm given by (cid:6)x,y(t) =x + ty.
Note that for every a ∈ F, b ∈ F \ {0}, the line (cid:6)x+ay,by has the same
set of points in its image as (cid:6)x,y; we refer to this set of points as an
unpolymerized line. When y = 0, the parameterized line contains only
the single point x.



<!-- pdf-page: 249 -->
246 Pseudorandom Generators

If g : Fm → F is any function and (cid:6) : F → Fm is a line, then we use
g|(cid:4) to denote the restriction of g to (cid:6), which is simply the composition
g ◦ (cid:6) : F → F. Note that if p is any polynomial of total degree at most
d, then p|(cid:4) is a (univariate) polynomial of degree at most d.

So we are given an oracle g of distance less than δ from some
degree d polynomial p : Fm → F, and we want to compute p(x) for
some x ∈ Fm. We begin by choosing a random line (cid:6) through x. Every
point of Fm \ {x} lies on exactly one parameterized line through x,
so the points on (cid:6) (except x) are distributed uniformly at random
over the whole domain, and thus g and p are likely to agree on these
points. Thus we can hope to use the points on this line to reconstruct
the value of p(x). If δ is suﬃciently small compared to the degree
(e.g., δ = 1/3(d + 1)), we can simply interpolate the value of p(x) from
d + 1 points on the line. This gives rise to the following algorithm.

Algorithm 7.43 (Local Corrector for Reed–Muller Code I).
Input: An oracle g : Fm → F, an input x ∈ Fm, and a degree
parameter d

(1) Choose y R← Fm. Let (cid:6) = (cid:6)x,y : F → Fm be the line through x

in direction y.

(2) Query g to obtain β0 = g|(cid:4)(α0) =g ((cid:6)(a0)), . . . , βd = g|(cid:4)(αd) =
g((cid:6)(ad)), where α0, . . . , αd ∈ F \ {0} are any ﬁxed points
(3) Interpolate to ﬁnd the unique univariate polynomial q of

degree at most d s.t. ∀ i, q(αi) =β i

(4) Output q(0)

Claim 7.44 If g has distance less than δ = 1/3(d + 1) from some
polynomial p of degree at most d, then Algorithm 7.43 will output
p(x) with probability greater than 2/3.

Proof of Claim: Observe that for all x ∈ Fm and αi ∈ F \ {0},
(cid:6)x,y(αi) is uniformly random in Fm over the choice of y R← Fm. This



<!-- pdf-page: 250 -->
7.5 Worst-Case/Average-Case Reductions and Locally Decodable Codes

247

implies that for each i,

[g|(cid:4)(αi) (cid:1)= p|(cid:4)(αi)] < δ =

Pr
(cid:4)

1
3(d + 1)

.

By a union bound,

[∃i, g|(cid:4)(αi) (cid:1)= p|(cid:4)(αi)] < (d + 1)· δ =

Pr
(cid:4)

1
3

.

Thus, with probability greater than 2/3, we have ∀ i, q(αi) =p| (cid:4)(αi)
and hence
the algorithm
is poly(m, q).

running time of

q(0) = p(x). The

We now show how to improve the decoder to handle a larger fraction
of errors, up to distance δ = 1/12. We alter Steps 7.43 and 7.43 in the
above algorithm. In Step 7.43, instead of querying only d + 1 points,
we query over all points in (cid:6). In Step 7.43, instead of interpolation,
we use a global decoding algorithm for Reed–Solomon codes to decode
the univariate polynomial p|(cid:4). Formally, the algorithm proceeds as
follows.

Algorithm 7.45 (Local Corrector for Reed–Muller Codes II).
Input: An oracle g : Fm → F, an input x ∈ Fm, and a degree parame-
ter d, where q = |F| ≥36 and d ≤ q/9.

(1) Choose y R← Fm. Let (cid:6) = (cid:6)x,y : F → Fm be the line through x

in direction y.

(2) Query g at all points on (cid:6) to obtain g|(cid:4) : F → F.
(3) Run the 1/3-decoder for the q-ary Reed–Solomon code of
degree d on g|(cid:4) to obtain the (unique) polynomial q at
distance less than 1/3 from g|(cid:4) (if one exists).5

(4) Output q(0).

5 A 1/3-decoder for Reed–Solomon codes follows from the (1 − 2
d/q) list-decoding algo-
rithm of Theorem 5.19. Since 1/3 ≤ 1 − 2
d/q, the list-decoder will produce a list con-
taining all univariate polynomials at distance less than 1/3, and since 1/3 is smaller than
half the minimum distance (1 − d/q), there will be only one good decoding.

(cid:1)

(cid:1)



<!-- pdf-page: 251 -->
248 Pseudorandom Generators

Claim 7.46. If g has distance less than δ = 1/12 from some polynomial
p of degree at most d, and the parameters satisfy q = |F| ≥36, d ≤ q/9,
then Algorithm 7.45 will output p(x) with probability greater than 2/3.

Proof of Claim: The expected distance (between g|(cid:4) and p|(cid:4)) is small:

[dH (g|(cid:4), p|(cid:4))] <

E
(cid:4)

1
q

+ δ =

1
36

+

1
12

=

1
9

,

where the term 1/q is due to the fact that the point x is not random.
Therefore, by Markov’s Inequality,

Pr[dH (g|(cid:4), p|(cid:4)) ≥ 1/3] ≤ 1/3.

Thus, with probability at least 2/3, we have that p|(cid:4) is the unique
polynomial of degree at most d at distance less than 1/3 from g|(cid:4) and
thus q must equal p|(cid:4).

7.5.2 Low-Degree Extensions

Recall that to obtain locally decodable codes from locally correctible
codes (as constructed above), we need to exhibit systematic encoding:
(Deﬁnition 7.38.) Thus, given f : [L] → {0, 1}, we want to encode it as
a Reed–Muller codeword ˆf : [ ˆL] → Σ s.t.:

• The encoding time is 2O((cid:4)) = poly(L).
• ˆ(cid:6) = O((cid:6)), or equivalently ˆL = poly(L).
• The code is systematic in the sense of Deﬁnition 7.38.

Note that the usual encoding for Reed–Muller codes, where the mes-
sage gives the coeﬃcients of the polynomial, is not systematic. Instead
the message should correspond to evaluations of the polynomial at
certain points. Once we settle on the set of evaluation points, the task
becomes one of interpolating the values at these points (given by the
message) to a low-degree polynomial deﬁned everywhere.

The simplest approach is to use the boolean hypercube as the set

of evaluation points.



<!-- pdf-page: 252 -->
7.5 Worst-Case/Average-Case Reductions and Locally Decodable Codes

249

Lemma 7.47.(multilinear extension) For every f : {0, 1}(cid:4) → {0, 1}
and every ﬁnite ﬁeld F, there exists a (unique) polynomial ˆf : F(cid:4) → F
such that ˆf |{0,1}(cid:2) ≡ f and ˆf has degree at most 1 in each variable (and
hence total degree at most (cid:6)).

Proof. We prove the existence of the polynomial ˆf . Deﬁne

ˆf (x1, . . . , x(cid:4)) =

(cid:3)

f (α)δα(x)

α∈{0,1}(cid:2)

for

(cid:20)

(cid:5)

(cid:21) (cid:20)

(cid:5)

δα(x) =

xi

i : αi=1

i : αi=0

(cid:21)

(1 − xi)

Note that for x ∈ {0, 1}(cid:4), δα(x) = 1 only when α = x, therefore
ˆf |{0,1}(cid:2) ≡ f . We omit the proof of uniqueness. The bound on the
individual degrees is by inspection.

Thinking of ˆf as an encoding of f , let’s inspect the properties of

this encoding.

• Since the total degree of the multilinear extension can be
as large as (cid:6), we need q ≥ 9(cid:6) for the local corrector of
Theorem 7.42 to apply.

• The encoding time is 2O(ˆ(cid:4)), as computing a single point of
ˆf requires summing over 2(cid:4) elements, and we have 2ˆ(cid:4) points
on which to compute ˆf .

• The code is systematic, since ˆf is an extension of f .
• However, the input length is ˆ(cid:6) = (cid:6) log q = Θ((cid:6) log (cid:6)), which is

slightly larger than our target of ˆ(cid:6) = O((cid:6)).

To solve the problem of the input length ˆ(cid:6) in the multilinear
encoding, we reduce the dimension of the polynomial ˆf by changing
the embedding of the domain of f : Instead of interpreting {0, 1}(cid:4) ⊂ F(cid:4)
as an embedding of the domain of f in F(cid:4), we map{0, 1}(cid:4) to Hm for
some subset H ⊂ F, and as such embed it in Fm.



<!-- pdf-page: 253 -->
250 Pseudorandom Generators

More precisely, we ﬁx a subset H ⊂ F of size |H| = (cid:15)

q(cid:16). Choose
m = (cid:15)(cid:6)/log |H|(cid:16), and ﬁx some eﬃcient one-to-one mapping from {0, 1}(cid:4)
into Hm. With this mapping, view f as a function f : Hm → F.

√

Analogously to before, we have the following.

(low-degree extension) For every ﬁnite ﬁeld F,
Lemma 7.48.
H ⊂ F, m ∈ N, and function f : Hm → F, there exists a (unique)
ˆf : Fm → F such that ˆf |Hm ≡ f and ˆf has degree at most |H| −1 in
each variable (and hence has total degree at most m · (|H| −1)).

√

Using |H| = (cid:15)

q(cid:16), the total degree of ˆf is at most d = (cid:6)

q. So we
can apply the local corrector of Theorem 7.42, as long as q ≥ 81(cid:6)2 (so
that d ≤ q/9). Inspecting the properties of ˆf as an encoding of f , we
have:

√

• The input length is ˆ(cid:6) = m · log q = (cid:15)(cid:6)/log |H|(cid:16) · log q = O((cid:6)),
as desired. (We can use a ﬁeld of size 2k for k ∈ N, so that ˆL
is a power of 2 and we incur no loss in encoding inputs to ˆf
as bits.)

• The code is systematic as long as our mapping from {0, 1}(cid:4)

to Hm is eﬃcient.

Note that not every polynomial of total degree at most m · (|H| −1)
is the low-degree extension of a function f : Hm → F, so the image of
our encoding function f (cid:14)→ ˆf is only a subcode of the Reed–Muller code.
This is not a problem, because any subcode of a locally correctible
code is also locally correctible, and we can aﬀord the loss in rate (all
we need is ˆ(cid:6) = O((cid:6))).

7.5.3 Putting It Together

Combining Theorem 7.42 with Lemmas 7.48, and 7.39, we obtain the
following locally decodable code:

Proposition 7.49. For every L ∈ N, there is an explicit code Enc :
{0, 1}L → Σ ˆL, with blocklength ˆL = poly(L) and alphabet size |Σ| =
poly(log L), that has a local (1/12)-decoder running in time poly(log L).



<!-- pdf-page: 254 -->
7.5 Worst-Case/Average-Case Reductions and Locally Decodable Codes

251

Using Proposition 7.36, we obtain the following conversion from

worst-case hardness to average-case hardness:

If there exists f : {0, 1}(cid:4) → {0, 1} in E that is
Proposition 7.50.
worst-case hard against (nonuniform) time t((cid:6)), then there exists
ˆf : {0, 1}O((cid:4)) → {0, 1}O(log (cid:4)) in E that is (t(cid:3)((cid:6)), 1/12) average-case hard
for t(cid:3)((cid:6)) =t((cid:6))/poly( (cid:6)).

This diﬀers from our original goal in two ways: ˆf is not Boolean,
and we only get hardness 1/12 (instead of 1/2 − ε). The former concern
can be remedied by concatenating the code of Proposition 7.49 with
a Hadamard code, similarly to Problem 5.2. Note that the Hadamard
code is applied on message space Σ, which is of size polylog(L), so it
can be 1/4-decoded by brute-force in time polylog(L) (which is the
amount of time already taken by our decoder).6 Using this, we obtain:

Theorem 7.51. For
Enc : {0, 1}L → {0, 1} ˆL with blocklength ˆL = poly(L)
local (1/48)-decoder running in time poly(log L).

every L ∈ N,

there

is an explicit

code
that has a

Theorem 7.52. If there exists f : {0, 1}(cid:4) → {0, 1} in E that is worst-
case hard against time t((cid:6)), then there exists ˆf : {0, 1}O((cid:4)) → {0, 1} in
E that is (t(cid:3)((cid:6)), 1/48) average-case hard, for t(cid:3)((cid:6)) =t((cid:6))/poly( (cid:6)).

An improved decoding distance can be obtained using Problem 7.7.
We note that the local decoder of Theorem 7.51 not only runs
in time poly(log L), but also makes poly(log L) queries. For some
applications (such as Private Information Retrieval, see Problem 7.6),
it is important to have the number q of queries be as small as possible,
ideally a constant. Using Reed–Muller codes of constant degree, it
is possible to obtain constant-query locally decodable codes, but the

6 Some readers may recognize this concatenation step as the same as applying the
“Goldreich–Levin hardcore predicate” to ˆf . (See Problems 7.12 and 7.13.) However, for
the parameters we are using, we do not need the power of these results, and can aﬀord to
perform brute-force unique decoding instead.



<!-- pdf-page: 255 -->
252 Pseudorandom Generators

blocklength will be ˆL = exp(L1/(q−1)). In a recent breakthrough, it
was shown how to obtain constant-query locally decodable codes with
blocklength ˆL = exp(Lo(1)). Obtaining polynomial blocklength remains
open.

Open Problem 7.53. Are there binary codes that are locally
decodable with a constant number of queries (from constant distance
δ > 0) and blocklength polynomial in the message length?

7.5.4 Other Connections

As shown in Problem 7.6, locally decodable codes are closely related
to protocols for private information retrieval. Another connection, and
actually the setting in which these local decoding algorithms were ﬁrst
discovered, is to program self-correctors. Suppose we have a program for
computing a function, such as the Determinant, which happens to be
a codeword in a locally decodable code (e.g., the determinant is a low-
degree multivariate polynomial, and hence a Reed–Muller codeword).
Then, even if this program has some bugs and gives the wrong answer
on some small fraction of inputs, we can use the local decoding algo-
rithm to obtain the correct answer on all inputs with high probability.

7.6 Local List Decoding and PRGs from

Worst-Case Hardness

7.6.1 Hardness Ampliﬁcation

In the previous section, we saw how to use locally decodable codes to
convert worst-case hard functions into ones with constant average-case
hardness (Theorem 7.52). Now our goal is to amplify this hardness
(e.g., to 1/2 − ε).

There are some generic techniques for hardness ampliﬁcation. In
these methods, we evaluate the function on many independent inputs.
For example, consider f (cid:3) that concatenates the evaluations of ˆf on k
independent inputs:

f (cid:3)(x1, . . . , xk) = ( ˆf (x1), . . . , ˆf (xk)).



<!-- pdf-page: 256 -->
7.6 Local List Decoding and PRGs from Worst-Case Hardness

253

Intuitively, if ˆf is 1/12 average-case hard, then f (cid:3) should be (1 −
(11/12)k)-average case hard because any eﬃcient algorithm can solve
each instance correctly with probability at most 11/12. Proving this
is nontrivial (because the algorithm trying to compute f (cid:3) need not
behave independently on the k instances), but there are Direct Prod-
uct Theorems showing that the hardness does get ampliﬁed essentially
as expected. Similarly, if we take the XOR on k independent inputs, the
XOR Lemma says that the hardness approaches 1/2 exponentially fast.
The main disadvantage of these approaches (for our purposes) is
that the input length of f (cid:3) is k(cid:6) while we aim for input length of O((cid:6)).
To overcome this problem, it is possible to use derandomized products,
where we evaluate ˆf on correlated inputs instead of independent ones.
We will take a diﬀerent approach, generalizing the notion and
algorithms for locally decodable codes to locally list-decodable codes,
and thereby directly construct ˆf that is (1/2 − ε)-hard. Nevertheless,
the study of hardness ampliﬁcation is still of great interest, because it
(or variants) can be employed in settings where doing a global encod-
ing of the function is infeasible (e.g., for amplifying the average-case
hardness of functions in complexity classes lower than E, such as
NP, and for amplifying the security of cryptographic primitives). We
remark that results on hardness ampliﬁcation can be interpreted in
a coding-theoretic language as well, as converting locally decodable
codes with a small decoding distance into locally list-decodable codes
with a large decoding distance. (See Section 8.2.3.)

7.6.2 Deﬁnition

We would like to formulate a notion of local list-decoding to enable us
to have binary codes that are locally decodable from distances close
to 1/2. This is somewhat tricky to deﬁne — what does it mean to
produce a “list” of decodings when only asked to decode a particular
coordinate? Let g be our received word, and ˆf1, ˆf2, . . . , ˆfs the codewords
that are close to g. One option would be for the decoding algorithm,
on input x, to output a set of values Decg(x) ⊂ Σ that is guaranteed
to contain ˆf1(x), ˆf2(x), . . . ˆfs(x) with high probability. However, this is
not very useful; in the common case that s ≥ |Σ|, the list could always



<!-- pdf-page: 257 -->
254 Pseudorandom Generators

be Decg(x) = Σ. Rather than outputting all of the values, we want to
be able to specify to our decoder which ˆfi(x) to output. We do this
with a two-phase decoding algorithm (Dec1, Dec2), where both phases
can be randomized.

(1) Dec1, using g as an oracle and not given any other input
other than the parameters deﬁning the code, returns a list
of advice strings a1, a2, . . . , as, which can be thought of as
“labels” for each of the codewords close to g.

(2) Dec2 (again, using oracle access to g), takes input x and ai,

and outputs ˆfi(x).

The picture for Dec2 is much like our old decoder, but it takes an

extra input ai corresponding to one of the outputs of Dec1:

g

oracle access

x

a_i

Dec_2

f_i(x)

More formally:

Deﬁnition 7.54. A local δ-list-decoding algorithm for a code Enc is
a pair of probabilistic oracle algorithms (Dec1, Dec2) such that for all
received words g and all codewords ˆf = Enc(f ) with dH ( ˆf , g) < δ, the
following holds. With probability at least 2/3 over (a1, . . . , as) ← Decg
1,
there exists an i ∈ [s] such that
∀ x, Pr[Decg

2(x, ai) =f (x)] ≥ 2/3.

Note that we don’t explicitly require a bound on the list size s
(to avoid introducing another parameter), but certainly it cannot be
larger than the running time of Dec1.

As we did for locally (unique-)decodable codes, we can deﬁne a
local δ-list-correcting algorithm, where Dec2 should recover arbitrary
symbols of the codeword ˆf rather than the message f . In this case,
we don’t require that for all j, Decg
2(·, aj) is a codeword, or that it is



<!-- pdf-page: 258 -->
7.6 Local List Decoding and PRGs from Worst-Case Hardness

255

close to g; in other words, some of the ajs may be junk. Analogously
to Lemma 7.39, a local δ-list-correcting algorithm implies local
δ-list-decoding if the code is systematic.

Proposition 7.36 shows how locally decodable codes convert
functions that are hard in the worst case to ones that are hard on
average. The same is true for local list-decoding:

Proposition 7.55. Let Enc be an error-correcting code with local
δ-list-decoding algorithm (Dec1, Dec2) where Dec2 runs in time at
most tDec, and let f be worst-case hard for non-uniform time t. Then
ˆf = Enc(f ) is (t(cid:3), δ) average-case hard, where t(cid:3) = t/tDec.

Proof. Suppose for contradiction that ˆf is not (t(cid:3), δ)-hard. Then some
nonuniform algorithm A running in time t(cid:3) computes ˆf with error prob-
ability smaller than δ. But if Enc has a local δ list-decoding algorithm,
then (with A playing the role of g) that means there exists ai (one
2 (·, ai) computes f (·)
of the possible outputs of DecA
2 (·, ai) is a nonuniform
everywhere. Hardwiring ai as advice, DecA
algorithm running in time at most time(A) · time(Dec2) ≤ t.

1 ), such that DecA

Note that,

in contrast to Proposition 7.36, here we are using
nonuniformity more crucially, in order to select the right function from
the list of possible decodings. As we will discuss in Section 7.7.1, this
use of nonuniformity is essential for “black-box” constructions, that do
not exploit any structure in the hard function f or the adversary (A in
the above proof). However, there are results on hardness ampliﬁcation
against uniform algorithms, which use structure in the hard function
f (e.g., that it is complete for a complexity class like E or NP) to
identify it among the list of decodings without any nonuniform advice.

7.6.3 Local List-Decoding Reed–Muller Codes

Theorem 7.56. There is a universal constant c such that the q-ary
Reed–Muller code of degree d and dimension m over can be locally
(1 − ε)-list-corrected in time poly(q, m) for ε = c

d/q.

(cid:7)



<!-- pdf-page: 259 -->
256 Pseudorandom Generators

Note that the distance at which list decoding can be done
approaches 1 as q/d → ∞. It matches the bound for list-decoding
Reed–Solomon codes (Theorem 5.19) up to the constant c. Moreover,
as the dimension m increases, the running time of the decoder
(poly(q, m)) becomes much smaller than the block length (qm · log q),
(cid:2)
m+d
at the price of a reduced rate (
m
Proof. Suppose we are given an oracle g : Fm → F that is (1 − ε) close
to some unknown polynomial p : Fm → F, and that we are given an x ∈
Fm. Our goal is to describe two algorithms, Dec1 and Dec2, where Dec2
is able to compute p(x) using a piece of Dec1’s output (i.e., advice).

/qm).

(cid:1)

The advice that we will give to Dec2 is the value of p on a single
point. Dec1 can easily generate a (reasonably small) list that contains
one such point by choosing a random y ∈ Fm, and outputting all pairs
(y, z), for z ∈ F. More formally:

Algorithm 7.57 (Reed–Muller Local List-Decoder Dec1).
Input: An oracle g : Fm → F and a degree parameter d

(1) Choose y R← Fm
(2) Output {(y, z) :z ∈ F}

This ﬁrst-phase decoder is rather trivial in that it doesn’t make use
of the oracle access to the received word g. It is possible to improve
both the running time and list size of Dec1 by using oracle access to g,
but we won’t need those improvements below.

Now, the task of Dec2 is to calculate p(x), given the value of p
on some point y. Dec2 does this by looking at g restricted to the line
through x and y, and using the list-decoding algorithm for Reed–
Solomon Codes to ﬁnd the univariate polynomials q1, q2, . . . , qt that are
close to g. If exactly one of these polynomials qi agrees with p on the
test point y, then we can be reasonably conﬁdent that qi(x) =p(x ).

In more detail, the decoder works as follows:

Algorithm 7.58 (Reed–Muller Local List-Corrector Dec2).
Input: An oracle g : Fm → F, an input x ∈ Fm, advice (y, z) ∈ Fm × F,



<!-- pdf-page: 260 -->
7.6 Local List Decoding and PRGs from Worst-Case Hardness

257

and a degree parameter d

(1) Let (cid:6) = (cid:6)x,y−x : F → Fm be the line through x and y (so that

(cid:6)(0) = x and (cid:6)(1) = y).

(2) Run the (1 − ε/2)-list-decoder for Reed–Solomon Codes
(Theorem 5.19) on g|(cid:4) to get all univariate polys q1, . . . , qt
that agree with g|(cid:4) in greater than an ε/2 fraction of points.
(3) If there exists a unique i such that qi(1) = z, output qi(0).

Otherwise, fail.

Now that we have fully speciﬁed the algorithms, it remains to
analyze them and show that they decode p correctly. Observe that it
suﬃces to compute p on greater than an 11/12 fraction of the points
x, because then we can apply the unique local correcting algorithm of
Theorem 7.42. Therefore, to ﬁnish the proof of the theorem we must
prove the following.

Claim 7.59. Suppose that g : Fm → F has agreement greater than ε
with a polynomial p : Fm → F of degree at most d. For at least half
of the points y ∈ Fm the following holds for greater than an 11/12
fraction of lines (cid:6) going through y:

(1) agr(g|(cid:4), p|(cid:4)) > ε/2.
(2) There does not exist any univariate polynomial q of degree
at most d other than p|(cid:4) such that agr(g|(cid:4), q) > ε/2 and
q(y) =p(y ).

Proof of Claim:
It suﬃces to show that Items 7.59 and 7.59 hold
with probability 0.99 over the choice of a random point y R← Fm and
a random line (cid:6) through y; then we can apply Markov’s inequality to
ﬁnish the job.

Item 7.59 holds by pairwise independence. If the line (cid:6) is chosen
randomly, then the q points on (cid:6) are pairwise independent samples
of Fm. The expected agreement between g|(cid:4) and p|(cid:4) is simply the



<!-- pdf-page: 261 -->
258 Pseudorandom Generators

agreement between g and p, which is greater than ε by hypothesis. So
by the Pairwise-Independent Tail Inequality (Prop. 3.28),

Pr[agr(g|(cid:4), p|(cid:4)) ≤ ε/2] <

1
q · (ε/2)2 ,

which can be made smaller than 0.01 for a large enough choice of the
constant c in ε = c

d/q.

(cid:7)

To prove Item 7.59, we imagine ﬁrst choosing the line (cid:6) uniformly
at random from all lines in Fm, and then choosing y uniformly at
random from the points on (cid:6) (reparameterizing (cid:6) so that (cid:6)(1) = y).
Once we choose (cid:6), we can let q1, . . . , qt be all polynomials of degree
at most d, other than p|(cid:4), that have agreement greater than ε/2 with
g|(cid:4). (Note that this list is independent of the parametrization of (cid:6),
i(x) =q i(ax + b)
i.e.,
have agreement equal to agr(p|(cid:4), qi).) By the list-decodability of
Reed–Solomon Codes (Proposition 5.15), we have t = O(

if (cid:6)(cid:3)(x) =(cid:6)(ax + b) for a (cid:1)= 0 then p|(cid:4)(cid:2) and q(cid:3)

q/d).

(cid:7)

Now, since two distinct polynomials can agree in at most d points,
when we choose a random point y R← (cid:6), the probability that qi and
p agree at y is at most d/q. After reparameterization of (cid:6) so that
(cid:6)(1) = y, this gives

[∃i : qi(1) = p(1)] ≤ t · d
q

Pr
y

= O

(cid:20)(cid:26)

(cid:21)

.

d
q

This can also be made smaller than 0.01 for large enough choice
of the constant c (since we may assume q/d > c2, else ε ≥ 1 and the
result holds vacuously).

7.6.4 Putting it Together

To obtain a locally list-decodable (rather than list-correctible) code,
we again use the low-degree extension (Lemma 7.48) to obtain a
systematic encoding. As before, to encode messages of length (cid:6) = log L,
we apply Lemma 7.48 with |H| = (cid:15)
q(cid:16) and m = (cid:15)(cid:6)/ log |H|(cid:16), for total
degree d ≤
q · (cid:6). To decode from a 1 − ε fraction of errors using
d/q ≤ ε, which follows if q ≥ c2(cid:6)2/ε4. This
Theorem 7.56, we need c

(cid:7)

√

√



<!-- pdf-page: 262 -->
7.6 Local List Decoding and PRGs from Worst-Case Hardness

259

yields the following locally list-decodable codes:

Theorem 7.60. For every L ∈ N and ε >0, there is an explicit code
Enc : {0, 1}L → Σ ˆL, with blocklength ˆL = poly(L, 1/ε) and alphabet
size |Σ| = poly(log L, 1/ε), that has a local (1 − ε)-list-decoder running
in time poly(log L, 1/ε).

Concatenating the code with a Hadamard code, similarly to

Problem 5.2, we obtain:

Theorem 7.61. For every L ∈ N and ε >0, there is an explicit code
Enc : {0, 1}L → {0, 1} ˆL with blocklength ˆL = poly(L, 1/ε) that has a
local (1/2 − ε)-list-decoder running in time poly(log L, 1/ε).

Using Proposition 7.55, we get the following hardness ampliﬁcation

result:

Theorem 7.62. For s : N → N, suppose that there is a function
f : {0, 1}(cid:4) → {0, 1} in E that is worst-case hard against nonuniform
time s((cid:6)), where s((cid:6)) is computable in time 2O((cid:4)), then there exists
ˆf : {0, 1}O((cid:4)) → {0, 1} in E that is (1/2 − 1/s(cid:3)((cid:6))) average-case hard
against (non-uniform) time s(cid:3)((cid:6)) for s(cid:3)((cid:6)) =t((cid:6)) Ω(1)/poly((cid:6)).

Combining this with Theorem 7.19 and Corollary 7.20, we get:

Theorem 7.63. For s : N → N, suppose that there is a function f ∈ E
such that for every input length (cid:6) ∈ N, f is worst-case hard for nonuni-
form time s((cid:6)), where s((cid:6)) is computable in time 2O((cid:4)). Then for every
m ∈ N, there is a mildly explicit (m, 1/m) pseudorandom generator G :
{0, 1}d(m) → {0, 1}m with seed length d(m) =O (s−1(poly(m))2/ log m).

Corollary 7.64. For s : N → N, suppose that there is a function
f ∈ E = DTIME(2O((cid:4))) such that for every input length (cid:6) ∈ N, f is



<!-- pdf-page: 263 -->
260 Pseudorandom Generators

worst-case hard for nonuniform time s((cid:6)). Then:

(1) If s((cid:6)) = 2Ω((cid:4)), then BPP = P.
(2) If s((cid:6)) = 2(cid:4)Ω(1)
, then BPP ⊂ ˜P.
(3) If s((cid:6)) =(cid:6) ω(1), then BPP ⊂ SUBEXP.

We note that the hypotheses in these results are simply asserting
that there are problems in E of high circuit complexity, which is quite
plausible. Indeed, many common NP-complete problems, such as
SAT, are in E and are commonly believed to have circuit complexity
2Ω((cid:4)) on inputs of length (cid:6) (though we seem very far from proving it).
Thus, we have a “win–win” situation, either we can derandomize all
of BPP or SAT has signiﬁcantly faster (nonuniform) algorithms than
currently known.

Problem 7.1 establishes a converse to Theorem 7.63, showing that
pseudorandom generators imply circuit lower bounds. The equivalence
is fairly tight, except for the fact that Theorem 7.63 has seed length
d(m) =O (s−1(poly(m))2/ log m) instead of d(m) =O (s−1(poly(m))).
It is known how to close this gap via a diﬀerent construction, which
is more algebraic and constructs PRGs directly from worst-case hard
functions (see the Chapter Notes and References); a (positive) solution
to Open Problem 7.25 would give a more modular and versatile
construction. For Corollary 7.64, however, there is only a partial
converse known. See Section 8.2.2.

Technical Comment. Consider Item 3 of Corollary 7.64, which
assumes that there is a problem in E of superpolynomial circuit
complexity. This sounds similar to assuming that E (cid:1)⊂ P/poly (which
is equivalent to EXP (cid:1)⊂ P/poly, by Problem 7.2). However, the latter
assumption is a bit weaker, because it only guarantees that there is a
function f ∈ E and a function s((cid:6)) =(cid:6) ω(1) such that f has complexity
at least s((cid:6)) for inﬁnitely many input lengths (cid:6). Theorem 7.63 and
Corollary 7.64 assume that f has complexity at least s((cid:6)) for all (cid:6);
equivalently f is not in i.o.-P/poly, the class of functions that are
computable by poly-sized circuits for inﬁnitely many input lengths. We
need the stronger assumptions because we want to build generators
G : {0, 1}d(m) → {0, 1}m that are pseudorandom for all output lengths



<!-- pdf-page: 264 -->
7.7 Connections to Other Pseudorandom Objects

261

m, in order to get derandomizations of BPP algorithms that are
correct on all input lengths. However, there are alternate forms of
these results, where the “inﬁnitely often” is moved from the hypothesis
if E (cid:1)⊂ P/poly, we can conclude
to the conclusion. For example,
that BPP ⊂ i.o.-SUBEXP, where i.o.-SUBEXP denotes the class
of
languages having deterministic subexponential-time algorithms
that are correct for inﬁnitely many input lengths. Even though these
“inﬁnitely often” issues need to be treated with care for the sake of
precision, it would be quite unexpected if the complexity of problems
in E and BPP oscillated as a function of input length in such a
strange way that they made a real diﬀerence.

7.7 Connections to Other Pseudorandom Objects

7.7.1 Black-Box Constructions

Similarly to our discussion after Theorem 7.19, the pseudorandom
generator construction in the previous section is very general. The con-
struction shows how to take any function f : {0, 1}(cid:4) → {0, 1} and use it
as a subroutine (oracle) to compute a generator Gf : {0, 1}d → {0, 1}m
whose pseudorandomness can be related to the hardness of f . The
only place that we use the fact that f ∈ E is to deduce that Gf is
computable in E. The reduction proving that Gf is pseudorandom is
also very general. We showed how to take any T that distinguishes
the output of Gf (Ud) from Um and use it as a subroutine (oracle)
to build an eﬃcient nonuniform algorithm Red such that RedT
computes f . The only place that we use the fact that T is itself an
eﬃcient nonuniform algorithm is to deduce that RedT is an eﬃcient
nonuniform algorithm, contradicting the worst-case hardness of f .

Such constructions are called “black box,” because they treat the
hard function f and the distinguisher T as black boxes (i.e., oracles),
without using the code of the programs that compute f and T .
As we will see, black-box constructions have signiﬁcant additional
implications. Thus, we formalize the notion of a black-box construction
as follows:

Deﬁnition 7.65. Let Gf : [D] → [M ] be a deterministic algorithm
that is deﬁned for every oracle f : [L] → {0, 1}, let t, k be positive



<!-- pdf-page: 265 -->
262 Pseudorandom Generators

integers such that k ≤ t, and let ε >0. We say that G is a (t, k, ε)
black-box PRG construction if there is a randomized oracle algorithm
Red, running in time t, such that for every f : [L] → {0, 1} and
T : [M ] → {0, 1} such that if

Pr[T (Gf (U[D])) = 1] − Pr[T (U[M ]) = 1] > ε,

then there is an advice string z ∈ [K] such that

∀ x ∈ [L] Pr[RedT (x, z) =f (x)] ≥ 2/3,

where the probability is taken over the coin tosses of Red.

Note that we have separated the running time t of Red and the
length k of its nonuniform advice into two separate parameters, and
assume k ≤ t since an algorithm cannot read more than k bits in
time t. When we think of Red as a nonuniform algorithm (like a
boolean circuit), then we may as well think of these two parameters as
being equal. (Recall that, up to polylog(s) factors, being computable
by a circuit of size s is equivalent to being computable by a uniform
algorithm running in time s with s bits of nonuniform advice.)
However, separating the two parameters is useful in order to isolate
the role of nonuniformity, and to establish connections with the other
pseudorandom objects we are studying.7

We note that if we apply a black-box pseudorandom generator
construction with a function f that is actually hard to compute, then
the result is indeed a pseudorandom generator:

Proposition 7.66.
If G is a (t, k, ε) black-box PRG construction
and f has nonuniform worst-case hardness at least s, then Gf is an
(s/ ˜O(t), ε) pseudorandom generator.

7 Sometimes it is useful to allow the advice string z to also depend on the coin tosses of
the reduction Red. By error reduction via r = O((cid:4)) repetitions, such a reduction can be
converted into one satisfying Deﬁnition 7.65 by sampling r = O((cid:4)) sequences of coin tosses,
but this blows up the advice length by a factor of r, which may be too expensive.



<!-- pdf-page: 266 -->
7.7 Connections to Other Pseudorandom Objects

263

Now, we can rephrase the pseudorandom generator construction of

Theorem 7.63 as follows:

Theorem 7.67. For every constant γ > 0, and every (cid:6), m ∈ N,
and every ε >0, there is a (t, k, ε) black-box PRG construction
Gf : {0, 1}d → {0, 1}m that is deﬁned for every oracle f : {0, 1}(cid:4) → {0, 1},
with the following properties:

(1) (Mild) explicitness: Gf

is computable in uniform time

poly(m, 2(cid:4)) given an oracle for f .

(2) Seed length: d = O(((cid:6) + log(1/ε))2/ log m).
(3) Reduction running time: t = poly(m, 1/ε).
(4) Reduction advice length: k = m1+γ + O((cid:6) + log(m/ε)).

In addition to asserting the black-box nature of Theorem 7.63, the
above is more general in that it allows ε to vary independently of m
(rather than setting ε = 1/m), and gives a tighter bound on the length
of the nonuniform advice than just t = poly(m, 1/ε).

Proof Sketch: Given a function f , Gf encodes f in the locally
list-decodable code of Theorem 7.61 (with decoding distance 1/2 − ε(cid:3)
for ε(cid:3) = ε/m) to obtain ˆf : {0, 1}ˆ(cid:4) → {0, 1} with ˆ(cid:6) = O((cid:6) + log(1/ε)),
and then computes the Nisan–Wigderson generator based on ˆf
(Construction 7.23) and a (ˆ(cid:6), γ log m) design. The seed length and
mild explicitness follow from the explicitness and parameters of the
design and code (Lemma 7.22 and Theorem 7.61). The running time
and advice length of the reduction follow from inspecting the proofs
of Theorems 7.61 and 7.19. Speciﬁcally, the running time of of the
Nisan–Wigderson reduction in the proof of Theorem 7.19 is poly(m)
(given the nonuniform advice) by inspection, and the running time of
the local list-decoding algorithm is poly((cid:6), 1/ε(cid:3)) ≤ poly(m, 1/ε). (We
may assume that m > (cid:6), otherwise Gf need not have any stretch, and
the conclusion is trivial.) The length of the advice from the locally
list-decodable code consists of a pair (y, z) ∈ Fv × F, where F is a
ﬁeld of size q = poly((cid:6), 1/ε) and v log |F| = ˆ(cid:6) = O((cid:6) + log(1/ε)). The



<!-- pdf-page: 267 -->
264 Pseudorandom Generators

Nisan–Wigderson reduction begins with the distinguisher-to-predictor
reduction of Proposition 7.16, which uses log m bits of advice to
specify the index i at which the predictor works and m − i − 1 bits
for hardwiring the bits fed to the distinguisher in positions i, . . . , m. In
addition, for j = 1, . . . , i − 1, the Nisan–Wigderson reduction nonuni-
formly hardwires a truth-table for the function fj(y) which depends on
the at most γ · log m bits of y selected by the intersection of the ith and
jth sets in the design. These truth tables require at most (i − 1) · mγ
bits of advice. In total, the amount of advice used is at most

O((cid:6) + log(1/ε)) + m − i − 1 + (i − 1) · mγ

= m1+γ + O((cid:6) + log(1/ε)).

One advantage of a black-box construction is that it allows us to
automatically “scale up” the pseudorandom generator construction.
If we apply the construction to a function f that is not necessarily
computable in E, but in some higher complexity class, we get a
pseudorandom generator Gf computable in an analogously higher
complexity class. Similarly, if we want our pseudorandom generator
to fool tests T computable by nonuniform algorithms in some higher
complexity class, it suﬃces to use a function f that is hard against an
analogously higher class.

For example, we get the following “nondeterministic” analogue of

Theorem 7.63:

Theorem 7.68. For s : N → N, suppose that there is a function f ∈
NE ∩ co-NE such that for every input length (cid:6) ∈ N, f is worst-case
hard for nonuniform algorithms running in time s((cid:6)) with an NP
oracle (equivalently, boolean circuits with SAT gates), where s((cid:6)) is
computable in time 2O((cid:4)). Then for every m ∈ N, there is a pseudo-
random generator G : {0, 1}d(m) → {0, 1}m with seed length d(m) =
O(s−1(poly(m))2/ log m)
(m, 1/m)-pseudorandom
such that G is
against nonuniform algorithms with an NP oracle, and G is computable
in nondeterministic time 2O(d(m)) (meaning that there is a nondetermin-
istic algorithm that on input x, outputs G(x) on at least one computa-
tion path and outputs either G(x) or “fail” on all computation paths).



<!-- pdf-page: 268 -->
7.7 Connections to Other Pseudorandom Objects

265

The signiﬁcance of such generators is that they can be used for
derandomizing AM, which is a randomized analogue of NP, deﬁned
as follows:

Deﬁnition 7.69. A language L is in AM iﬀ there is a probabilistic
polynomial-time veriﬁer V and polynomials m(n), p(n) such that for
all inputs x of length n,

x ∈ L ⇒

x /∈ L ⇒

Pr
R←{0,1}m(n)

r

Pr
R←{0,1}m(n)

r

[∃y ∈ {0, 1}p(n) V (x, r, y) = 1] ≥ 2/3,

[∃y ∈ {0, 1}p(n) V (x, r, y) = 1] ≤ 1/3.

Another (non-obviously!) equivalent deﬁnition of AM is the
class of languages having constant-round interactive proof systems,
where a computationally unbounded prover (“Merlin”) can convince
a probabilistic polynomial-time veriﬁer (“Arthur”) that an input
x is in L through an interactive protocol with of O(1) rounds of
polynomial-length communication.

Graph Nonisomorphism is the most famous example of a language
that is in AM but is not known to be in NP. Nevertheless, using The-
orem 7.68 we can give evidence that Graph Nonisomorphism is in NP.

Corollary 7.70.
inputs of
running in time 2Ω((cid:4)) with an NP oracle, then AM = NP.

If there is a function f ∈ NE ∩ co-NE that, on
is worst-case hard for nonuniform algorithms

length (cid:6),

While the above complexity assumption may seem very strong,
it is actually known to be weaker than the very natural assump-
tion that exponential time E = DTIME(2O((cid:4))) is not contained in
subexponential space ∩ε>0DSPACE(2εn).

As we saw in Section 7.4.3 on derandomizing constant-depth
circuits, black-box constructions can also be “scaled down” to apply
to lower complexity classes, provided that the construction G and/or
reduction Red can be shown to be computable in a lower class
(e.g., AC0).



<!-- pdf-page: 269 -->
266 Pseudorandom Generators

7.7.2 Connections to Other Pseudorandom Objects

At ﬁrst, it may seem that pseudorandom generators are of a diﬀerent
character than the other pseudorandom objects we have been studying.
We require complexity assumptions to construct pseudorandom gen-
erators, and reason about them using the language of computational
complexity (referring to eﬃcient algorithms, reductions, etc.). The
other objects we have been studying are all information-theoretic in
nature, and our constructions of them have been unconditional.

The notion of black-box constructions will enable us to bridge
this gap. Note that Theorem 7.67 is unconditional, and we will see
that it, like all black-box constructions, has an information-theoretic
interpretation. Indeed, we can ﬁt black-box pseudorandom generator
constructions into the list-decoding framework of Section 5.3 as follows:

Construction 7.71. Let Gf : [D] → [M ] be an algorithm that is
deﬁned for every oracle f : [n] → {0, 1}. Then, setting N = 2n, deﬁne
Γ : [N ] × [D] → [M ], by

where we view the truth table of f as an element of [N ] ≡ {0, 1}n.

Γ(f, y) =G f (y),

It turns out that if we allow the reduction unbounded running time
(but still bound the advice length), then pseudorandom generator
constructions have an exact characterization in our framework:

Proposition 7.72. Let Gf and Γ be as in Construction 7.71. Then
Gf is an (∞, k, ε) black-box PRG construction iﬀ for every T ⊂ [M ],
we have

|LISTΓ(T, µ(T ) +ε)| ≤K,

where K = 2k.

Proof.
⇒. Suppose Gf is an (∞, k, ε) black-box PRG construction. Then f
distinguishes Gf (U[D]) from U[M ] with
is in LISTΓ(T, µ(T ) +ε) iﬀT



<!-- pdf-page: 270 -->
7.7 Connections to Other Pseudorandom Objects

267

advantage greater than ε. This implies that there exists a z ∈ [K]
such that RedT (·, z) computes f everywhere. Thus, the number of
functions f in LISTΓ(T, µ(T ) +ε) is bounded by the number of advice
strings z, which is at most K.
⇐. Suppose that for every T ⊂ [M ], we have L = |LISTΓ(T, µ(T ) +
ε)| ≤K . Then we can deﬁne RedT (x, z) =f z(x), where f1, . . . , fL are
any ﬁxed enumeration of the elements of LISTΓ(T, µ(T ) +ε).

Notice that this characterization of black-box PRG constructions
(with reductions of unbounded running time) is the same as the one
for averaging samplers (Proposition 5.30) and randomness extractors
(Proposition 6.23). In particular, the black-box PRG construction
of Theorem 7.67 is already a sampler and extractor of very good
parameters:

Theorem 7.73. For every constant γ > 0, every n ∈ N, k ∈ [0, n], and
every ε >0, there is an explicit ( k, ε) extractor Ext : {0, 1}n × {0, 1}d →
{0, 1}m with seed length d = O(log2(n/ε)/ log k) and output length
m ≥ k1−γ.

Proof Sketch: Without loss of generality, assume that n is a power
of 2, namely n = 2(cid:4) = L. Let Gf (y) :{0, 1}d → {0, 1}m be the (t, k0, ε0)
black-box PRG construction of Theorem 7.67 which takes a function
f : {0, 1}(cid:4) → {0, 1} and has k0 = m1+γ + O((cid:6) + log(m/ε0)), and let
Ext(f, y) = Γ(f, y) =G f (y). By Propositions 7.72 and 6.23, Ext is a
(k0 + log(1/ε0), 2ε0) extractor. Setting ε = 2ε0 and k = k0 + log(1/ε0),
we have a (k, ε) extractor with output length

m = (k − O((cid:6) + log(m/ε)))1−γ ≥ k1−γ − O((cid:6) + log(m/ε)).
We can increase the output length to k1−γ by increasing the seed
length by O((cid:6) + log(m/ε)). The total seed length then is

(cid:14)

d = O

((cid:6) + log(1/ε))2
log m

+ (cid:6) + log(m/ε)

= O

(cid:15)

(cid:14)

(cid:15)

.

log2(n/ε)
log k

The parameters of Theorem 7.73 are not quite as good as those of
Theorem 6.36 and Corollary 6.39, as the output length is k1−γ rather



<!-- pdf-page: 271 -->
268 Pseudorandom Generators

than (1 − γ)k, and the seed length is only O(log n) when k = nΩ(1).
However, these settings of parameters are already suﬃcient for many
purposes, such as the simulation of BPP with weak random sources.
Moreover, the extractor construction is much more direct than that of
Theorem 6.36. Speciﬁcally, it is

Ext(f, y) = ( ˆf (y|S1), . . . , ˆf (y|Sm)),
where ˆf is an encoding of f in a locally list-decodable code and
S1, . . . , Sm are a design. In fact, since Proposition 7.72 does not depend
on the running time of the list-decoding algorithm, but only the
amount of nonuniformity, we can use any (1/2 − ε/2m, poly(m/ε))
list-decodable code, which will only require an advice of
length
O(log(m/ε)) to index into the list of decodings. In particular, we can
use a Reed–Solomon code concatenated with a Hadamard code, as in
Problem 5.2.

We now provide some additional

intuition for why black-box
pseudorandom generator constructions are also extractors. A black-
box PRG construction Gf
is designed to use a computationally
hard function f (plus a random seed) to produce an output that is
computationally indistinguishable from uniform. When we view it as
an extractor Ext(f, y) =G f (y), we instead are feeding it a function
f that is chosen randomly from a high min-entropy distribution (plus
a random seed). This can be viewed as saying that f is information-
theoretically hard, and from this stronger hypothesis, we are able
to obtain the stronger conclusion that the output is statistically
indistinguishable from uniform. The information-theoretic hardness
of f can be formalized as follows: if f is sampled from a source F
of min-entropy at least k + log(1/ε), then for every ﬁxed function A
(such as A = RedT ), the probability (over f ← F ) that there exists
a string z of length k such that A(·, z) computes f everywhere is at
most ε. That is, a function generated with min-entropy larger than
k is unlikely to have a description of length k (relative to any ﬁxed
“interpreter” A).

Similarly to black-box PRG constructions, we can also discuss
converting worst-case hard functions to average-case hard functions in



<!-- pdf-page: 272 -->
7.7 Connections to Other Pseudorandom Objects

269

a black-box manner:

Deﬁnition 7.74. Let Ampf : [D] → [q] be a deterministic algorithm
that is deﬁned for every oracle f : [n] → {0, 1}. We say that Amp is a
(t, k, ε) black-box worst-case-to-average-case hardness ampliﬁer if there
is a probabilistic oracle algorithm Red, called the reduction, running
in time t such that for every function g : [D] → [q] such that

Pr[g(U[D]) = Ampf (U[D])] > 1/q + ε,

there is an advice string z ∈ [K], where K = 2k, such that

∀ x ∈ [n]

Pr[Redg(x, z) =f (x)] ≥ 2/3,

where the probability is taken over the coin tosses of Red.

Note that this deﬁnition is almost identical to that of a locally
(1 − 1/q − ε)-list-decodable code (Deﬁnition 7.54), viewing Ampf as
Enc(f ), and Redg as Decg
2. The only diﬀerence is that in the deﬁnition
of locally list-decodable code, we require that there is a ﬁrst-phase
decoder Decg
1 that eﬃciently produces a list of candidate advice strings
(a property that is natural from a coding perspective, but is not
needed when amplifying hardness against nonuniform algorithms). If
we remove the constraint on the running time of Red, we simply obtain
the notion of a (1 − 1/q − ε, K) list-decodable code. By analogy, we
can view black-box PRG constructions (with reductions of bounded
running time) as simply being extractors (or averaging samplers) with
a kind of eﬃcient local list-decoding algorithm (given by Red, again
with an advice string that need not be easy to generate).

In addition to their positive uses illustrated above, black-box reduc-
tions and their information-theoretic interpretations are also useful for
understanding the limitations of certain proof techniques. For example,
we see that a black-box PRG construction Gf : {0, 1}d → {0, 1}m must
have a reduction that uses k ≥ m − d − log(1/ε) − 1 bits of advice.
Otherwise, by Propositions 7.72 and 6.23, we would obtain a (k, 2ε)
extractor that outputs m almost-uniform bits when given a source
of min-entropy less than k − d − 1, which is impossible if ε <1/4.



<!-- pdf-page: 273 -->
270 Pseudorandom Generators

Indeed, notions of black-box reduction have been used in other settings
as well, most notably to produce a very ﬁne understanding of the
relations between diﬀerent cryptographic primitives, meaning which
ones can be constructed from each other via black-box constructions.

7.8 Exercises

there exists a mildly explicit

imply hard functions). Suppose that
Problem 7.1 (PRGs
for every m,
(m, 1/m) pseudo-
random generator Gm : {0, 1}d(m) → {0, 1}m. Show that E has
a function f : {0, 1}(cid:4) → {0, 1} with nonuniform worst-case hard-
ness t((cid:6)) = Ω(d−1((cid:6) − 1)). In particular,
if d(m) =O (log m), then
t((cid:6)) = 2Ω((cid:4)) (Hint: look at a preﬁx of Gs output.)

Problem 7.2 (Equivalence of
lower bounds for EXP and
E). Show that E contains a function f : {0, 1}(cid:4) → {0, 1} of cir-
cuit complexity (cid:6)ω(1)
if and only if EXP does. (Hint: consider
f (cid:3)(x1 · · · x(cid:4)) =f (x1 · · · x(cid:4)(cid:3)).)
Does the same argument work if we replace (cid:6)ω(1) with 2(cid:4)Ω(1)
about 2Ω((cid:4))?

? How

Problem 7.3 (Limitations of Cryptographic Generators).

(1) Prove that a cryptographic pseudorandom generator cannot

have seed length d(m) =O (log m).

(2) Prove that cryptographic pseudorandom generators (even
with seed length d(m) =m − 1) imply NP (cid:2) P/poly.
(3) Note where your proofs fail if we only require that G is an

(mc, 1/mc) pseudorandom generator for a ﬁxed constant c.

Problem 7.4 (Deterministic Approximate Counting). Using
the PRG for constant-depth circuits of Theorem 7.29, give deter-
ministic quasipolynomial-time algorithms for the problems below.



<!-- pdf-page: 274 -->
(The running time of your algorithms should be 2poly(log n,log(1/ε)),
where n is the size of the circuit/formula given and ε is the accuracy
parameter mentioned.)

7.8 Exercises

271

(1) Given a constant-depth circuit C and ε >0, approximate
the fraction of inputs x such that C(x) = 1 to within an
additive error of ε.

(2) Given a DNF formula ϕ and ε >0, approximate the number
of assignments x such that ϕ(x) = 1 to within a multiplica-
tive fraction of (1 + ε). You may restrict your attention to
ϕ in which all clauses contain the same number of literals.
(Hint: Study the randomized DNF counting algorithm of
Theorem 2.34.)

Note that these are not decision problems, whereas classes such as
BPP and BPAC0 are classes of decision problems. One of the points
of this problem is to show how derandomization can be used for other
types of problems.

Problem 7.5 (Strong Pseudorandom Generators). By analogy
with strong extractors, call a function G : {0, 1}d → {0, 1}m a (t, ε)
strong pseudorandom generator iﬀ the function G(cid:3)(x) = (x, G(x)) is a
(t, ε) pseudorandom generator.

(1) Show that there do not exist strong cryptographic pseudo-

random generators.

(2) Show that the Nisan–Wigderson generator (Theorem 7.24)

is a strong pseudorandom generator.

(3) Suppose that for all constants α > 0, there is a strong
(m, ε(m)) pseudorandom generator
and fully explicit
G : {0, 1}mα → {0, 1}m. Show that
every language
for
L ∈ BPP, there is a deterministic polynomial-time algo-
R←{0,1}n[A(x) (cid:1)= χL(x)] ≤
rithm A such that for all n, Pr
x
1/2n + ε(poly(n)). That
is, we get a polynomial-time
average-case derandomization even though the seed length
of G is d(m) =m α.



<!-- pdf-page: 275 -->
272 Pseudorandom Generators

(4) Show that for every language L ∈ BPAC0, there is an AC0
R←{0,1}n[A(x) (cid:1)= χL(x)] ≤ 1/n.

algorithm A such that Pr
x

(Warning: be careful about error reduction.)

Problem 7.6 (Private Information Retrieval). The goal of pri-
vate information retrieval is for a user to be able to retrieve an entry of
a remote database in such a way that the server holding the database
learns nothing about which database entry was requested. A trivial
solution is for the server to send the user the entire database, in which
case the user does not need to reveal anything about the entry desired.
We are interested in solutions that involve much less communication.
One way to achieve this is through replication.8 Formally, in a q-server
private information-retrieval (PIR) scheme, an arbitrary database
D ∈ {0, 1}n is duplicated at q noncommunicating servers. On input an
index i ∈ [n], the user algorithm U tosses some coins r and outputs
queries (x1, . . . , xq) =U (i, r), and sends xj to the jth server. The jth
server algorithm Sj returns an answer yj = Sj(xj, D). The user then
computes its output U (i, r, x1, . . . , xq), which should equal Di, the ith
bit of the database. For privacy, we require that the distribution of
each query xj (over the choice of the random coin tosses r) is the same
regardless of the index i being queried.

It turns out that q-query locally decodable codes and q-server PIR
are essentially equivalent. This equivalence is proven using the notion
of smooth codes. A code Enc : {0, 1}n → Σˆn is a q-query smooth code
if there is a probabilistic oracle algorithm Dec such that for every
message x and every i ∈ [n], we have Pr[DecEnc(x)(i) =x i] = 1 and Dec
makes q nonadaptive queries to its oracle, each of which is uniformly
distributed in [ˆn]. Note that the oracle in this deﬁnition is a valid
codeword, with no corruptions. Below you will show that smooth
codes imply locally decodable codes and PIR schemes; converses are
also known (after making some slight relaxations to the deﬁnitions).

8 Another way is through computational security, where we only require that it be compu-
tationally infeasible for the database to learn something about the entry requested.



<!-- pdf-page: 276 -->
7.8 Exercises

273

(1) Show that the decoder for a q-query smooth code is also a

local (1/3q)-decoder for Enc.

(2) Show that every q-query smooth code Enc : {0, 1}n → Σˆn
gives rise to a q-server PIR scheme in which the user and
servers communicate at most q · (log ˆn + log |Σ|) bits for
each database entry requested.

(3) Using the Reed–Muller code, show that there is a polylog(n)-
server PIR scheme with communication complexity
polylog(n) for n-bit databases. That is, the user and servers
communicate at most polylog(n) bits for each database
entry requested. (For constant q, the Reed–Muller code with
an optimal systematic encoding as in Problem 5.4 yields a
q-server PIR with communication complexity O(n1/(q−1)).)

Problem 7.7 (Better Local Decoding of Reed–Muller Codes).
Show that for every constant ε >0, there is a constant γ > 0 such that
there is a local (1/2 − ε)-decoding algorithm for the q-ary Reed–Muller
code of degree d and dimension m, provided that d ≤ γq. (Here we are
referring to unique decoding, not list decoding.) The running time of
the decoder should be poly(m, q).

Problem 7.8 (Hitting-Set Generators). A set Hm ⊂ {0, 1}m is a
(t, ε) hitting set if for every nonuniform algorithm T running in time
t that accepts greater than an ε fraction of m-bit strings, T accepts at
least one element of Hm.

(1) Show that

(m, 1/2) hitting
(cid:8)
RP ⊂
then RP = P.

if,

for

can construct an
then
c DTIME(s(nc)). In particular, if s(m) = poly(m),

every m, we
set Hm in time

s(m) ≥ m,

(2) Show that if there is a (t, ε) pseudorandom generator
Gm : {0, 1}d → {0, 1}m computable in time s, then there is a
(t, ε) hitting set Hm constructible in time 2d · s.



<!-- pdf-page: 277 -->
274 Pseudorandom Generators

(3) Show that if, for every m, we can construct an (m, 1/2) hit-
ting set Hm in time s(m) = poly(m), then BPP = P. (Hint:
this can be proven in two ways. One uses Problem 3.1 and
the other uses a variant of Problem 7.1 together with Corol-
lary 7.64. How do the parameters for general s(m) compare?)
(4) Deﬁne the notion of a (t, k, ε) black-box construction of
hitting set-generators, and show that, when t = ∞, such
constructions are equivalent to constructions of dispersers
(Deﬁnition 6.19).

Problem 7.9 (PRGs versus Uniform Algorithms ⇒ Average–
Case Derandomization). For functions t : N → N and ε : N → [0, 1],
we say that a sequence {Gm : {0, 1}d(m) → {0, 1}m} of is a (t(m), ε(m))
pseudorandom generator against uniform algorithms iﬀ the ensem-
bles {G(Ud(m))}m∈N and {Um}m∈N are uniformly computationally
indistinguishable (Deﬁnition 7.2).

Suppose that we have a mildly explicit (m, 1/m) pseudorandom gen-
erator against uniform algorithms that has seed length d(m). Show that
for every language L in BPP, there exists a deterministic algorithm
A running in time 2d(poly(n)) · poly(n) on inputs of length n such that:

(1) Pr [A(Xn) =L(X n)] ≥ 1 − 1/n2, where Xn

R← {0, 1}n and
L(·) is the characteristic function of L. (The exponent of
2 in n2 is arbitrary, and can be replaced by any constant.)
Hint: coming up with the algorithm A is the “easy” part;
proving that it works well is a bit trickier.

(2) Pr [A(Xn) =L(X n)] ≥ 1 − 1/n2,

for any random variable

Xn distributed on {0, 1}n that is samplable in time n2.

Problem 7.10 (PRGs are Necessary for Derandomization).

(1) Call a function G : {0, 1}d → {0, 1}m a (t, (cid:6), ε) pseudorandom
generator against bounded-nonuniformity algorithms iﬀ for



<!-- pdf-page: 278 -->
7.8 Exercises

275

every probabilistic algorithm T that has a program of length
at most (cid:6) and that runs in time at most t on inputs of
length n, we have

| Pr[T (G(Ud)) = 1] − Pr[T (Um) = 1]| ≤ε.

Consider the promise problem Π whose YES instances
are truth tables of functions G : {0, 1}d → {0, 1}m that are
(m, log m, 1/m) pseudorandom generators against bounded-
nonuniformity algorithms, and whose NO instances are
functions that are not (m, log m, 2/m)
truth tables of
pseudorandom generators against bounded-nonuniformity
algorithms. (Here m and d are parameters determined by
the input instance G.) Show that Π is in prBPP.

(2) Using Problem 2.11, show that if prBPP = prP, then
there is a mildly explicit (m, 1/m) pseudorandom generator
against uniform algorithms with seed length O(log m).
(See Problem 7.9 for the deﬁnition. It turns out that the
hypothesis prBPP = prP here can be weakened to obtain
an equivalence between PRGs vs. uniform algorithms and
average-case derandomization of BPP.)

Problem 7.11 (Composition). For simplicity in this problem, only
consider constant t in this problem (although the results do have
generalizations to growing t = t((cid:6))).

(1) Show that if f : {0, 1}(cid:4) → {0, 1}(cid:4) is a one-way permutation,
then for any constant t, f (t) is a one-way permutation, where
f (t)(x) def= f (f (· · · f
(x))).
*
’

()
t

(2) Show that the above fails for one-way functions. That
is, assuming that there exists a one-way function g, con-
struct a one-way function f which doesn’t remain one
set
for
(Hint:
way under composition.
f (x, y) = 1|g(y)|g(y) unless x ∈ {0(cid:4), 1(cid:4)}.)

|x| = |y| = (cid:6)/2,



<!-- pdf-page: 279 -->
276 Pseudorandom Generators

(3) Show that if G is a cryptographic pseudorandom generator
with seed length d(m) =m Ω(1), then for any constant t, G(t)
is a cryptographic pseudorandom generator. Note where
your proof fails for fully explicit pseudorandom generators
against time mc for a ﬁxed constant c.

→ Z2, A parameterized subspace x + V of Zm

Problem 7.12 (Local List Decoding the Hadamard Code). For
a function f : Zm
2 of
2
dimension d is given by a linear map V : Zd
2 and a shift x ∈ Zm
2 .
2
(We do not require that the map V be full rank.) We write V for
0 +V . For a function f : Zm
2 by
2
f |x+V (y) =f (x + V (y)).

→ Z2, we deﬁne f |x+V : Zd
2

→ Zm

→ Zm

(1) Let c : Zm
2

→ Z2 be a codeword in the Hadamard code
(i.e., a linear function), r : Zm
→ Z2 a received word, V a
2
parameterized subspace of Zm
2 of dimension d, and x ∈ Zm
2 .
Show that if dH (r|x+V , c|x+V ) < 1/2, then c(x) can be
computed from x, V , c|V , and oracle access to r in time
poly(m, 2d) with 2d − 1 queries to r.

(2) Show that for every m ∈ N and ε >0, the Hadamard code
of dimension m has a (1/2 − ε) local list-decoding algorithm
(Dec1, Dec2) in which both Dec1 and Dec2 run in time
poly(m, 1/ε), and the list output by Dec1 has size O(1/ε2).
(Hint: consider a random parameterized subspace V of
dimension 2 log(1/ε) +O (1), and how many choices there
are for c|V .)

(3) Show that Dec2 can be made to be deterministic and run in

time O(m).

Problem 7.13 (Hardcore Predicates). A hardcore predicate for
a one-way function f : {0, 1}(cid:4) → {0, 1}(cid:4) is a poly((cid:6))-time computable
function b : {0, 1}(cid:4) → {0, 1} such that for every constant c, every



<!-- pdf-page: 280 -->
7.8 Exercises

277

nonuniform algorithm A running in time (cid:6)c, we have:

Pr[A(f (U(cid:4))) = b(U(cid:4))] ≤ 1
2

+

1
(cid:6)c ,

for all suﬃciently large (cid:6). Thus, while the one-wayness of f only
guarantees that it is hard to compute all the bits of f s input from its
output, b speciﬁes a particular bit of information about the input that
is very hard to compute (one can’t do noticeably better than random
guessing).

(1) Let Enc : {0, 1}(cid:4) → {0, 1} ˆL be a code such that given
x ∈ {0, 1}(cid:4) and y ∈ [ ˆL], Enc(x)y can be computed in time
poly((cid:6)). Suppose that for every constant c and all suﬃciently
large (cid:6), Enc has a (1/2 − 1/(cid:6)c) local list-decoding algorithm
(Dec1, Dec2) in which both Dec1 and Dec2 run in time
poly((cid:6)). Prove that if f : {0, 1}(cid:4) → {0, 1}(cid:4)
is a one-way
function, then b(x, y) = Enc(x)y is a hardcore predicate for
the one-way function f (cid:3)(x, y) = (f (x), y).

(2) Show that if b : {0, 1}(cid:4) → {0, 1}(cid:4) is a hardcore predicate for
a one-way permutation f : {0, 1}(cid:4) → {0, 1}(cid:4), then for every
m = poly((cid:6)), the following function G : {0, 1}(cid:4) → {0, 1}m is
a cryptographic pseudorandom generator:

G(x) = (b(x), b(f (x)), b(f (f (x))), . . . , b(f (m−1)(x))).

(Hint: show that G is “previous-bit unpredictable.”)

(3) Using Problem 7.12, deduce that if f : {0, 1}(cid:4) → {0, 1}(cid:4) is
a one-way permutation, then for every m = poly((cid:6)), the
following is a cryptographic pseudorandom generator:

Gm(x, r) = ((cid:19)x, r(cid:20), (cid:19)f (x), r(cid:20), (cid:19)f (f (x)), r(cid:20), . . . , (cid:19)f (m−1)(x), r(cid:20)).

Problem 7.14 (PRGs
from 1–1 One-Way Functions). A
random variable X has (t, ε) pseudoentropy at least k if it is (t, ε)
indistinguishable from some random variable of min-entropy at least k.



<!-- pdf-page: 281 -->
278 Pseudorandom Generators

(1) Suppose that X has (t, ε) pseudoentropy at least k and that
Ext : {0, 1}n × {0, 1}d → {0, 1}m is a (k, ε(cid:3))-extractor com-
putable in time t(cid:3). Show that Ext(X, Ud) is an (t − t(cid:3), ε + ε(cid:3))
indistinguishable from Um.

(2) Let f : {0, 1}(cid:4) → {0, 1}(cid:4)(cid:2)

be a one-to-one one-way function
(not necessarily length-preserving) and b : {0, 1}(cid:4) → {0, 1} a
hardcore predicate for f (see Problem 7.13). Show that for
every constant c and all suﬃciently large (cid:6), the random vari-
able f (U(cid:4))b(U(cid:4)) has ((cid:6)c, 1/(cid:6)c) pseudoentropy at least (cid:6) + 1.
(3) (*) Show how to construct a cryptographic pseudorandom
generator from any one-to-one one-way function. (Any seed
length (cid:6)(m) < m is ﬁne.)

7.9 Chapter Notes and References

Other surveys on pseudorandom generators and derandomization
include [162, 209, 226, 288].

Descriptions of classical constructions of pseudorandom generators
(e.g., linear congruential generators) and the batteries of statistical
tests that are used to evaluate them can be found in [245, 341]. Linear
congruential generators and variants were shown to be cryptographi-
cally insecure (e.g., not satisfy Deﬁnition 7.9) in [56, 80, 144, 252, 374].
Current standards for pseudorandom generation in practice can be
found in [51].

The modern approach to pseudorandomness described in this
section grew out of the complexity-theoretic approach to cryptography
initiated by Diﬃe and Hellman [117] (who introduced the concept
of one-way functions, among other things). Shamir [360] constructed
a generator achieving a weak form of unpredictability based on the
conjectured one-wayness of the RSA function [336]. (Shamir’s gener-
ator outputs a sequence of long strings, such that none of the string
can be predicted from the others, except with negligible probability,
but individual bits may be easily predictable.) Blum and Micali [72]
proposed the criterion of next-bit unpredictability (Deﬁnition 7.15)
and constructed a generator satisfying it based on the conjectured



<!-- pdf-page: 282 -->
7.9 Chapter Notes and References

279

hardness of the Discrete Logarithm Problem. Yao [421] gave the
now-standard deﬁnition of pseudorandomness (Deﬁnition 7.3) based
on the notion of computational indistinguishability introduced in the
earlier work of Goldwasser and Micali [176] (which also introduced
hybrid arguments). Yao also proved the equivalence of pseudoran-
domness and next-bit unpredictability (Proposition 7.16), and showed
how to construct a cryptographic pseudorandom generator from any
one-way permutation. The construction described in Section 7.2 and
Problems 7.12 and 7.13 uses the hardcore predicate from the later work
of Goldreich and Levin [168]. The construction of a pseudorandom
generator from an arbitrary one-way function (Theorem 7.11) is due
to H˚astad, Impagliazzo, Levin, and Luby [197]. The most eﬃcient
(and simplest) construction of pseudorandom generators from general
one-way functions to date is in [198, 401]. Goldreich, Goldwasser,
and Micali
[164] deﬁned and constructed pseudorandom functions,
and illustrated their applicability in cryptography. The application of
pseudorandom functions to learning theory is from [405], and their
application to circuit lower bounds is from [323]. For more about
cryptographic pseudorandom generators, pseudorandom functions,
and their applications in cryptography, see the text by Goldreich [157].
Yao [421] demonstrated the applicability of pseudorandom gen-
erators to derandomization, noting in particular that cryptographic
pseudorandom generators imply that BPP ⊂ SUBEXP, and that one
can obtain even BPP ⊂ ˜P under stronger intractability assumptions.
Nisan and Wigderson [302] observed that derandomization only
requires a mildly explicit pseudorandom generator, and showed how
to construct such generators based on the average-case hardness
of E (Theorem 7.24). A variant of Open Problem 7.25 was posed
in [202], who showed that it also would imply stronger results on
hardness ampliﬁcation; some partial negative results can be found
in [214, 320].

The instantiation of the Nisan–Wigderson pseudorandom generator
that uses the parity function to fool constant-depth circuits (Theo-
rem 7.29) is from the earlier work of Nisan [298]. (The average-case
hardness of parity against constant-depth circuits stated in Theo-
rem 7.27 is due Boppana and H˚astad [196].) The ﬁrst unconditional



<!-- pdf-page: 283 -->
280 Pseudorandom Generators

pseudorandom generator against constant-depth circuits was due to
Ajtai and Wigderson [12] and had seed length (cid:6)(m) =m ε (compared
to polylog(m) in Nisan’s generator). Recently, Braverman [81] proved
that any polylog(m)-wise independent distribution fools AC0, provid-
ing a diﬀerent way to obtain polylogarithmic seed length and resolving
a conjecture of Linial and Nisan [265]. The notion of strong pseudo-
random generators (a.k.a. seed-extending pseudorandom generators)
and the average-case derandomization of AC0 (Problem 7.5) are from
[242, 355]. Superpolynomial circuit lower bounds for AC0[2] were
given by [322, 368]. Viola [412] constructed pseudorandom generators
with superpolynomial stretch for AC0[2] circuits that are restricted
to have a logarithmic number of parity gates.

Detailed surveys on locally decodable codes and their applications
in theoretical computer science are given by Trevisan [391] and
Yekhanin [424]. The notion grew out of several diﬀerent lines of work,
and it took a couple of years before a precise deﬁnition of locally decod-
able codes was formulated. The work of Goldreich and Levin [168] on
hardcore predicates of one-way permutations implicitly provided a local
list-decoding algorithm for the Hadamard code. (See Problems 7.12
and 7.13.) Working on the problem of “instance hiding” introduced
in [2], Beaver and Feigenbaum [54] constructed a protocol based on
Shamir’s “secret sharing” [359] that eﬀectively amounts to using the
local decoding algorithm for the Reed–Muller code (Algorithm 7.43)
with the multilinear extension (Lemma 7.47). Blum, Luby, and Rubin-
feld [71] and Lipton [266] introduced the concept of self-correctors
for functions, which allow a one to convert a program that correctly
computes a function on most inputs to one that correctly computes
the function on all inputs.9 Both papers gave self-correctors for group
homomorphisms, which, when applied to homomorphisms from Zn
2
to Z2, can be interpreted as a local corrector for the Hadamard code

9 Blum, Luby, and Rubinfeld [71] also deﬁned and constructed self-testers for functions,
which allow one to eﬃciently determine whether a program does indeed compute a function
correctly on most inputs before attempting to use self-correction. Together a self-tester and
self-corrector yield a “program checker” in the sense of [70]. The study of self-testers gave
rise to the notion of locally testable codes, which are intimately related to probabilistically
checkable proofs [41, 42], and to the notion of property testing [165, 337, 340], which is an
area within sublinear-time algorithms.)



<!-- pdf-page: 284 -->
7.9 Chapter Notes and References

281

(Proposition 7.40). Lipton [266] observed that the techniques of Beaver
and Feigenbaum [54] yield a self-corrector for multivariate polynomials,
which, as mentioned above, can be interpreted as a local corrector for
the Reed–Muller code. Lipton pointed out that it is interesting to apply
these self-correctors to presumably intractable functions, such as the
Permanent (known to be #P-complete [404]), and soon it was realized
that they could also be applied to complete problems for other classes
by taking the multilinear extension [42]. Babai, Fortnow, Nisan, and
Wigderson [43] used these results to construct pseudorandom genera-
tors from the worst-case hardness of EXP (or E, due to Problem 7.2),
and thereby obtain subexponential-time or quasipolynomial-time
simulations of BPP under appropriate worst-case assumptions
(Corollary 7.64, Parts 2 and 3). All of these works also used the
terminology of random self-reducibility, which had been present in
the cryptography literature for a while [29], and was known to imply
worst-case/average-case connections. Understanding the relationship
between the worst-case and average-case complexity of NP (rather
than “high” classes like EXP) is an important area of research; see the
survey [74].

Self-correctors for multivariate polynomials that can handle a
constant fraction of errors (as in Theorem 7.42) and fraction of errors
approaching 1/2 (as in Problem 7.7) were given by Gemmell et al. [149]
and Gemmell and Sudan [150], respectively. Babai, Fortnow, Levin, and
Szegedy [41] reformulated these results as providing error-correcting
codes with eﬃcient local decoding (and “local testing”) algorithms.
Katz and Trevisan [239] focused attention on the exact query complex-
ity of locally decodable codes (separately from computation time), and
proved that locally decodable codes cannot simultaneously have the
rate, distance, and query complexity all be constants independent of
the message length. Constructions of 3-query locally decodable codes
with subexponential blocklength were recently given by Yekhanin [423]
and Efremenko [128]. Private Information Retrieval (Problem 7.6)
was introduced by Chor, Goldreich, Kushilevitz, and Sudan [99].
Katz and Trevisan [239] introduced the notion of smooth codes and
showed their close relation to both private information retrieval and
locally decodable codes (Problem 7.6). Recently, Saraf, Kopparty,



<!-- pdf-page: 285 -->
282 Pseudorandom Generators

and Yekhanin [249] constructed the ﬁrst locally decodable codes with
sublinear-time decoding and rate larger 1/2.

Techniques for Hardness Ampliﬁcation (namely, the Direct Product
Theorem and XOR Lemma) were ﬁrst described in oral presentations of
Yao’s paper [421]. Since then, these results have been strengthened and
generalized in a number of ways. See the survey [171] and Section 8.2.3.
The ﬁrst local list-decoder for Reed–Muller codes was given by Arora
and Sudan [35] (stated in the language of program self-correctors). The
one in Theorem 7.56 is due to Sudan, Trevisan, and Vadhan [381], who
also gave a general deﬁnition of locally list-decodable codes (inspired
by a list-decoding analogue of program self-correctors deﬁned by Ar
et al. [30]) and explicitly proved Theorems 7.60, 7.61, and 7.62.

The result that BPP = P if E has a function of nonuniform worst-
case hardness s((cid:6)) = 2Ω((cid:4)) (Corollary 7.64, Part 1) is from the earlier
work of Impagliazzo and Wigderson [215], who used derandomized
versions of the XOR Lemma to obtain suﬃcient average-case hardness
for use in the Nisan–Wigderson pseudorandom generator. An optimal
construction of pseudorandom generators from worst-case hard func-
tions, with seed length d(m) =O (s−1(poly(m))) (cf., Theorem 7.63),
was given by Shaltiel and Umans [356, 399].

For more background on AM, see the Notes and References of
Section 2. The ﬁrst evidence that AM = NP was given by Arvind
and K¨obler [37], who showed that one can use the Nisan–Wigderson
generator with a function that is (2Ω((cid:4)), 1/2 − 1/2Ω((cid:4)))-hard for non-
deterministic circuits. Klivans and van Melkebeek [244] observed that
the Impagliazzo–Wigderson pseudorandom generator construction
is “black box” and used this to show that AM can be deran-
domized using functions that are worst-case hard for circuits with
an NP oracle (Theorem 7.68). Subsequent work showed that one
only needs worst-case hardness against a nonuniform analogue of
NP ∩ co-NP [289, 356, 357].

Trevisan [389] showed that black-box pseudorandom generator
constructions yield randomness extractors, and thereby obtained the
extractor construction of Theorem 7.73. This surprising connection
between complexity-theoretic pseudorandomness and information-
from
theoretic pseudorandomness sparked much subsequent work,



<!-- pdf-page: 286 -->
7.9 Chapter Notes and References

283

which the uniﬁed theory presented in this survey emerged. The fact
that black-box hardness ampliﬁers are a form of locally list-decodable
codes was explicitly stated (and used to deduce lower bounds on
advice length) in [397]. The use of black-box constructions to classify
and separate cryptographic primitives was pioneered by Impagliazzo
and Rudich [213]; see also [326, 330].

Problem 7.1 (PRGs imply hard functions) is from [302]. Problem 7.2
is a special case of the technique called “translation” or “padding”
in complexity theory.
Problem 7.4 (Deterministic Approximate
Counting) is from [302]. The fastest known deterministic algorithms
for approximately counting the number of satisfying assignments to
a DNF formula are from [280] and [178] (depending on whether the
approximation is relative or additive, and the magnitude of the error).
The fact that hitting set generators imply BPP = P (Problem 7.8)
was ﬁrst proven by Andreev, Clementi, and Rolim [27]; for a more
direct proof, see [173]. Problem 7.9 (that PRGs vs. uniform algorithms
imply average-case derandomization) is from [216]. Goldreich [163]
showed that PRGs are necessary for derandomization (Problem 7.10).
The result that one-to-one one-way functions imply pseudorandom
generators is due to Goldreich, Krawczyk, and Luby [167]; the proof
in Problem 7.14 is from [197].

For more on Kolmogorov complexity, see [261]. In recent years,
connections have been found between Kolmogorov complexity and
derandomization; see [14]. The tighter equivalence between circuit size
and nonuniform computation time mentioned after Deﬁnition 7.1 is due
to Pippenger and Fischer [311]. The 5n − O(n) lower bound on circuit
size is due to Iwama, Lachish, Morizumi, and Raz [218, 254]. The
fact that single-sample indistinguishability against uniform algorithms
does not imply multiple-sample indistinguishability unless we make
additional assumptions such as eﬃcient samplability (in contrast to
Proposition 7.14), is due to Goldreich and Meyer [169]. (See also [172].)



<!-- pdf-page: 287 -->
8

Conclusions

8.1 A Uniﬁed Theory of Pseudorandomness

In the course of this survey, we have seen that a wide variety of
“pseudorandom objects” are very closely related, and indeed almost
equivalent when viewed appropriately: list-decodable codes, averag-
ing samplers, expander graphs, randomness extractors, (black-box)
pseudorandom generator constructions, and hardness ampliﬁers. The
power of these connections comes from the fact they allow us to
translate intuitions and techniques that are very natural for one of
these objects to others where they have been might be diﬃcult to
discover. Indeed, we have seen several examples of this, such the
use of randomness extractors to construct near-optimal samplers
(Problem 6.5), the use of Parvaresh–Vardy codes to construct bipartite
expanders (Theorem 5.35) and lossless condensers (Theorem 6.34), and
the use of the Nisan–Wigderson pseudorandom generator construction
to construct extractors (Theorem 7.73).

Table 8.1 reviews the connections between these objects, by putting
them in our list-decoding framework. Recall that we can view each
of the objects as a function Γ : [N ] × [D] → [M ] and can characterize
their properties by bounding the sizes of sets of the form LISTΓ(T, α) =
{x : Pry[Γ(x, y) ∈ T ] > α}, where T ⊂ [M ]. (When α = 1, we change

284



<!-- pdf-page: 288 -->
8.1 A Uniﬁed Theory of Pseudorandomness

285

0
3
.
5

3
2
.
6

2
7
.
7

3
3
.
5

.

b
o
r
P

3
3
.
6

7
.
4

,
)
)
δ
/
1
(
g
o
l
,
ε
/
1
(
y
l
o
p
=
D

,

N
δ
=
K

e
r
a
c

t
’
n
o
d

γ
n
≤
)
ε
/
1
,

n
g
o
l
(
y
l
o
p
=

t

=
k

)
e
c
i
v
d
a
/
w

l
a
c
o
l
(

K
≤

K
≤

|
)
ε
+
)
T
(
µ

|
)
ε
+
)
T
(
µ

,

T
(
T
S
I
L

,

T
(
T
S
I
L

)
)
δ
/
1
(
g
o
l

+
m
(
O
=
n

,
)
)
ε
/
n
(
g
o
l
(
O
=
d

e
r
a
c

t
’
n
o
d

K
(cid:1)

|
)
ε
+
)
T
(
µ

,

T
(
T
S
I
L

]

n
γ
,
)
n
(
g
o
l
y
l
o
p

[

∈
)

m
(
O
=
k

,

m
/
1
=
ε

)

m
(
y
l
o
p
=

t

K
≤

|
)
ε
+
)
T
(
µ

,

T
(
T
S
I
L

N
=
M

,
2
/
N
=
K

,
)
)
δ
/
1
(
g
o
l
,
ε
/
1
(
y
l
o
p
=
D

,

N
δ
=
K

e
r
a
c

t
’
n
o
d

]

γ
n

,
)
n
(
g
o
l
y
l
o
p

[

∈
)

m
(
y
l
o
p
=

t

=
k

)
e
c
i
v
d
a
/
w

l
a
c
o
l
(

,
)
1
(
Ω
+
1
=
A

,
)
1
(
O
=
D

e
r
a
c

t
’
n
o
d

]

n
γ
,
)
n
(
g
o
l
y
l
o
p

[

∈
)

m
(
O
=
k

)
)
δ
/
1
(
g
o
l

+
m
(
O
=
n

,
)
)
ε
/
n
(
g
o
l
(
O
=
d

e
r
a
c

t
’
n
o
d

K
≤

|
)
ε
+
)
T
(
µ

,

T
(
T
S
I
L

⇒
K
D
)
ε
−
1
(
<

|

T

K
<

|
)
1
,

T
(
T
S
I
L

⇒
M

)
ε
−
1
(
<

|

T

K
<

|
)
1
,

T
(
T
S
I
L

⇒
K
A
<

|

T

|

|

|

|

|

|

|

|

|

|

y
)
x
(
p
m
a
S

)
ε
,
δ
(

s
r
e
l
p
m
a
s

g
n
i
g
a
r
e
v
a

)
y
,

x
(
t
x
E

)
y
(

x
G

r
b
n

h
t
’
y

x

f
o

y
)
x
(
p
m
a
S

)
y
,

x
(
n
o
C

s
G
R
P
x
o
b
-
k
c
a
l
b

s
r
e
d
n
a
p
x
e

,

)
A
K
=
(

)
ε
,
δ
(

s
r
e
s
n
e
d
n
o
c

)
s
s
e
l
s
s
o
l
(

s
r
e
l
p
m
a
s

g
n
i
t
t
i
h

d
+
k

ε

→
k

s
r
o
t
c
a
r
t
x
e

)
ε
,
k
,
t
(

)
ε
,
k
(

s
e
d
o
c

e
l
b
a
d
o
c
e
d
-
t
s
i
l

x
o
b
-
k
c
a
l
b

)
ε
,
k
,
t
(

s
r
e
ﬁ
i
l
p
m
a

s
s
e
n
d
r
a
h

)
n
(
y
l
o
p
=
K

,
)
n
(
O
=
q
D
=
M

4
7
.
7

,
)
n
(
y
l
o
p
=
q
D
=
M

,
2
=
q

,
)
n
g
o
l
(
O
=
d

)
ε
/
1
,

n
g
o
l
(
y
l
o
p
=

t

K
≤

|
)
ε
+
)
T
(
µ

,

T
(
T
S
I
L

|

⇒

}
)
y
r
,
y
(
{
=

T

)
)
y
(

f

p
m
A

,
y
(

r
o
f

}
α
>

]

T
∈
)
y
,

x
(
Γ

[
y
r
P

:

x
{
=
)
α

,

T
(
Γ
T
S
I
L

f
o

s
e
z
i
s

g
n
i
d
n
u
o
b

y
b

]

M

[

→

]

D

[

×

]

N

[

:

Γ

s
t
c
e
j
b
O

m
o
d
n
a
r
o
d
u
e
s
P

g
n
i
r
u
t
p
a
C

.
1
.
8

e
l
b
a
T

.

k

2
=
K
d
n
a

,

2
=
D

,

d

m
2
=
M

,

n

2
=
N

,
l
a
u
s
u

s
A

.
t
n
a
t
s
n
o
c

e
v
i
t
i
s
o
p

l
l
a
m

s

y
l
i
r
a
r
t
i
b
r
a

a

s
e
t
o
n
e
d

γ

r
e
t
e
m
a
r
a
p

e
h
T

.
]

M

[

⊂
T

.

p
o
r
P

9
2
.
5

s
r
e
t
e
m
a
r
a
P
d
r
a
d
n
a
t
S

i

e
m
T
g
n
i
d
o
c
e
D

m
e
l
b
o
r
P
g
n
i
d
o
c
e
D
-
t
s
i
L

)
y
,

x
(
Γ

t
c
e
j
b
O

,
)
1
(
Ω
=
ε

,
)
1
(
O
=
q

)
ε
/
1
,

n
(
y
l
o
p

⇒

}
)
y
r
,
y
(
{
=

T

)
y
)
x
(
c
n
E

,
y
(

)

K
,
ε
−
q
/
1
−
1
(



<!-- pdf-page: 289 -->
286 Conclusions

the inequality to an equality.) Other objects we have encountered,
such as dispersers (Deﬁnition 6.19), black-box hitting-set generator
constructions (Problem 7.8), and lossy condensers (Deﬁnition 6.32)
can also be cast in the framework, but we leave this as an exercise.

In addition to illustrating the connections between the objects,
Table 8.1 also brings out their diﬀerences. In some cases α = µ(T ) +ε,
and in other cases α = 1. In some cases (samplers, extractors, PRG con-
structions), we consider all subsets T ⊂ [M ], and in other cases (codes,
hardness ampliﬁers, expanders, condensers), we only consider T that
are small and possibly have some additional structure, like being the
graph of a received word. (Typically, the only way the graph structure
is used is to determine that the size of T is D.) In some cases, we want
eﬃcient algorithms to construct LIST(T, α) (even polylogarithmic-time
local decoding algorithms), and in others, all we care about is its size.
The most common parameter ranges also vary quite widely among
the objects. The typical relation between M and N ranges from loga-
rithmic (codes) to polylogarithmic (hardness ampliﬁers) to a constant
power (samplers) to a constant multiplicative factor (expanders).
(Extractors, PRG constructions, and condensers all consider the full
range between polylogarithmic and a constant power.) The typical
value of D ranges from being a constant independent of N (expanders),
to being logarithmic in N (codes), to being polylogarithmic in N
(extractors, condensers, PRG constructions, hardness ampliﬁers).
Despite these diﬀerences, we have seen that the connections are
nevertheless quite powerful, and ideas or techniques developed for one
of these objects are often useful for the others.

The uniﬁed framework of Table 8.1 opens up a tantalizing possibil-
ity that we can also have a uniﬁed construction of all of these objects.
In what follows, we will argue that this is possible ignoring explic-
itness/eﬃciency considerations (including local
list-decoding). The
bounds will be stated in terms of the tails of the binomial distribution:

Deﬁnition 8.1 (tails of binomial distributions). For
µ, α ∈ (0, 1), deﬁne

t ∈ N,

Bin(t, µ, α) = Pr

Xi > α

,

(cid:25)

(cid:24)

1
t

t(cid:3)

i=1



<!-- pdf-page: 290 -->
8.1 A Uniﬁed Theory of Pseudorandomness

287

where the Xis are iid {0, 1}-valued random variables such that
Pr[Xi = 1] = µ, and deﬁne

Bin(t, µ, 1) = Pr

Xi = 1

= µt.

(cid:25)

(cid:24)

1
t

t(cid:3)

i=1

With this deﬁnition, we can give the following uniﬁed construction:

Theorem 8.2 (nonconstructive uniﬁed pseudorandom object).
For every N, M, D ∈ N, there exists a function Γ : [N ] × [D] → [M ]
such that for every T ⊂ [M ] and every α ∈ (0, 1], we have

|LISTΓ(T, α)|
(cid:6)

≤ min

K ∈ N :

(cid:14)

N
K

(cid:15)

(cid:14)

·

(cid:15)

M
|T |

· Bin(D, µ(T ), α)K ≤

1
4K2|T |2

.

We leave the proof of Theorem 8.2 as an exercise and instead show
how many of the nonconstructive bounds we’ve seen for various pseu-
dorandom objects would simultaneously hold for the Γ of Theorem 8.2
by setting parameters appropriately:

• The nonconstructive bounds for expanders (Theorem 4.4)
can be obtained by setting M = N , α = 1, µ = µ(T ),
K = |T |/(D − 2) (ignoring round-oﬀ errors), and noting that

(cid:14)

(cid:15)

(cid:14)

(cid:15)

N
K

N
|T |

·

(cid:14)

≤

(cid:14)

· Bin(D, µ, 1)K

(cid:15)

K

(cid:14)

·

N e
K

N e
|T |
(cid:15)

(cid:15)|T |

· µDK

·

K

=

(D − 2) · e
µ
= ((D − 2)eD−1µ)K
< 1/(4K2|T |2),

(cid:15)

(D−2)·K

(cid:14)

e
µ

· µD·K

provided µ is suﬃciently small. Thus, by Proposition 5.33,
Γ deﬁnes a (γN, (D − 2)) vertex expander for a suﬃciently
small γ.

 


<!-- pdf-page: 291 -->
288 Conclusions

N
βN
• For

(cid:2)

is

More generally, we see that for any constants γ, A, D > 0
and suﬃciently large N = M , Γ will be a (γN, A)
expander provided that D > (H(γ) +H (γA))/γ log(1/γA),
where H(x) =x log(1/x) + (1 − x) log(1/(1 − x))
the
binary entropy function.1 (To see this, use the fact that
(cid:1)

= 2(H(β)+o(1))·N as N → ∞.)
the nonconstructive bound on extractors

(Theo-
rem 6.14) and averaging samplers, we set α = µ(T ) +ε
≤ 2M , and
and use the bounds
Bin(D, µ(T ), µ(T ) +ε) ≤ exp(−Ω(Dε2)) (by the Chernoﬀ
Bound of Theorem 2.21). Then the condition of Theo-
rem 8.2 is satisﬁed provided that D ≥ (c/ε2) · log(N/K) and
M ≤ ε2KD/c for a suﬃciently large constant c.

≤ (N e/K)K,

M
T

N
K

(cid:1)

(cid:2)

(cid:1)

(cid:2)

To get the “strong” forms of pseudorandom objects, where
Γ(x, y) = (y, Γ(cid:3)(x, y)) for some function Γ(cid:3), we need to consider the
tails of sums of independent, but not necessarily identically distributed,
binomial random variables:

Deﬁnition 8.3 (tails of Poisson binomial distributions). For
t, N, µ, α ∈ (0, 1), deﬁne

PBin(t, µ, α, η) = sup

Pr

(Y1,...,Yt)

(cid:25)

Yi > α

,

(cid:24)

1
t

t(cid:3)

i=1

and

PBin(t, µ, 1, η) = sup

Pr

(Y1,...,Yt)

(cid:25)

Yi = 1

= Bin(t, µ, 1),

(cid:24)

1
t

t(cid:3)

i=1

where the suprema are taken over all sequences of
(cid:4)
Bernoulli random variables Y1, . . . , Yt such that (1/t) ·
and additionally E[Yi] is an integer multiple of η for every i.

independent
t
i=1 E[Yi] ≤ µ,

1 The discussion after Theorem 4.4 states a slightly stronger result, only requiring D >
(H(γ) +H (γA))/(H(γ) − γAH(1/γ)), but this is based on choosing a graph that is the
union of D random perfect matchings, which does indeed have slightly better expansion
properties than the model we are using now, of choosing D random neighbors for each left
vertex.



<!-- pdf-page: 292 -->
8.1 A Uniﬁed Theory of Pseudorandomness

289

Theorem 8.4 (nonconstructive uniﬁed pseudorandom object).
For every N, q, D ∈ N, there exists a function Γ(cid:3) : [N ] × [D] → [q] such
that if we deﬁne Γ(x, y) = (y, Γ(cid:3)(x, y)), then for every T ⊂ [D] × [q]
and every α ∈ (0, 1], we have

|LISTΓ(T, α)|
(cid:6)

≤ min

K ∈ N :

(cid:15)

(cid:15)

(cid:14)

·

(cid:14)

N
K

Dq
|T |

· PBin(D, µ(T ), α, 1/q)K ≤

1
4K2|T |2

.

for

• Nonconstructive bounds

strong vertex expanders,
hitting samplers, and lossless condensers
(matching the
bounds for the non-strong ones) follow by noting that
PBin(n, µ, 1, η) ≤ Bin(n, µ, 1).
Indeed, writing µi
for the
expectation of Bernoulli random variable Yi, then

(cid:24)

Pr

1
t

t(cid:3)

i=1

(cid:25)

Yi = 1

=

t(cid:5)

i=1

µi ≤

(cid:20)

1
t

t(cid:3)

i=1

(cid:21)t

µi

≤ µt,

from the

the

second-to-last

where
Arithmetic Mean–Geometric Mean Inequality.
bounds

• Nonconstructive

inequality follows

• Nonconstructive bounds

for

strong

extractors

list-decodable codes

and
for
averaging samplers (matching the bounds for the non-
strong ones) follow because the Chernoﬀ Bound (Theo-
rem 2.21) also applies to nonidentical random variables:
PBin(D, µ(T ), µ(T ) +ε, η ) ≤ exp(−Ω(Dε2)) for every η > 0.
(The-
orem 5.8) follow because the list-decodability of codes
involves taking T to be the graph of a received word
(cf. Proposition
and
and
PBin(D, 1/q, 1 − δ, 1/q) =q Hq(δ,D)·D/qD. To see the latter,
let E[Yi] =m i/q for mi ∈ N such that
i mi ≤ D. soY i can
be viewed as the indicator for the event the R(i) ∈ {1, . . . , mi}
for a uniformly random received word R : [D] → [q], and
i Yi > 1 − δ] is the probability that the graph G(R) =
Pr[
{(i, r(i)) : i ∈ [D]} of the received word R intersects the set

hence µ(T ) = 1/q,

5.29)

(cid:4)

(cid:4)

 


<!-- pdf-page: 293 -->
290 Conclusions

T (cid:3) = {(i, j) :i ∈ [D], j ≤ mi} in more than (1 − δ)D posi-
tions. For a set S ⊂ T (cid:3), the probability that G(R) ∩ T (cid:3) = S
is at most (1/q)|S| · (1 − 1/q)D−|S|. (This is exactly the
probability in case S contains only pairs (i, j) with D
distinct values of i, otherwise the probability is zero.) Thus,

(cid:24)

(cid:3)

i

Pr

Yi > 1 − δ

≤

(cid:15)

(1/q)s · (1 − 1/q)D−s

(cid:25)

(cid:14)(cid:4)

(cid:3)

s>(1−δ)D

(cid:3)

i mi
s
(cid:14)

≤ 1
qD

·

s>(1−δ)D

(cid:15)

(q − 1)s

D
s

=

qHq(δ,D)·D
qD

.

(cid:1)

(cid:2)

(cid:1)

(cid:1)

N
K

Dq
D

Now, given this bound on PBin(·) and Proposition 5.29,
Theorem 8.4 gives us a (δ, K) list-decodable code Enc :
(cid:2)
· ( qHq (δ,D)·D
·
)K ≤ 1
[N ] → [q]D provided that
4K2D2 .
qD
(cid:2)
(cid:2)
(cid:1)
≤ (eq)D, we see
≤ N K and
Using the bounds
that we get a list-decodable code provided that the rate
than Hq(δ, D) − O(1/K) −
ρ = log N/D log q
O((log KD)/(KD log q). This matches the nonconstructive
bound for list-decodable codes (Theorem 5.8) up to the
dependence of the error term on the list size K.

smaller

Dq
D

N
K

is

Given the above, a natural
pseudorandomness is the following:

long-term goal

for the theory of

Open Problem 8.5. Can we give explicit constructions of functions
Γ that nearly match the bounds of Theorems 8.2 and 8.4? Can this be
done with eﬃcient (local) list-decoding algorithms?

8.2 Other Topics in Pseudorandomness

In this section, we survey some additional topics in the theory of
pseudorandomness that we did not cover in depth, each of which
could merit at least an entire section on its own. Sections 7.2 and 7.9



<!-- pdf-page: 294 -->
8.2 Other Topics in Pseudorandomness

291

contained a detailed survey of cryptographic pseudorandomness, so we
do not discuss it again here.

8.2.1 Pseudorandomness for Space-Bounded Computation

As discussed in Section 4.4, unlike for BPP and RP, we do know
very nontrivial derandomizations RL (and BPL). These deran-
domizations are obtained constructions of pseudorandom generators
G : {0, 1}d → {0, 1}m such that no randomized (log m)-space algorithm
can distinguish G(Ud) from Um. In order to get derandomizations that
are correct on every input x, we require pseudorandom generators
that fool nonuniform space-bounded algorithms. On the other hand,
since randomized space-bounded algorithms get their random bits
as a stream of coin tosses, we only need to fool space-bounded
distinguishers that read each of their input bits once, in order. Thus,
we consider distinguishers that are (oblivious, read-once) branching
programs, which maintain a state si ∈ [w] after reading i input bits,
and determine the next state si+1 ∈ [w] as a function of si and the
(i + 1)th input bit. The number w of available states at each time
step is called the width of the branching program, and corresponds to
a space bound of log w bits. A generator G : {0, 1}d(m) → {0, 1}m that
is computable in space O(d(m)) and such that G(Ud(m)) cannot be
distinguished from Um by oblivious, read-once branching programs of
width m implies that BPL ⊂ DSPACE(O(d(poly(m)))).

The fact that pseudorandom generators imply lower bounds
(Problem 7.1) applies to this context too, but fortunately we do know
exponential width lower bounds for oblivious, read-once branching pro-
grams (e.g., computing the inner-product modulo 2 of two (cid:6)-bit strings
requires width 2Ω((cid:4))). On the other hand, we cannot simply plug
such lower bounds into the Nisan–Wigderson generator construction
(Theorem 7.24), because the reductions used do not preserve the read-
once property (and we do not know superpolynomial lower-bounds for
branching programs that can read each input bit many times).

Nevertheless, a series of papers starting with Ajtai, Koml´os, and
[11] have given unconditional pseudorandom generators
Szemer´edi
for space-bounded computation. The pseudorandom generator of



<!-- pdf-page: 295 -->
292 Conclusions

Nisan [299] uses a seed of length O(log2 m) to produce m bits that are
pseudorandom to oblivious, read-once branching programs of width
m. At ﬁrst, this only seems to imply that RL ⊂ L2, which already
follows from Savitch’s Theorem [349] that NL ⊂ L2. Nevertheless,
Nisan’s generator and its additional properties has been used in more
sophisticated ways to obtain highly nontrivial derandomizations of
RL. Speciﬁcally, Nisan [300] used it to show that every problem in RL
can be solved simultaneously in polynomial time and O(log2 n) space,
and Saks and Zhou [344] used it to prove that RL ⊂ L3/2. Another
important pseudorandom generator for space-bounded computation
is that of Nisan and Zuckerman [303], which uses a seed of length
O(log m) to produce logk m bits that are pseudorandom to oblivious,
read-once branching programs of width m. None of these results have
been improved in nearly two decades.

However, substantially better generators have been constructed
for restricted classes of oblivious read-once branching programs.
Speciﬁcally, there are pseudorandom generators or hitting-set gen-
length ˜O(log m)
erators (see Problem 7.8) stretching a seed of
to m bits that fool combinatorial rectangles (which check mem-
bership in a “rectangle” S1 × S2 × · · · × Sm/ log m, where
each
Si ⊂ {0, 1}log m) [136, 264, 31, 271, 179], branching programs of
width 2 and 3 [345, 73, 363, 179], constant-width regular branching
programs (where the transition function at each layer is regu-
lar) [82, 84], and constant-width permutation branching programs
(where each input string induces a permutation of the states at each
layer) [338, 250, 113, 373]. However, the following remains open:

Open Problem 8.6.
Is there an explicit pseudorandom generator
G : {0, 1}o(log2 m) → {0, 1}m whose output distribution is pseudorandom
to oblivious, read-once branching programs of width 4?

8.2.2 Derandomization vs. Lower Bounds

Derandomization from Uniform Assumptions. The construc-
tion of pseudorandom generators we have seen (Theorem 7.63) requires
nonuniform circuit lower bounds for functions in E, and it is of interest



<!-- pdf-page: 296 -->
8.2 Other Topics in Pseudorandomness

293

to ﬁnd constructions that only require uniform hardness assumptions.
One way to obtain such results is to show that uniform hardness
assumptions imply nonuniform assumptions. Indeed, the Karp–Lipton
Theorems in complexity theory [235] show that certain strong uniform
lower bounds imply nonuniform lower bounds. For example,
if an
EXP-complete problem cannot be solved by a uniform algorithm in
the second level of the polynomial-time hierarchy (like NP but with
two nondeterministic quantiﬁers, cf. Section 3.3), then it also cannot be
solved by polynomial-sized circuits. Subsequent strengthenings of the
Karp–Lipton Theorem (based on the theory of interactive proofs) show
that if EXP (cid:1)= MA (where MA is like NP but allows probabilistic ver-
iﬁcation of witnesses), then EXP (cid:2) P/poly [42]; consequently one gets
pseudorandom generators with arbitrary polynomial stretch (secure for
inﬁnitely many input lengths) under the assumption EXP (cid:1)= MA [43].
Assuming the Karp–Lipton Theorem cannot be further improved
(e.g., to show EXP (cid:2) P/poly ⇔ EXP (cid:1)= BPP),
from a uniform
assumption such as EXP (cid:1)= BPP, we can only hope to construct
pseudorandom generators that are secure against uniform distinguish-
ers (because pseudorandom generators secure against nonuniform
distinguishers imply nonuniform lower bounds, by Problem 7.1).
In the context of cryptographic pseudorandom generators, uniform
results were typically developed together with or soon after the cor-
responding nonuniform results. Indeed, analogously to Theorem 7.11,
it is known that cryptographic pseudorandom generators that are
secure against uniform distinguishers exist if and only if there exist
one-way functions that are hard to invert by uniform algorithms [197].
For noncryptographic, mildly explicit pseudorandom generators as
in Theorem 7.63 and Corollary 7.64, an obstacle is that black-box
constructions (Deﬁnition 7.65) require nonuniform advice in the
reduction. (See discussion at the end of Section 7.7.2. This obstacle
is avoided in the case of cryptographic pseudorandom generators,
because the appropriate deﬁnition of black-box construction from
one-way functions gives the reduction oracle access to the one-way
function in addition to the distinguisher, since one-way functions are
supposed to be eﬃciently computable by deﬁnition.)



<!-- pdf-page: 297 -->
294 Conclusions

Thus, we must turn to non-black-box constructions, in which we
make more use of the fact that the hard function f is computable in E
and/or the fact that the distinguisher T is computable by an eﬃcient
probabilistic algorithm, not just to deduce that Gf is mildly explicit
and RedT is eﬃcient. In fact, f and T need not even be used as
oracles; we can make use of the code of the programs computing these
functions (e.g., to reduce f to an E-complete problem). While at ﬁrst
it may seem diﬃcult to take advantage of non-black-box constructions,
this was eventually accomplished by Impagliazzo and Wigderson [216].
They showed that if EXP (cid:1)= BPP, then there are mildly explicit pseu-
dorandom generators with polynomial stretch that are secure against
uniform probabilistic distinguishers (for inﬁnitely many input lengths),
and hence BPP has subexponential-time average-case derandomiza-
tions (by Problem 7.9). (See [397] for a precise statement regarding the
construction of pseudorandom generators.) This is a uniform analogue
of the “low-end” nonuniform result in Corollary 7.64 (Item 3). Ana-
logues for the high-end bounds (Items 1, 2) remain open. For example:

Open Problem 8.7. Does EXP (cid:1)⊂ BPSUBEXP imply mildly
explicit generators G : {0, 1}polylog(m) → {0, 1}m whose input is pseu-
dorandom to every uniform probabilistic algorithm running in time m
(for inﬁnitely many m)?

Such a result is known if we replace EXP by PSPACE [397].
For derandomizing AM instead of BPP, both high-end and
low-end uniform results have been obtained [195, 358]. These results
utilize hard functions in E, unlike the nonuniform results which only
require hard functions in NE ∩ co-NE (cf. Theorem 7.68).

Derandomization Implies Circuit Lower Bounds. Since uni-
form hardness assumptions and PRGs against uniform distinguish-
ers only seem to imply average-case derandomizations (Problem 7.9),
it is tempting to conjecture that worst-case derandomizations imply
(or are even equivalent to) nonuniform circuit lower bounds. A result
of this type was ﬁrst given implicitly by Buhrman, Fortnow, and



<!-- pdf-page: 298 -->
8.2 Other Topics in Pseudorandomness

295

Thierauf [86] and then explicitly and in stronger form by Impagli-
azzo, Kabanets, and Wigderson [212]. Speciﬁcally, these results show
that if MA (like NP, but with probabilistic veriﬁcation of witnesses)
can be derandomized (e.g., MA = NP or even MA ⊂ NSUBEXP),
then NEXP (cid:2) P/poly. Derandomization of prBPP implies deran-
domization of MA, so this also implies that if prBPP = prP or
even prBPP ⊂ prSUBEXP, then NEXP (cid:2) P/poly. This result falls
short of giving a converse to Corollary 7.64 (Item 3) because the circuit
lower bounds are for NEXP rather than EXP. (Corollary 7.64, as well
as most of the other derandomization results we’ve seen, apply equally
well to prBPP as to BPP.) In addition, the result does not give expo-
nential circuit lower bounds even if we assume full derandomization
(prBPP = prP). However, Santhanam [347] shows that prBPP =
prP implies that for every constant k, there is a language in NP that
does not have circuits of size nk, which can be viewed as a “scaled down”
version of the statement that NE requires circuits of size 2Ω(n).2

Thus, the following remain open:

Open Problem 8.8. Does prBPP = prP imply E (cid:2) P/poly
(equivalently EXP (cid:2) P/poly, by Problem 7.2)?

Open Problem 8.9. Does prBPP = prP imply that NEXP has a
problem requiring nonuniform boolean circuits of size 2(cid:4)Ω(1)
on inputs
of length (cid:6)?

By the result of [212] and Corollary 2.31, ﬁnding a determin-
istic polynomial-time algorithm for the prBPP-complete problem
[+ε]-Approx Circuit Average implies superpolynomial circuit lower
bounds for NEXP. Unfortunately, we do not know a wide variety
of natural problems that are complete for prBPP (unlike NP).
Nevertheless, Kabanets and Impagliazzo [227] showed that ﬁnding
a deterministic polynomial-time algorithm for Polynomial Identity

2 Indeed, by a standard “padding” or “translation” argument in complexity theory, if for
some constant k, every language in NP had circuits of size nk, then every language in
NE would have circuits of size 2o(n).



<!-- pdf-page: 299 -->
296 Conclusions

Testing implies that either NEXP (cid:2) P/poly or that the Permanent
does not have polynomial-sized arithmetic circuits, both of which
are long-standing open problems in complexity theory. (See [1] for a
simpler and somewhat stronger proof.) Polynomial Identity Testing is
in co-RP, by Theorem 2.12, but is not known to be complete for any
randomized complexity class. Of course, it is also of interest to ﬁnd
additional complete problems for prBPP:

Open Problem 8.10. Find combinatorial or algebraic complete
problems for any randomized complexity classes (e.g., prBPP, prRP,
prAM, BPP, RP, ZPP).

Derandomizations of prAM are also known to imply circuit lower
bounds, which are stronger than what the aforementioned results give
from derandomizations of prBPP in that they either yield exponential-
size bounds [38] or give lower bounds for nondeterministic circuits [39].
One interesting interpretation of many of these results is to show
that if derandomization is possible via any means (for all of prBPP or
prAM), then it can be done in a canonical way — via pseudorandom
generators (because these results show that derandomization implies
circuit lower bounds, which in turn imply pseudorandom generators
via Theorem 7.63). A recent work by Goldreich [163] directly proves
equivalences between various kinds of derandomizations of prBPP
(e.g., worst-case or average-case) and various forms of pseudoran-
dom generators, without going through circuit lower bounds. (See
Problem 7.10.)

Another reason for the interest in these results is that they suggest
derandomization as a potential approach to proving circuit lower
bounds. Indeed, derandomization results have played a role in some
state-of-the-art lower bounds, namely the result of Buhrman, Fortnow,
and Thierauf [86] that MAEXP (the exponential-time analogue of
MA) is not in P/poly, and the result of Williams [418, 419] that
NEXP is not in ACC (which is deﬁned like AC0 but also allowing
unbounded fan-in gates that test whether their inputs sum to zero
modulo m, for any constant m). The result of Kabanets and Impagli-
azzo [227] (along with [7]) has also been one of the motivations for



<!-- pdf-page: 300 -->
8.2 Other Topics in Pseudorandomness

297

the recent line of work on derandomizing Polynomial Identity Testing
for low-depth arithmetic circuits. (See the Notes and References of
Section 2.)

8.2.3 Hardness Ampliﬁcation

As discussed in Section 7.6.1, hardness ampliﬁcation is the task
of taking a computational problem that is mildly hard on average
and making it much more hard on average. Hardness ampliﬁca-
tion was introduced by Yao,
in oral presentations of his paper
[421]. Speciﬁcally, he suggested the “Direct Product” construction
f (cid:3)(x1, . . . , xk) = (f (x1), . . . , f (xk)) to convert a weak one-way function
f (one that is mildly hard to invert) into a standard “strong” one-way
function f (cid:3) (satisfying Deﬁnition 7.10), and an “XOR Lemma”
showing that if a Boolean function f is mildly hard to compute,
then f (cid:3)(x1, . . . , xk) =f (x1) ⊕ f (x2) ⊕ · · · f (xk) is very hard on average
to compute. These were tools used in his proof that weak one-way
permutations imply pseudorandom generators. These results have
been generalized and strengthened in a number of ways:

Quantitative Bounds:
It is of interest to have tight bounds on
the hardness of f (cid:3) as a function of the hardness of f and k. For
if f is δ average-case-hard, then
the Direct Product construction,
intuitively we expect f (cid:3) to be roughly (1 − (1 − δ)k) average-case-hard,
corresponding to the fact that an eﬃcient algorithm trying to compute
f (cid:3) should have probability at most 1 − δ of solving each of the k
instances correctly. Similarly, in the case of the XOR Lemma, we
expect that if f is (1 − δ)/2 average-case-hard, then f (cid:3) should be
roughly (1 − δk)/2-average-case hard. Levin [259] proved a version
of the XOR Lemma that gives such a tight bound, and his proof
technique also extends to the Direct Product construction (see [171]).

Derandomization: Goldreich, Impagliazzo, Levin, Venkatesan, and
Zuckerman [166] gave derandomized hardness ampliﬁcation results
for converting weak one-way permutations and weak regular one-way
functions into strong ones, where the inputs xi are not independent but
are generated in some pseudorandom way from a short seed that is the



<!-- pdf-page: 301 -->
298 Conclusions

input to f (cid:3). Impagliazzo and Wigderson [208, 215] gave derandomized
versions of the XOR Lemma and a Direct Product Lemma (for
hard-to-compute boolean functions). These results were used in the
ﬁrst proof, due to [215], that P = BPP if E requires exponential-size
circuits. Recall that the proof we saw in Section 7 avoids hardness
ampliﬁcation, and instead goes directly from worst-case hardness to
strong average-case hardness via locally list-decodable codes (following
[381]). Nevertheless, hardness ampliﬁcation is still of interest because
it can be implemented in lower complexity than worst-case-to-average-
case ampliﬁcation. Indeed, hardness ampliﬁcation (starting from mild
average-case hardness) can be implemented in polynomial time with
oracle access to f , whereas Viola [411] has shown that black-box
worst-case-to-average-case ampliﬁcation (per Deﬁnition 7.74) cannot
be implemented in the polynomial-time hierarchy (due to needing to
compute a list-decodable encoding of the truth table of f ). Indeed,
another line of work has investigated hardness ampliﬁcation for
functions in NP.

Hardness Ampliﬁcation in NP: The study of this topic was
initiated in the work of O’Donnell [304]. The goal is to show that
if NP has a function f that is mildly hard on average, then it
has a function f (cid:3) that is very hard on average. Yao’s XOR Lemma
does not prove this because f being in NP does not imply that
f (cid:3)(x1, . . . , xk) =f (x1) ⊕ · · · ⊕ f (xk) is also in NP, assuming that
NP (cid:1)= co-NP (which is commonly conjectured). Thus, O’Donnell
examines constructions of the form f (cid:3)(x1, . . . , xk) =C (f (x1), . . . , f (xk)),
where C is an eﬃciently computable and monotone combining function
(i.e., changing an input of C from 0 to 1 cannot change the output
from 1 to 0). He characterizes the ampliﬁcation properties of C in
terms of its “noise stability,” thereby connecting the study of hardness
ampliﬁcation with the analysis of boolean functions (see [305] for more
on this topic). He uses this connection to ﬁnd monotone functions C
with nearly optimal ampliﬁcation properties, namely ones that will
ensure that the function f (cid:3) is roughly (1/2 − O(1/
k))-hard if it is
obtained by combining k evaluations of f . Contrast this bound with
the XOR Lemma, where C is the (non-monotone) parity function and

√



<!-- pdf-page: 302 -->
8.2 Other Topics in Pseudorandomness

299

ensures that f (cid:3) is (1/2 − 1/2Ω(k))-hard. Healy, Vadhan, and Viola [202]
showed how to derandomize O’Donnell’s construction, so that the
inputs x1, . . . , xk can be generated in a correlated way by a much
shorter input to f (cid:3). This allows for taking k to be exponential in the
input length of f (cid:3), and for certain combining functions C, the function
f (cid:3) is still in NP (using the ability of a nondeterministic computation
to compute exponential-sized ORs). As a result, assuming that f is
mildly hard for nonuniform algorithms running in time 2Ω(n) (the
“high end”), they obtain f (cid:3) ∈ NP that is (1/2 − 1/2(n(cid:2))1/2
)-hard where
n(cid:3) is the input length of f (cid:3). A quantitative improvement was given by
[273, 179], replacing 2(n(cid:2))1/2
with 2n(cid:2)/polylog(n(cid:2)), but it remains open to
achieve the optimal bound of 2Ω(n(cid:2)).

Uniform Reductions: Another line of work has sought to give
hardness ampliﬁcation results for uniform algorithms, similarly to
the work on derandomization from uniform assumptions described in
Section 8.2.2. Like with cryptographic pseudorandom generators, most
of the hardness ampliﬁcation results in the cryptographic setting, such
as Yao’s original hardness ampliﬁcation for one-way functions [421],
also apply to uniform algorithms. In the noncryptographic setting,
a diﬃculty is that black-box hardness ampliﬁcation corresponds to
error-correcting codes that can be decoded from very large distances,
such as 1/2 − ε in the case of binary codes, and at these distances
unique decoding is impossible, so one must turn to list decoding and
use some nonuniform advice to select the correct decoding from the
list. (See Deﬁnition 7.74 and the discussion after it. For ampliﬁcation
from mild average-case hardness rather than worst-case hardness, the
coding-theoretic interpretation is that the decoding algorithm only
needs to recover a string that is very close to the original message,
rather than exactly equal to the message [209, 390]; this also requires
list decoding for natural settings of parameters.) However, unlike
the case of pseudorandom generator constructions, here the number
of candidates in the list can be relatively small (e.g., poly(1/ε)),
so a reasonable goal for a uniform algorithm is to produce a list of
possible decodings, as in our deﬁnition of locally list-decodable codes
(Deﬁnition 7.54). As observed in [216, 397, 390], if we are interested in



<!-- pdf-page: 303 -->
300 Conclusions

amplifying hardness for functions in natural complexity classes such as
NP or E, we can use (non-black-box) “checkability” properties of the
initial function f to select a good decoding from the list, and thereby
obtain a fully uniform hardness ampliﬁcation result.

Uniform local list-decoding algorithms for the Reed–Muller Code
were given by [35, 381] (as covered in Section 7), and were used to give
uniform worst-case-to-average-case hardness ampliﬁcation results for
E and other complexity classes in [397]. Trevisan [390, 392] initiated
the study of uniform hardness ampliﬁcation from mild average-case
hardness, giving uniform analogues of some of the hardness ampli-
ﬁcation results from [208, 304]. Impagliazzo, Jaiswal, Kabanets, and
Wigderson [210, 211] gave nearly optimal uniform Direct Product
Theorems and XOR Lemmas. The existing uniform ampliﬁcation
results still do not quite match the nonuniform results in two respects.
First, the derandomizations are not quite as strong; in particular, it
is not known how to achieve an optimal “high end” result, converting
a function on n-bit inputs that is mildly average-case hard against
algorithms that run in time 2Ω(n) into a function on O(n)-bit inputs
that is (1/2 − 1/2Ω(n))-hard against time 2Ω(n). (In the nonuniform
setting, this was achieved by [215].) Second, for hardness ampliﬁcation
in NP, the existing uniform results only amplify a function that is
mildly hard against algorithms running in time t to ones that are
(1/2 − 1/(log t)Ω(1))-hard, rather than (1/2 − 1/tΩ(1))-hard, which
for a
is achieved in the nonuniform case by [304, 202]. See [88]
coding-theoretic approach to closing this gap.

Other Cryptographic Primitives: There has also been a large
body of work on security ampliﬁcation for other kinds of cryptographic
primitives and interactive protocols (where the goal of the adversary
is much more complex than just computing or inverting a function).
Describing this body of work is beyond the scope of this survey, so we
simply refer the interested reader to [119, 105, 388] and the references
therein.

A key component of many hardness ampliﬁcation results mentioned
above is the Hardcore Theorem of Impagliazzo [208] and variants. In
its basic form, this theorem states that if a function f is mildly hard



<!-- pdf-page: 304 -->
8.2 Other Topics in Pseudorandomness

301

on average, then there is a hardcore set of inputs, of noticeable density,
on which the function is very hard on average. Thus,
intuitively,
hardness ampliﬁcation occurs when we evaluate a function many times
because we are likely to hit the hardcore set. Since Impagliazzo’s
original paper, there have been a number of papers giving quantitative
improvements to the Hardcore Theorem [243, 206, 45].
In addition
to its applications in hardness ampliﬁcation, the Hardcore Theorem
has been shown to be closely related to “boosting” in machine learn-
ing [243], “dense model theorems” that have applications in additive
number theory and leakage-resilient cryptography [127, 329, 395],
computational analogues of entropy [49, 106, 145, 257, 329, 381, 401],
and “regularity lemmas” in the spirit of Szemer´edi’s Regularity
Lemma in graph theory [396]. One downside of using the Hardcore
Theorem is that the (black-box) reductions in its proofs inherently
require a lot of nonuniform advice [274]. As shown by Holenstein [206],
this nonuniformity can often be avoided in cryptographic settings,
where one can eﬃciently sample random pairs (x, f (x)); his “uniform”
analogue of the Hardcore Theorem and variants have played a key
role in simplifying and improving the construction of cryptographic
pseudorandom generators from one-way functions [198, 206, 401].

8.2.4 Deterministic Extractors

As mentioned in Section 6.5, the study of deterministic extractors has
remained active even after the introduction of seeded extractors. One
reason is that many applications (such as in cryptography, distributed
computing, and Monte Carlo simulation) really require high-quality
random bits, we often only have access to physical sources of random-
ness, and the trick of enumerating the seeds of a seeded extractor does
not work in these contexts. Another is that deterministic extractors
for certain classes of sources often have other applications of interest
(even in contexts where we allow sources of truly random bits). For
these reasons, after nearly a decade of work on simulating BPP with
weak sources and seeded extractors, there was a resurgence of interest
in deterministic extractors for various classes of sources [90, 398].



<!-- pdf-page: 305 -->
302 Conclusions

One important class of sources are those that consist of a
small number of independent k-sources, ﬁrst studied by Chor and
Goldreich [96] (following [346, 409], who gave extractors for several
independent unpredictable-bit sources). In addition to their motivation
for obtaining high-quality randomness, extractors for 2 independent
sources are of
interest because of connections to communication
complexity and to Ramsey theory. (Textbooks on these topics are
[253] and [182], respectively, and their connections to extractors can be
found in [409, 96] and the references below.) In particular, a disperser
for 2 independent k-sources of length n is equivalent to a bipartite
Ramsey graph — a bipartite graph with N vertices on each side that
contains no K × K bipartite clique or K × K bipartite independent
set (for N = 2n and K = 2k). Giving explicit constructions of Ramsey
graphs that approach K = O(log N ) bound given by the probabilistic
method [132] is a long-standing open problem posed by Erd˝os [133].

Chor and Goldreich [96] gave extractors

for 2 independent
k-sources when k > n/2 (e.g.,
inner-product modulo 2), and there
was no improvement in this bound for nearly 2 decades. Substantial
progress began again with the work of Barak, Impagliazzo, and
Wigderson [46], who used new results in arithmetic combinatorics to
construct extractors for a constant number of independent k-sources
when k = δn for an arbitrarily small constant δ > 0. Speciﬁcally, they
used the Sum–Product Theorem over ﬁnite ﬁelds [79], which says that
for p prime and every subset A ⊂ Fp whose size is not too close to
p, either the set A + A of pairwise sums or the set A · A of pairwise
products is of size signiﬁcantly larger than |A|. Arithmetic (and
additive) combinatorics have now been found to be closely connected
to many topics in pseudorandomness and theoretical computer science
more broadly; see the survey of Trevisan [394] and the talks and
lecture notes from the minicourse [50].

A series of subsequent works improved [46] using techniques based
on seeded extractors and condensers, various forms of composition, and
other new ideas, achieving in particular explicit extractors for 3 sources
of min-entropy k = δn [47], extractors for a constant number of sources
of min-entropy k = nδ [318] (notably making no use of arithmetic com-
binatorics), and dispersers for 2 sources of min-entropy k = no(1) [48].



<!-- pdf-page: 306 -->
8.2 Other Topics in Pseudorandomness

303

The latter result is a substantial improvement over the previous best
explicit construction of Ramsey graphs [141], which avoided cliques and
n and only applied to the nonbipartite
independent sets of size K = 2
case. Even with all of this progress, the following remains open:

√

Open Problem 8.11. For every constant δ > 0, construct an explicit
function Ext : {0, 1}n × {0, 1}n → {0, 1} such that
for every two
independent δn-sources X, Y , Ext(X, Y ) isε-close to uniform on {0, 1}.

Another line of work considers classes of sources deﬁned by some
measure of “complexity,” for example capturing the complexity of gen-
erating a random sample of the source (from independent coin tosses).
Explicit extractors have been constructed for a variety of models of
space-bounded sources [69, 231, 246, 247, 398, 408]. In particular,
Kamp, Rao, Vadhan, and Zuckerman [231] show how to determin-
istically extract Ω(n) bits from any source of min-entropy k = Ω(n)
generated by a (nonuniform) algorithm with O(n) space; this results
exploits connections to extracting from multiple independent sources
(as discussed above) as well as from bit-ﬁxing sources (see Section 6.5).
Trevisan and Vadhan [398] suggest to consider sources generated
by small Boolean circuits, and show that under strong complexity
assumptions (similar to, but stronger than, the one in Theorem 7.68),
there is a deterministic extractor computable in time poly(s) that
extracts randomness from sources of min-entropy k = (1 − Ω(1))n
generated by circuits of size s, with error ε = 1/s. It is necessary that
the extractor has higher computational complexity than the source,3
but the min-entropy and error bounds can potentially be much better:

Open Problem 8.12. Under plausible complexity assumptions, show
that there exists a deterministic extractor computable in time poly(s)
that extracts randomness from sources of min-entropy k generated
by circuits of size s, with error ε, for k ≤ n/2 and/or ε = s−ω(1).
Alternatively, give evidence that no such extractor exists.

3 Interestingly, for condensers, it no longer seems necessary that the extractor has higher
complexity than the source [120].



<!-- pdf-page: 307 -->
304 Conclusions

De and Watson [114] and Viola [414, 415] have recently obtained
unconditional extractors for restricted classes of sampling circuits,
such as NC0 (where each output bit depends on a constant number of
input bits) [114, 414] AC0 [414], even for sublinear min-entropy. These
results are based on a close connection between constructing extractors
for a class of circuits and ﬁnding explicit distributions that are hard
for circuits in the class to sample, the latter a topic that was also
studied for the purpose of proving data structure lower bounds [415].
It is also natural to look at sources that are low complexity in an
algebraic sense. The simplest such model is that of aﬃne sources, which
are uniform over aﬃne subspaces of Fn for a ﬁnite ﬁeld F. If the sub-
space has dimension k, then the source is a ﬂat source of min-entropy
k log |F|. For the case of F = Z2, there are now explicit extractors for
aﬃne sources of sublinear min-entropy k = O(n) [78, 422, 262] and dis-
persers for aﬃne sources of subpolynomial min-entropy k = no(1) [353].
For large ﬁelds F (i.e., |F| = poly(n)), there are extractors for subspaces
of every dimension k ≥ 1 [147]. There have also been works on extrac-
tors for sources described by polynomials of degree larger than 1, either
as the output distribution of a low-degree polynomial map [123] or the
zero set of low-degree polynomial (i.e., an algebraic variety) [122].

We remark that several of the state-of-art constructions for
independent sources and aﬃne sources, such as [47, 48, 353], are quite
complicated, using sophisticated compositions and/or machinery from
arithmetic combinatorics. It is of interest to ﬁnd simpler constructions;
some progress has been made for aﬃne sources in [60, 262] and for inde-
pendent sources in [62] (where the latter in fact gives a reductions from
constructing 2-source extractors to constructing aﬃne extractors).

8.2.5 Algebraic Pseudorandomness

Algebraic Measures of Pseudorandomness.
In this survey,
we have mostly focused on statistical and computational measures
of (pseudo)randomness, such as pairwise independence and com-
putational indistinguishability, respectively. It is also of interest to
consider more algebraic measures, because they can be often related to
statistical and/or computational measures, may be convenient for ana-



<!-- pdf-page: 308 -->
8.2 Other Topics in Pseudorandomness

305

lyzing algebraic constructions of pseudorandom objects, and can have
applications of their own (e.g., in additive or arithmetic combinatorics).
One of the most basic and important algebraic measures of pseu-
dorandomness is that of a small-bias space, introduced by Naor and
Naor [296]. Here a random variable X = (X1, . . . , Xn) taking values
in {0, 1}n is said to be ε-biased iﬀ for every nonempty subset S ⊂ [n],
we have (1 − ε)/2 ≤ Pr[⊕i∈SXi = 1]≤ (1 + ε)/2. Naor and Naor [296]
presented an explicit generator G : {0, 1}d → {0, 1}n of seed length
d = O(log(n/ε)) such that G(Ud) isε-biased; thus G is a pseudorandom
generator fooling all “parity tests.” (Simpler constructions with better
constants are in [19].) This generator has found a variety of applica-
tions, such as almost k-wise independent hash functions [296, 19] (cf.
Problem 3.4), pseudorandom generators for small-width branching
programs [345, 363, 179], derandomization of speciﬁc algorithms [296],
and almost-linear-length probabilistically checkable proofs [61, 59].

Small-bias generators have several equivalent formulations. When
viewed appropriately, they are equivalent to linear error-correcting
codes (as in Problem 5.4) over F2 in which every nonzero codeword has
Hamming weight between (1 − ε)/2 and (1 + ε)/2 [296, 19]. They are
also equivalent to expanders with spectral expansion 1 − ε that have
algebraic structure of a Cayley graph over the group G = Zn
2 [24]. (In
general, when G is a group and S ⊂ G, the Cayley graph is |S|-regular
digraph on vertex set G, where the neighbors of vertex g are {gs : s ∈
S}.) Finally, the small-bias property is equivalent to X being a distribu-
tion on the group G = Zn
2 all of whose nontrivial Fourier coeﬃcients are
at most ε [296]. Speciﬁcally, the fact that the (1 − ε)/2 ≤ Pr[⊕i∈SXi =
1] ≤ (1 + ε)/2 is equivalent to requiring that | E[χS(X)]| ≤ε, where
χS(x) = (−1)⊕i∈S xi is the Fourier character of G = Zn
2 indexed by the
set S. (For background on Fourier analysis over ﬁnite groups, see the
book by Terras [387], and for a survey of applications in theoretical com-
puter science, see [115] and the references therein.) Thus, we see that
even in an algebraic context, diﬀerent types of pseudorandom objects
(generators, codes, and expanders) are equivalent.

These diﬀerent views of small-bias spaces suggest diﬀerent general-
izations. One is that of linear codes over larger ﬁnite ﬁelds, which have
been studied extensively in coding theory and of which we’ve seen some



<!-- pdf-page: 309 -->
306 Conclusions

examples (Problem 5.4). Another is to consider Cayley graphs and
Fourier analysis over groups G other than Zn
2 . Over abelian groups, this
generalization is fairly direct; the Fourier coeﬃcients of a small-bias
space on a group G are exactly the eigenvalues of a corresponding Cay-
ley graph over the group G. For many abelian groups, including those
of the form G = Zn
p for prime p, there are known explicit constructions
of small-bias generators with seed length O(log log |G| + log(1/ε)),
corresponding to explicit Cayley expanders of spectral expansion 1 − ε
and degree poly(log |G|, 1/ε) [240, 9, 135, 40, 321, 21]. However, there
are beneﬁts in working with nonabelian groups, as Cayley expanders
over abelian groups G require degree Ω(log N ), where N = |G|
is
the number of vertices [24]. The logarithmic degree lower bound for
expanders over abelian groups also holds for the more general notion of
Schreier graphs, where the group G acts as permutations on the vertex
set V , and we connect a vertex v ∈ V to s(v) for every s ∈ S for some
subset S ⊂ G. On the other hand, many of the algebraic constructions
of constant-degree expanders, including Ramanujan graphs and the
others described in Section 4.3.1, are obtained as Cayley graphs or
Schreier graphs over nonabelian groups. The spectral expansion of
these constructions can be analyzed via group representation theory,
which is more involved than Fourier analysis over abelian groups,
because it deals with matrix-valued (rather than scalar-valued)
functions. See the surveys by Hoory, Linial, and Wigderson [207]
and Lubotzky [276], the lecture notes of Tao [386], and the notes for
Section 4 for more on this and other approaches to analyzing the
expansion of Cayley and Schreier graphs.

In the above, we think of a small-bias generator (according to
the original deﬁnition) as producing pseudorandom elements of the
group G = Zn
2 , and consider generalizations to diﬀerent groups G. An
alternative view is that the small-bias generator produces a sequence
of bits, and the group G = Zn
2 only arises in deﬁning what it means for
the distribution on bit-strings to be pseudorandom. More generally,
we can take G = H n for any ﬁnite group H, and consider a random
variable X = (X1, . . . , Xn) taking values in {0, 1}n to be pseudorandom
if for every (h1, . . . , hn) ∈ H n, the distribution of hX1
is
statistically close to hR1
n where R = (R1, . . . , Rn) is uniformly

· · · hXn
n

1 hX2

· · · hRn

1 hR2

2

2



<!-- pdf-page: 310 -->
8.2 Other Topics in Pseudorandomness

307

· · · hxn
n

distributed in {0, 1}n. This notion is of interest in part because the
function fh(x1, . . . , xn) =h x1
can be computed by a read-once
1
branching program of width |H| (see Section 8.2.1). Thus constructing
generators fooling such “group product programs” are a natural
warm-up to constructing pseudorandom generators for space-bounded
computation, and in fact are equivalent to constructing generators for
permutation branching programs in the case of constant width [250].

Yet another type of generalization is obtained by expanding the
class of distinguishers from linear functions (which over Fn
2 are simply
parities) to higher-degree polynomials. A series of recent results has
shown that the sum of d small-bias spaces (over Fn for any ﬁnite
ﬁeld F) cannot be distinguished from uniform by polynomials of degree
d [75, 270, 413]. These results were inspired by and inﬂuenced work on
the Gowers uniformity norms from arithmetic combinatorics [180, 181],
which can be viewed as providing a “higher-order Fourier analysis”
and have found numerous applications in theoretical computer science.
(See [394, 50].)

Explicit Constructions via Polynomial Evaluation. As we’ve
seen in this survey, algebra also provides powerful tools for construct-
ing pseudorandom objects whose deﬁnitions make no reference to
algebra. One particularly useful paradigm in such constructions is
polynomial evaluation. Speciﬁcally, we construct a pseudorandom
object Γ : Fn × E → Fm, where F is a ﬁnite ﬁeld and E ⊂ Ft is a set
of evaluation points, by setting Γ(f, y) = (f1(y), . . . , fm(y)), where we
view f ∈ Fn as specifying a low-degree polynomial in t variables, from
which we construct m related low-degree polynomials f1, . . . , fm that
we evaluate at the seed y. Reed–Solomon and Reed–Muller Codes
(Constructions 5.14 and 5.16) correspond to the case where m = 1
and we take f1 = f to be a univariate or multivariate polynomial,
respectively.4 In Parvaresh–Vardy Codes (Construction 5.21), we took
f to be a univariate polynomial and obtained the fis by powering f
modulo an irreducible polynomial. In Folded Reed–Solomon Codes

4 In our presentation of Reed–Solomon and Reed–Muller codes, we took E = Ft, but many
of the properties of these codes also hold for appropriately chosen subsets of evaluation
points.



<!-- pdf-page: 311 -->
308 Conclusions

(Construction 5.23), fi(Y ) =f (γi−1Y ), so evaluating fi at y amounts
to evaluating f at the related point γi−1y. More generally, if our con-
struction Γ(f, y) is obtained by evaluating f at points g1(y), . . . , gm(y)
for linear (or low-degree) functions g1, . . . , gm, we can also view it as
evaluating the polynomials f1 = f ◦ g1, . . . , fm = f ◦ gm at the seed y.
Prior to Parvaresh–Vardy codes, constructions of this type were
used for extractors and pseudorandom generators. Speciﬁcally, Mil-
tersen and Vinodchandran [289] show that if we take f to describe
a multivariate polynomial (via low-degree extension) and evaluate it
on the points of a random axis-parallel line through y, we obtain a
hitting-set generator construction against nondeterministic circuits
(assuming f has appropriate worst-case hardness for nondeterministic
circuits); this construction has played a key role in derandomizations
of AM under uniform assumptions [195, 358].5 Ta-Shma, Zuck-
erman, and Safra [384] showed that a similar construction yields
randomness extractors with seed length (1 + O(1)) log n for polyno-
mially small min-entropy and polynomial entropy loss. Shaltiel and
Umans [356, 399] showed that evaluating the t-variate polynomial f at
the points y, γy, γ2y, . . . , γm−1y, where γ is a primitive element of the
ﬁeld of size |F|t (which we associate with Ft) yields both a very good
extractor construction and an optimal construction of pseudorandom
generators from worst-case hard functions. Notice that this construc-
tion is precisely a multivariate analogue of Folded Reed–Solomon
Codes (which came afterwards [188]). Recently, Kopparty, Saraf, and
Yekhanin [249] have introduced yet another useful way of obtaining
the “related polynomials” f1, . . . , fm, namely by taking derivatives of
f ; this has yielded the ﬁrst codes with rate approaching 1 while being
locally (list-)decodable in sublinear time [249, 248] as well as codes
matching the optimal rate-distance tradeoﬀ of Folded Reed–Solomon
Codes [193, 248]. All of this suggests that polynomial evaluation
may be a promising approach to obtaining a uniﬁed and near-optimal
construction of pseudorandom objects (Open Problem 8.5).

5 The constructions described here have some additional components in addition to the basic
polynomial evaluation framework Γ(f, y) = (f1(y), . . . , fm(y)), for example the seed should
also specify the axis along which the line is parallel in [289] and a position in an “inner
encoding” in [384, 356, 399]. We ignore these components in this informal discussion.



<!-- pdf-page: 312 -->
Acknowledgments

My exploration of pseudorandomness began in my graduate and post-
doctoral years at MIT and IAS, under the wonderful guidance of Oded
Goldreich, Shaﬁ Goldwasser, Madhu Sudan, and Avi Wigderson. It was
initiated by an exciting reading group organized at MIT by Luca Tre-
visan, which immersed me in the subject and started my extensive col-
laboration with Luca. Through fortuitous circumstances, I also began
to work with Omer Reingold, starting what I hope will be a lifelong col-
laboration. I am indebted to Oded, Shaﬁ, Madhu, Avi, Luca, and Omer
for all the insights and research experiences they have shared with me.
I have also learned a great deal from my other collaborators on
including Boaz Barak, Eli Ben-Sasson, Michael
pseudorandomness,
Capalbo, Kai-Min Chung, Nenad Dedic, Yevgeniy Dodis, Parikshit
Gopalan, Dan Gutfreund, Venkat Guruswami, Iftach Haitner, Alex
Healy, Thomas Holenstein, Jesse Kamp, Danny Lewin, Adriana
L´opez-Alt, Shachar Lovett, Chi-Jen Lu, Raghu Meka, Ilya Mironov,
Michael Mitzenmacher, Shien Jin Ong, Michael Rabin, Anup Rao, Ran
Raz, Yakir Reshef, Leo Reyzin, Thomas Ristenpart, Eyal Rozenman,
Thomas Steinke, Madhur Tulsiani, Chris Umans, Emanuele Viola,
Hoeteck Wee, Colin Jia Zheng, and David Zuckerman. Needless to

309



<!-- pdf-page: 313 -->
310 Acknowledgments

say, this list omits many other researchers in the ﬁeld with whom I
have had stimulating discussions.

The starting point for this survey was scribe notes taken by
students in the 2004 version of my graduate course on Pseudorandom-
ness. I thank those students for their contribution: Alexandr Andoni,
Adi Akavia, Yan-Cheng Chang, Denis Chebikin, Hamilton Chong,
Vitaly Feldman, Brian Greenberg, Chun-Yun Hsiao, Andrei Jorza,
Adam Kirsch, Kevin Matulef, Mihai Pˇatra¸scu, John Provine, Pavlo
Pylyavskyy, Arthur Rudolph, Saurabh Sanghvi, Grant Schoenebeck,
Jordanna Schutz, Sasha Schwartz, David Troiano, Vinod Vaikun-
tanathan, Kartik Venkatram, David Woodruﬀ. I also thank the
students from the other oﬀerings of the course; Dan Gutfreund, who
gave some guest lectures in 2007; and all of my teaching fellows,
Johnny Chen, Kai-Min Chung, Minh Nguyen, Emanuele Viola, and
Colin Jia Zheng. Special thanks are due to Levent Alpoge, Michael
Forbes, Dieter van Melkebeek, Greg Price, and Adam Sealfon for their
extensive feedback on the lecture notes and/or drafts of this survey.

Helpful input of various types (corrections, comments, answering
questions) has also been given by Zachary Abel, Dana Albrecht, Nir
Avni, Pablo Azar, Trevor Bass, Osbert Bastiani, Jeremy Booher,
Fan Chung, Ben Dozier, Chinmoy Dutta, Zhou Fan, Oded Goldreich,
Andrey Grinshpun, Venkat Guruswami, Alex Healy, Stephan Holzer,
Andrei Jorza, Michael von Korﬀ, Kevn Lee, Alex Lubotzky, Avner May,
Eric Miles, Shira Mitchell, Jelani Nelson, Omer Reingold, Yakir Reshef,
Shubhangi Saraf, Shrenik Shah, Madhu Sudan, Justin Thaler, Jon Ull-
man, Ameya Velingker, Neal Wadhwa, Hoeteck Wee, Avi Wigderson,
and David Wu. Thanks to all of them, as well as those I have forgotten.
I am extremely grateful to James Finlay of now publishers for his
years of patience and continual encouragement, without which I would
have never ﬁnished this survey.

My time working on this survey included sabbatical visits to
the Miller Institute for Basic Research in Science at UC Berkeley,
Microsoft Research Silicon Valley, and Stanford University, as well
as support from a Sloan Fellowship, a Guggenheim Fellowship, NSF
grants CCF-0133096 and CCF-1116616, ONR grant N00014-04-1-0478,
and US-Israel BSF grants 2006060 and 2010196.



<!-- pdf-page: 314 -->
References

[1] S. Aaronson and D. van Melkebeek, “On circuit lower bounds from derandom-
ization,” Theory of Computing. An Open Access Journal, vol. 7, pp. 177–184,
2011.

[2] M. Abadi, J. Feigenbaum, and J. Kilian, “On hiding information from an ora-
cle,” Journal of Computer and System Sciences, vol. 39, no. 1, pp. 21–50, 1989.
[3] L. Adleman, “Two theorems on random polynomial time,” in Annual
Symposium on Foundations of Computer Science (Ann Arbor, Mich., 1978),
pp. 75–83, Long Beach, California, 1978.

[4] M. Agrawal, “On derandomizing tests for certain polynomial identities,” in

IEEE Conference on Computational Complexity, pp. 355–, 2003.

[5] M. Agrawal and S. Biswas, “Primality and identity testing via Chinese

remaindering,” Journal of the ACM, vol. 50, no. 4, pp. 429–443, 2003.

[6] M. Agrawal, N. Kayal, and N. Saxena, “PRIMES is in P,” Annals of

Mathematics. Second Series, vol. 160, no. 2, pp. 781–793, 2004.

[7] M. Agrawal and V. Vinay, “Arithmetic circuits: A chasm at depth four,” in

FOCS, pp. 67–75, 2008.

[8] A. V. Aho, ed., Proceedings of the Annual ACM Symposium on Theory of

Computing, 1987, New York, USA, 1987.

[9] M. Ajtai, H. Iwaniec, J. Koml´os, J. Pintz, and E. Szemer´edi, “Construc-
tion of a thin set with small Fourier coeﬃcients,” Bulletin of the London
Mathematical Society, vol. 22, no. 6, pp. 583–590, 1990.

[10] M. Ajtai, J. Koml´os, and E. Szemer´edi, “Sorting in c log n parallel steps,”

Combinatorica, vol. 3, no. 1, pp. 1–19, 1983.

311



<!-- pdf-page: 315 -->
312 References

[11] M. Ajtai, J. Koml´os, and E. Szemer´edi, “Deterministic Simulation in
LOGSPACE,” in Annual ACM Symposium on Theory of Computing,
pp. 132–140, New York City, 25–27 May 1987.

[12] M. Ajtai and A. Wigderson, “Deterministic simulation of probabilistic con-
stant depth circuits,” in Randomness and Computation, vol. 5 of Advances in
Computing Research, (F. P. Preparata and S. Micali, eds.), pp. 199–223, 1989.
[13] R. Aleliunas, R. M. Karp, R. J. Lipton, L. Lov´asz, and C. Rackoﬀ, “Random
walks, universal traversal sequences, and the complexity of maze problems,”
in Annual Symposium on Foundations of Computer Science (San Juan,
Puerto Rico, 1979), pp. 218–223, New York, 1979.

[14] E. Allender, H. Buhrman, M. Kouck´y, D. van Melkebeek, and D. Ronneb-
urger, “Power from random strings,” SIAM Journal on Computing, vol. 35,
no. 6, pp. 1467–1493, 2006.

[15] N. Alon, “Eigenvalues and expanders,” Combinatorica, vol. 6, no. 2, pp. 83–96,

1986.

[16] N. Alon, “Eigenvalues, geometric expanders, sorting in rounds, and Ramsey

theory,” Combinatorica, vol. 6, no. 3, pp. 207–219, 1986.

[17] N. Alon and M. R. Capalbo, “Explicit unique-neighbor expanders,” in
Symposium on Foundations of Computer Science (Vancouver, BC, 2002),
pp. 73–79, 2002.

[18] N. Alon and F. R. K. Chung, “Explicit construction of linear sized tolerant

networks,” Discrete Mathematics, vol. 72, no. 1–3, pp. 15–19, 1988.

[19] N. Alon, O. Goldreich, J. H˚astad, and R. Peralta, “Simple constructions
of almost k-wise independent random variables,” Random Structures &
Algorithms, vol. 3, no. 3, pp. 289–304, 1992.
(See also addendum in issue
4(1), 1993, pp. 199–120).

[20] N. Alon, V. Guruswami, T. Kaufman, and M. Sudan, “Guessing secrets
eﬃciently via list decoding,” ACM Transactions on Algorithms, vol. 3, no. 4,
pp. Art 42, 16, 2007.

[21] N. Alon and Y. Mansour, “(cid:1)-discrepancy sets and their application for
interpolation of sparse polynomials,” Information Processing Letters, vol. 54,
no. 6, pp. 337–342, 1995.

[22] N. Alon, Y. Matias, and M. Szegedy, “The space complexity of approximating
the frequency moments,” Journal of Computer and System Sciences, vol. 58,
no. 1, pp. 137–147, (Part 2) 1999.

[23] N. Alon and V. D. Milman, “Eigenvalues, expanders and superconcentrators
(Extended Abstract),” in Annual Symposium on Foundations of Computer
Science, pp. 320–322, Singer Island, Florida, 24–26 October 1984.

[24] N. Alon and Y. Roichman, “Random Cayley graphs and expanders,” Random

Structures and Algorithms, vol. 5, no. 2, pp. 271–284, 1994.

[25] N. Alon and J. H. Spencer, The Probabilistic Method. Wiley-Interscience
Series in Discrete Mathematics and Optimization.
New York: Wiley-
Interscience [John Wiley & Sons], Second Edition, 2000. (With an appendix
on the life and work of Paul Erd˝os).

[26] N. Alon and B. Sudakov, “Bipartite subgraphs and the smallest eigenvalue,”
Combinatorics, Probability and Computing, vol. 9, no. 1, pp. 1–12, 2000.



<!-- pdf-page: 316 -->
References

313

[27] A. E. Andreev, A. E. F. Clementi, and J. D. P. Rolim, “Worst-case hard-
ness suﬃces for derandomization: A new method for hardness-randomness
trade-oﬀs,” in Automata, Languages and Programming, 24th International
Colloquium, vol. 1256 of Lecture Notes in Computer Science, (P. Degano,
R. Gorrieri, and A. Marchetti-Spaccamela, eds.), pp. 177–187, Bologna, Italy:
Springer-Verlag, 7–11 July 1997.

[28] A. E. Andreev, A. E. F. Clementi, J. D. P. Rolim, and L. Trevisan, “Weak
random sources, hitting sets, and BPP simulations,” SIAM Journal on
Computing, vol. 28, no. 6, pp. 2103–2116, (electronic) 1999.

[29] D. Angluin and D. Lichtenstein, “Provable security of cryptosystems: A sur-
vey,” Technical Report YALEU/DCS/TR-288, Yale University, Department
of Computer Science, 1983.

[30] S. Ar, R. J. Lipton, R. Rubinfeld, and M. Sudan, “Reconstructing algebraic
functions from mixed data,” SIAM Journal on Computing, vol. 28, no. 2,
pp. 487–510, 1999.

[31] R. Armoni, M. Saks, A. Wigderson, and S. Zhou, “Discrepancy sets and pseu-
dorandom generators for combinatorial rectangles,” in Annual Symposium on
Foundations of Computer Science (Burlington, VT, 1996), pp. 412–421, Los
Alamitos, CA, 1996.

[32] S. Arora and B. Barak, Computational complexity. Cambridge: Cambridge

University Press, 2009. (A modern approach).

[33] S. Arora, C. Lund, R. Motwani, M. Sudan, and M. Szegedy, “Proof veriﬁ-
cation and the hardness of approximation problems,” Journal of the ACM,
vol. 45, pp. 501–555, May 1998.

[34] S. Arora and S. Safra, “Probabilistic checking of proofs: A new characteriza-

tion of NP,” Journal of the ACM, vol. 45, pp. 70–122, January 1998.

[35] S. Arora and M. Sudan, “Improved low degree testing and its applications,”
in Proceedings of the Annual ACM Symposium on Theory of Computing,
pp. 485–495, El Paso, Texas, 4–6 May 1997.

[36] M. Artin, Algebra. Englewood Cliﬀs, NJ: Prentice Hall Inc., 1991.
[37] V. Arvind and J. K¨obler, “On pseudorandomness and resource-bounded
measure,” Theoretical Computer Science, vol. 255, no. 1–2, pp. 205–221, 2001.
[38] B. Aydinlio˜glu, D. Gutfreund, J. M. Hitchcock, and A. Kawachi, “Derandom-
izing Arthur-Merlin games and approximate counting implies exponential-size
lower bounds,” Computational Complexity, vol. 20, no. 2, pp. 329–366, 2011.
[39] B. Aydinlio˜glu and D. van Melkebeek, “Nondeterministic circuit lower bounds
from mildly derandomizing Arthur-Merlin games,” Electronic Colloquium on
Computational Complexity (ECCC), vol. 19, p. 80, 2012.

[40] Y. Azar, R. Motwani, and J. Naor, “Approximating probability distributions
using small sample spaces,” Combinatorica, vol. 18, no. 2, pp. 151–171, 1998.
[41] L. Babai, L. Fortnow, L. A. Levin, and M. Szegedy, “Checking computations
in polylogarithmic time,” in STOC, (C. Koutsougeras and J. S. Vitter, eds.),
pp. 21–31, ACM, 1991.

[42] L. Babai, L. Fortnow, and C. Lund, “Nondeterministic exponential time has
two-prover interactive protocols,” Computational Complexity, vol. 1, no. 1,
pp. 3–40, 1991.



<!-- pdf-page: 317 -->
314 References

[43] L. Babai, L. Fortnow, N. Nisan, and A. Wigderson, “BPP has subexponential
time simulations unless EXPTIME has publishable proofs,” Computational
Complexity, vol. 3, no. 4, pp. 307–318, 1993.

[44] L. Babai and S. Moran, “Arthur-Merlin games: A randomized proof system,
and a hierarchy of complexity classes,” Journal of Computer and System
Sciences, vol. 36, no. 2, pp. 254–276, 1988.

[45] B. Barak, M. Hardt, and S. Kale, “The uniform hardcore lemma via
approximate Bregman projections,” in Proceedings of the Annual ACM-SIAM
Symposium on Discrete Algorithms, pp. 1193–1200, Philadelphia, PA, 2009.

[46] B. Barak, R. Impagliazzo, and A. Wigderson, “Extracting randomness using
few independent sources,” SIAM Journal on Computing, vol. 36, no. 4,
pp. 1095–1118, 2006.

[47] B. Barak, G. Kindler, R. Shaltiel, B. Sudakov, and A. Wigderson, “Simulating
independence: New constructions of condensers, Ramsey graphs, dispersers,
and extractors,” Journal of the ACM, vol. 57, no. 4, no. 4, pp. Art 20, 52, 2010.
[48] B. Barak, A. Rao, R. Shaltiel, and A. Wigderson, “2-source dispersers for
no(1) entropy and Ramsey graphs beating the Frankl–Wilson construction,”
Annals of Mathematics, 2012. (To appear. Preliminary version in STOC ‘06).
[49] B. Barak, R. Shaltiel, and A. Wigderson, “Computational analogues of
entropy,” in Approximation, randomization, and combinatorial optimization,
vol. 2764 of Lecture Notes in Computer Science, pp. 200–215, Berlin: Springer,
2003.

[50] B. Barak, L. Trevisan, and A. Wigderson, Additive Combinatorics and
http://www.cs.princeton.edu/theory/index.php/Main/

Computer Science.
AdditiveCombinatoricsMinicourse, August 2007.

[51] E. Barker and J. Kelsey, “Recommendation for random number generation
using deterministic random bit generators,” Special Publication 800-90A,
National
Institute of Standards and Technology, U.S. Department of
Commerce, January 2012.

[52] L. A. Bassalygo, “Asymptotically optimal switching circuits,” Problems of

Information Transmission, vol. 17, no. 3, pp. 206–211, 1981.

[53] J. D. Batson, D. A. Spielman, and N. Srivastava, “Twice-ramanujan sparsi-
ﬁers,” in Annual ACM Symposium on Theory of Computing (Bethesda, MD),
pp. 255–262, 2009.

[54] D. Beaver and J. Feigenbaum, “Hiding instances in multioracle queries
(Extended Abstract),” in STACS 90 (Rouen, 1990), vol. 415 of Lecture Notes
in Computer Science, pp. 37–48, Berlin: Springer, 1990.

[55] M. Bellare, O. Goldreich, and S. Goldwasser, “Randomness in interactive

proofs,” Computational Complexity, vol. 3, no. 4, pp. 319–354, 1993.

[56] M. Bellare, S. Goldwasser, and D. Micciancio, ““Pseudo-Random” number
generation within cryptographic algorithms: The DDS case,” in CRYPTO,
vol. 1294 of Lecture Notes in Computer Science, (B. S. K. Jr., ed.),
pp. 277–291, Springer, 1997.

[57] M. Bellare and J. Rompel, “Randomness-eﬃcient oblivious sampling,” in
Annual Symposium on Foundations of Computer Science, pp. 276–287, Santa
Fe, New Mexico, 20–22 November 1994.



<!-- pdf-page: 318 -->
References

315

[58] A. Ben-Aroya and A. Ta-Shma, “A combinatorial construction of almost-
Ramanujan graphs using the zig-zag product,” in Annual ACM Symposium
on Theory of Computing (Victoria, British Columbia), pp. 325–334, 2008.
[59] E. Ben-Sasson, O. Goldreich, P. Harsha, M. Sudan, and S. Vadhan, “Robust
PCPs of proximity, shorter PCPs and applications to coding,” SIAM Journal
on Computing, vol. 36, no. 4, pp. 889–974, 2006.

[60] E. Ben-Sasson and S. Kopparty, “Aﬃne dispersers from subspace polynomi-
als,” in STOC’09 — Proceedings of the 2009 ACM International Symposium
on Theory of Computing, pp. 65–74, New York, 2009.

[61] E. Ben-Sasson, M. Sudan, S. Vadhan, and A. Wigderson, “Randomness-
eﬃcient low degree tests and short PCPs via epsilon-biased sets,” in
Proceedings of
the Annual ACM Symposium on Theory of Computing,
pp. 612–621, New York, 2003.

[62] E. Ben-Sasson and N. Zewi, “From aﬃne to two-source extractors via approx-
imate duality,” in STOC, (L. Fortnow and S. P. Vadhan, eds.), pp. 177–186,
ACM, 2011.

[63] C. H. Bennett, G. Brassard, and J.-M. Robert, “Privacy ampliﬁcation by
public discussion,” SIAM Journal on Computing, vol. 17, no. 2, pp. 210–229,
1988. Special issue on cryptography.

[64] S. J. Berkowitz, “On computing the determinant in small parallel time using
a small number of processors,” Information Processing Letters, vol. 18, no. 3,
pp. 147–150, 1984.

[65] E. R. Berlekamp, Algebraic Coding Theory. New York: McGraw-Hill Book

Co., 1968.

[66] E. R. Berlekamp, “Factoring polynomials over large ﬁnite ﬁelds,” Mathematics

of Computation, vol. 24, pp. 713–735, 1970.

[67] J. Bierbrauer, T. Johansson, G. Kabatianskii, and B. Smeets, “On families
of hash functions via geometric codes and concatenation,” in Advances in
cryptology — CRYPTO ’93 (Santa Barbara, CA, 1993), vol. 773 of Lecture
Notes in Computer Science, pp. 331–342, Berlin: Springer, 1994.

[68] Y. Bilu and N. Linial, “Lifts, discrepancy and nearly optimal spectral gap,”

Combinatorica, vol. 26, no. 5, pp. 495–519, 2006.

[69] M. Blum, “Independent unbiased coin ﬂips from a correlated biased source —
a ﬁnite state Markov chain,” Combinatorica, vol. 6, no. 2, pp. 97–108, 1986.
Theory of computing (Singer Island, Fla., 1984).

[70] M. Blum and S. Kannan, “Designing programs that check their work,”

Journal of the ACM, vol. 42, no. 1, pp. 269–291, 1995.

[71] M. Blum, M. Luby, and R. Rubinfeld, “Self-testing/correcting with appli-
cations to numerical problems,” Journal of Computer and System Sciences,
vol. 47, no. 3, pp. 549–595, 1993.

[72] M. Blum and S. Micali, “How to generate cryptographically strong sequences
of pseudorandom bits,” SIAM Journal on Computing, vol. 13, no. 4,
pp. 850–864, 1984.

[73] A. Bogdanov, Z. Dvir, E. Verbin, and A. Yehudayoﬀ, “Pseudorandomness
for Width 2 Branching Programs,” Electronic Colloquium on Computational
Complexity (ECCC), vol. 16, p. 70, 2009.



<!-- pdf-page: 319 -->
316 References

[74] A. Bogdanov and L. Trevisan, “Average-case complexity,” Foundations
and Trends(cid:1) in Theoretical Computer Science, vol. 2, no. 1, pp. 1–106,
2006.

[75] A. Bogdanov and E. Viola, “Pseudorandom bits for polynomials,” SIAM

Journal on Computing, vol. 39, no. 6, pp. 2464–2486, 2010.

[76] A. Borodin, J. von zur Gathen, and J. Hopcroft, “Fast parallel matrix and
GCD computations,” Information and Control, vol. 52, no. 3, pp. 241–256,
1982.

[77] C. Bosley and Y. Dodis, “Does privacy require true randomness?,” in Theory
of cryptography, vol. 4392 of Lecture Notes in Computer Science, pp. 1–20,
Berlin: Springer, 2007.

[78] J. Bourgain, “On the construction of aﬃne extractors,” Geometric and

Functional Analysis, vol. 17, no. 1, pp. 33–57, 2007.

[79] J. Bourgain, N. Katz, and T. Tao, “A sum-product estimate in ﬁnite
ﬁelds, and applications,” Geometric and Functional Analysis, vol. 14, no. 1,
pp. 27–57, 2004.

[80] J. Boyar, “Inferring sequences produced by pseudo-random number genera-
tors,” Journal of the Association for Computing Machinery, vol. 36, no. 1,
pp. 129–141, 1989.

[81] M. Braverman, “Polylogarithmic independence fools AC0 circuits,” Journal

of the ACM, vol. 57, no. 5, pp. Art 28, 10, 2010.

[82] M. Braverman, A. Rao, R. Raz, and A. Yehudayoﬀ, “Pseudorandom gener-
ators for regular branching programs,” in FOCS, pp. 40–47, IEEE Computer
Society, 2010.

[83] A. Z. Broder, “How hard is to marry at random? (On the approximation
of the permanent),” in Annual ACM Symposium on Theory of Computing
(Berkeley, CA), pp. 50–58, 1986.

[84] J. Brody and E. Verbin, “The coin problem and pseudorandomness for

branching programs,” in FOCS, pp. 30–39, IEEE Computer Society, 2010.

[85] H. Buhrman and L. Fortnow, “One-sided two-sided error in probabilistic
computation,” in STACS 99 (Trier), vol. 1563 of Lecture Notes in Computer
Science, pp. 100–109, Berlin: Springer, 1999.

[86] H. Buhrman, L. Fortnow, and T. Thierauf, “Nonrelativizing separations,” in
Annual IEEE Conference on Computational Complexity (Buﬀalo, NY, 1998),
pp. 8–12, Los Alamitos, CA, 1998.

[87] H. Buhrman, P. B. Miltersen, J. Radhakrishnan, and S. Venkatesh, “Are
bitvectors optimal?,” SIAM Journal on Computing, vol. 31, no. 6, pp. 1723–
1744, 2002.

[88] J. Buresh-Oppenheim, V. Kabanets, and R. Santhanam, “Uniform hard-
ness ampliﬁcation in NP via monotone codes,” Electronic Colloquium on
Computational Complexity (ECCC), vol. 13, no. 154, 2006.

[89] P. B¨urgisser, M. Clausen, and M. A. Shokrollahi, Algebraic Complexity
Theory, volume 315 of Grundlehren der Mathematischen Wissenschaften
[Fundamental Principles of Mathematical Sciences]. Berlin: Springer-Verlag,
1997. (With the collaboration of Thomas Lickteig).



<!-- pdf-page: 320 -->
References

317

[90] R. Canetti, Y. Dodis, S. Halevi, E. Kushilevitz, and A. Sahai, “Exposure-
in
resilient
Cryptology — EUROCRYPT 00, Lecture Notes in Computer Science,
(B. Preneel, ed.), Springer-Verlag, 14–18 May 2000.

and all-or-nothing

in Advances

transforms,”

functions

[91] R. Canetti, G. Even, and O. Goldreich, “Lower bounds for sampling algo-
rithms for estimating the average,” Information Processing Letters, vol. 53,
no. 1, pp. 17–25, 1995.

[92] M. Capalbo, O. Reingold, S. Vadhan, and A. Wigderson, “Randomness con-
ductors and constant-degree lossless expanders,” in Annual ACM Symposium
on Theory of Computing (STOC ‘02), pp. 659–668, Montr´eal, CA, May 2002.
(Joint session with CCC ‘02).

[93] J. L. Carter and M. N. Wegman, “Universal classes of hash functions,”
Journal of Computer and System Sciences, vol. 18, no. 2, pp. 143–154, 1979.
[94] J. Cheeger, “A lower bound for the smallest eigenvalue of the Laplacian,”
in Problems in analysis (Papers dedicated to Salomon Bochner, 1969),
pp. 195–199, Princeton, NJ: Princeton Univ. Press, 1970.

[95] H. Chernoﬀ, “A measure of asymptotic eﬃciency for tests of a hypothesis
based on the sum of observations,” Annals of Mathematical Statistics, vol. 23,
pp. 493–507, 1952.

[96] B. Chor and O. Goldreich, “Unbiased bits from sources of weak randomness
and probabilistic communication complexity,” SIAM Journal on Computing,
vol. 17, pp. 230–261, April 1988.

[97] B. Chor and O. Goldreich, “On the power of two-point based sampling,”

Journal of Complexity, vol. 5, no. 1, pp. 96–106, 1989.

[98] B. Chor, O. Goldreich, J. H˚astad, J. Friedman, S. Rudich, and R. Smolensky,
“The bit extraction problem of t-resilient functions (Preliminary Version),”
in FOCS, pp. 396–407, IEEE, 1985.

[99] B. Chor, O. Goldreich, E. Kushilevitz, and M. Sudan, “Private information

retrieval,” Journal of the ACM, vol. 45, no. 6, pp. 965–982, 1998.

[100] F. Chung and R. Graham, “Sparse quasi-random graphs,” Combinatorica,
issue: Paul Erd˝os and his

(Special

vol. 22, no. 2, pp. 217–244, 2002.
mathematics).

[101] F. Chung and R. Graham, “Quasi-random graphs with given degree
sequences,” Random Structures and Algorithms, vol. 32, no. 1, pp. 1–19, 2008.
[102] F. Chung, R. Graham, and T. Leighton, “Guessing secrets,” Electronic Jour-
nal of Combinatorics, vol. 8, no. 1, p. 25 (electronic), 2001. Research Paper 13.
[103] F. R. K. Chung, “Diameters and eigenvalues,” Journal of the American

Mathematical Society, vol. 2, no. 2, pp. 187–196, 1989.

[104] F. R. K. Chung, R. L. Graham, and R. M. Wilson, “Quasi-random graphs,”

Combinatorica, vol. 9, no. 4, pp. 345–362, 1989.

[105] K.-M. Chung, “Eﬃcient parallel repetition theorems with applications to

security ampliﬁcation,” PhD Thesis, Harvard University, 2011.

[106] K.-M. Chung, Y. T. Kalai, F.-H. Liu, and R. Raz, “Memory delegation,”
in Advances in Cryptology — CRYPTO 2011, vol. 6841 of Lecture Notes in
Computer Science, pp. 151–168, Heidelberg: Springer, 2011.



<!-- pdf-page: 321 -->
318 References

[107] A. Cohen and A. Wigderson, “Dispersers, deterministic ampliﬁcation,
and weak random sources (extended abstract),” in Annual Symposium on
Foundations of Computer Science (Research Triangle Park, North Carolina),
pp. 14–19, 1989.

[108] D. Coppersmith and S. Winograd, “Matrix multiplication via arithmetic pro-
gressions,” Journal of Symbolic Computation, vol. 9, no. 3, pp. 251–280, 1990.
[109] T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein, Introduction to

Algorithms. Cambridge, MA: MIT Press, Second Edition, 2001.

[110] T. M. Cover and J. A. Thomas, Elements of Information Theory. Wiley
Series in Telecommunications: John Wiley & Sons, Inc., Second Edition, 1991.
[111] L. Csanky, “Fast parallel matrix inversion algorithms,” SIAM Journal on

Computing, vol. 5, no. 4, pp. 618–623, 1976.

[112] G. Davidoﬀ, P. Sarnak, and A. Valette, “Elementary number theory, group
theory, and Ramanujan graphs,” in vol. 55 of London Mathematical Society
Student Texts, Cambridge: Cambridge University Press, 2003.

[113] A. De, “Pseudorandomness for permutation and regular branching programs,”
in IEEE Conference on Computational Complexity, pp. 221–231, 2011.
[114] A. De and T. Watson, “Extractors and lower bounds for locally samplable
sources,” in Approximation, Randomization, and Combinatorial Optimization,
vol. 6845 of Lecture Notes in Computer Science, pp. 483–494, Heidelberg:
Springer, 2011.

[115] R. de Wolf, “A Brief Introduction to Fourier analysis on the Boolean cube,”

Theory of Computing, Graduate Surveys, vol. 1, pp. 1–20, 2008.

[116] R. A. DeMillo and R. J. Lipton, “A probabilistic remark on algebraic program

testing,” Information Processing Letters, vol. 7, no. 4, pp. 193–195, 1978.
[117] W. Diﬃe and M. E. Hellman, “New directions in cryptography,” IEEE

Transactions on Information Theory, vol. IT-22, no. 6, pp. 644–654, 1976.

[118] I. Dinur, “The PCP theorem by gap ampliﬁcation,” Journal of the ACM,

vol. 54, no. 3, article 12, p. 44 (electronic), 2007.

[119] Y. Dodis, R. Impagliazzo, R. Jaiswal, and V. Kabanets, “Security ampliﬁca-
tion for interactive cryptographic primitives,” in Theory of Cryptography, vol.
5444 of Lecture Notes in Computer Science, pp. 128–145, Berlin: Springer,
2009.

[120] Y. Dodis, T. Ristenpart, and S. Vadhan, “Randomness condensers for
eﬃciently samplable, seed-dependent sources,” in Proceedings of the IACR
Theory of Cryptography Conference (TCC ‘12), vol. 7194 of Lecture Notes
in Computer Science, (R. Cramer, ed.), pp. 618–635, Springer-Verlag, 19–21
March 2012.

[121] D. Dubhashi and A. Panconesi, Concentration of Measure for the Analysis of

Randomized Algorithms. Cambridge University Press, 2009.

[122] Z. Dvir, “Extractors for varieties,” in IEEE Conference on Computational

Complexity, pp. 102–113, 2009.

[123] Z. Dvir, A. Gabizon, and A. Wigderson, “Extractors and rank extractors
for polynomial sources,” Computational Complexity, vol. 18, no. 1, pp. 1–58,
2009.



<!-- pdf-page: 322 -->
References

319

[124] Z. Dvir, S. Kopparty, S. Saraf, and M. Sudan, “Extensions to the method
of multiplicities, with applications to Kakeya sets and mergers,” in 2009
Annual IEEE Symposium on Foundations of Computer Science (FOCS
2009), pp. 181–190, Los Alamitos, CA, 2009.

[125] Z. Dvir and S. Lovett, “Subspace evasive sets,” in Symposium on Theory of

Computing, (H. J. Karloﬀ and T. Pitassi, eds.), pp. 351–358, ACM, 2012.

[126] Z. Dvir and A. Shpilka, “Locally decodable codes with two queries and poly-
nomial identity testing for depth 3 circuits,” SIAM Journal on Computing,
vol. 36, no. 5, pp. 1404–1434 (electronic), 2006/07.

[127] S. Dziembowski and K. Pietrzak, “Leakage-resilient cryptography,” in
Symposium on Foundations of Computer Science, pp. 293–302, 2008.
[128] K. Efremenko, “3-query locally decodable codes of subexponential length,”
in STOC’09 — Proceedings of the 2009 ACM International Symposium on
Theory of Computing, pp. 39–44, New York, 2009.

[129] P. Elias, List Decoding for Noisy Channels, Research Laboratory of Electron-
ics, Massachusetts Institute of Technology. Rep. No. 335: Cambridge, MA,
1957.

[130] P. Elias, “The eﬃcient construction of an unbiased random sequence,” The

Annals of Mathematical Statistics, vol. 43, no. 3, pp. 865–870, June 1972.

[131] P. Elias, “Error-correcting codes for list decoding,” IEEE Transactions on

Information Theory, vol. 37, no. 1, pp. 5–12, 1991.

[132] P. Erd˝os, “Some remarks on the theory of graphs,” Bulletin of the American

Mathematical Society, vol. 53, pp. 292–294, 1947.

[133] P. Erd˝os, “Problems and results in chromatic graph theory,” in Proof
Techniques in Graph Theory (Proceedings of Ann Arbor Graph Theory
Conference, Ann Arbor, Michigan, 1968), pp. 27–35, New York, 1969.
[134] P. Erd˝os, P. Frankl, and Z. F¨uredi, “Families of ﬁnite sets in which no set
is covered by the union of r others,” Israel Journal of Mathematics, vol. 51,
no. 1–2, pp. 79–89, 1985.

[135] G. Even, “Construction of small probabilistic spaces for deterministic

simulation,” Master’s Thesis, The Technion, 1991.

[136] G. Even, O. Goldreich, M. Luby, N. Nisan, and B. Velickovic, “Eﬃcient
approximation of product distributions,” Random Struct. Algorithms, vol. 13,
no. 1, pp. 1–16, 1998.

[137] S. Even, A. L. Selman, and Y. Yacobi, “The complexity of promise problems
with applications to public-key cryptography,” Information and Control,
vol. 61, no. 2, pp. 159–173, 1984.

[138] U. Feige, S. Goldwasser, L. Lov´asz, S. Safra, and M. Szegedy, “Interactive
proofs and the hardness of approximating cliques,” Journal of the ACM,
vol. 43, no. 2, pp. 268–292, 1996.

[139] J. A. Fill, “Eigenvalue bounds on convergence to stationarity for nonreversible
Markov chains, with an application to the exclusion process,” Annals of
Applied Probability, vol. 1, no. 1, pp. 62–87, 1991.

[140] G. D. Forney, Concatenated Codes. MIT Press, 1966.
[141] P. Frankl and R. M. Wilson, “Intersection theorems with geometric

consequences,” Combinatorica, vol. 1, no. 4, pp. 357–368, 1981.



<!-- pdf-page: 323 -->
320 References

[142] M. L. Fredman, J. Koml´os, and E. Szemer´edi, “Storing a sparse table with
O(1) worst case access time,” Journal of the ACM, vol. 31, no. 3, pp. 538–544,
1984.

[143] J. Friedman, “A proof of Alon’s second eigenvalue conjecture and related
problems,” Memoirs of the American Mathematical Society, vol. 195, no. 910,
p. viii+100, 2008.

[144] A. M. Frieze, J. H˚astad, R. Kannan, J. C. Lagarias, and A. Shamir, “Recon-
structing truncated integer variables satisfying linear congruences,” SIAM
Journal on Computing, vol. 17, no. 2, pp. 262–280, 1988. (Special issue on
cryptography).

[145] B. Fuller, A. O’Neill, and L. Reyzin, “A uniﬁed approach to deterministic
encryption: New constructions and a connection to computational entropy,”
in TCC, vol. 7194 of Lecture Notes in Computer Science, (R. Cramer, ed.),
pp. 582–599, 2012.

[146] O. Gabber and Z. Galil, “Explicit constructions of linear-sized superconcen-
trators,” Journal of Computer and System Sciences, vol. 22, pp. 407–420,
June 1981.

[147] A. Gabizon and R. Raz, “Deterministic extractors for aﬃne sources over

large ﬁelds,” Combinatorica, vol. 28, no. 4, pp. 415–440, 2008.
[148] R. G. Gallager, Low-Density Parity-Check Codes. MIT Press, 1963.
[149] P. Gemmell, R. J. Lipton, R. Rubinfeld, M. Sudan, and A. Wigderson,
“Self-testing/correcting for polynomials and for approximate functions,” in
STOC, (C. Koutsougeras and J. S. Vitter, eds.), pp. 32–42, 1991.

[150] P. Gemmell and M. Sudan, “Highly resilient correctors for polynomials,”

Information Processing Letters, vol. 43, no. 4, pp. 169–174, 1992.

[151] E. Gilbert, “A comparison of signalling alphabets,” Bell Systems Technical

Journal, vol. 31, pp. 504–522, 1952.

[152] J. Gill, “Computational complexity of probabilistic Turing machines,” SIAM

Journal on Computing, vol. 6, no. 4, pp. 675–695, 1977.

[153] D. Gillman, “A Chernoﬀ bound for random walks on expander graphs,”
SIAM Journal on Computing, vol. 27, no. 4, pp. 1203–1220 (electronic), 1998.
[154] M. X. Goemans and D. P. Williamson, “Improved approximation algo-
rithms for maximum cut and satisﬁability problems using semideﬁnite
programming,” Journal of the ACM, vol. 42, no. 6, pp. 1115–1145, 1995.
[155] O. Goldreich, “A sample of samplers — a computational perspective on
sampling (survey),” Electronic Colloquium on Computational Complexity
(ECCC), vol. 4, no. 20, 1997.

[156] O. Goldreich, Modern Cryptography, Probabilistic Proofs and Pseudorandom-
ness, vol. 17 of Algorithms and Combinatorics. Berlin: Springer-Verlag, 1999.
[157] O. Goldreich, Foundations of Cryptography. Cambridge: Cambridge Univer-

sity Press, 2001. (Basic tools).

[158] O. Goldreich, Foundations of Cryptography II. Cambridge: Cambridge

University Press, 2004. (Basic Applications).

[159] O. Goldreich, “On promise problems: A survey,” in Theoretical Computer
Science, vol. 3895 of Lecture Notes in Computer Science, pp. 254–290, Berlin:
Springer, 2006.



<!-- pdf-page: 324 -->
References

321

[160] O. Goldreich, “Probabilistic proof systems: A primer,” Foundations and
Trends in Theoretical Computer Science, vol. 3, no. 1, pp. 1–91 (2008), 2007.
[161] O. Goldreich, Computational Complexity: A Conceptual Perspective. Cam-

bridge: Cambridge University Press, 2008.

[162] O. Goldreich, A Primer on Pseudorandom Generators, vol. 55 of University
Lecture Series. Providence, RI: American Mathematical Society, 2010.
[163] O. Goldreich, “In a World of P=BPP,” in Studies in Complexity and
Cryptography. Miscellanea on the Interplay of Randomness and Computation,
vol. 6650 of Lecture Notes in Computer Science, pp. 191–232, Springer, 2011.
[164] O. Goldreich, S. Goldwasser, and S. Micali, “How to construct random

functions,” Journal of the ACM, vol. 33, pp. 792–807, October 1986.

[165] O. Goldreich, S. Goldwasser, and D. Ron, “Property testing and its connec-
tion to learning and approximation,” Journal of the ACM, vol. 45, no. 4,
pp. 653–750, 1998.

[166] O. Goldreich, R. Impagliazzo, L. Levin, R. Venkatesan, and D. Zuckerman,
“Security preserving ampliﬁcation of hardness,” in Annual Symposium
on Foundations of Computer Science, Vol. I, II (St. Louis, MO, 1990),
pp. 318–326, Los Alamitos, CA: IEEE Computer Society Press, 1990.
[167] O. Goldreich, H. Krawczyk, and M. Luby, “On the existence of pseudorandom
generators,” SIAM Journal on Computing, vol. 22, no. 6, pp. 1163–1175, 1993.
[168] O. Goldreich and L. A. Levin, “A hard-core predicate for all one-way
functions,” in Proceedings of the Annual ACM Symposium on Theory of
Computing, pp. 25–32, Seattle, Washington, 15–17 May 1989.

[169] O. Goldreich and B. Meyer, “Computational indistinguishability: algorithms
vs. circuits,” Theoretical Computer Science, vol. 191, no. 1–2, pp. 215–218,
1998.

[170] O. Goldreich, S. Micali, and A. Wigderson, “Proofs that yield nothing but
their validity, or All languages in NP have zero-knowledge proof systems,”
Journal of the ACM, vol. 38, no. 3, pp. 691–729, 1991.

[171] O. Goldreich, N. Nisan, and A. Wigderson, “On Yao’s XOR lemma,” Tech-
nical Report TR95–050, revision 2, Electronic Colloquium on Computational
Complexity, http://www.eccc.uni-trier.de/eccc, June 2010.

[172] O. Goldreich and M. Sudan, “Computational indistinguishability: A sample
hierarchy,” Journal of Computer and System Sciences, vol. 59, no. 2, pp. 253–
269, 1999.
(13th Annual IEEE Conference on Computation Complexity
(Buﬀalo, NY, 1998)).

[173] O. Goldreich, S. Vadhan, and A. Wigderson, “Simpliﬁed derandomization of
BPP using a hitting set generator,” in Studies in Complexity and Cryptogra-
phy. Miscellanea on the Interplay of Randomness and Computation, vol. 6650
of Lecture Notes in Computer Science, pp. 59–67, Springer, 2011.

[174] O. Goldreich and A. Wigderson, “Tiny families of functions with random
properties: A quality-size trade-oﬀ for hashing,” Random Structures &
Algorithms, vol. 11, no. 4, pp. 315–343, 1997.

[175] S. Goldwasser, “Cryptography without (hardly any) secrets?,” in Advances
in cryptology — EUROCRYPT 2009, vol. 5479 of Lecture Notes in Computer
Science, pp. 369–370, Berlin: Springer, 2009.



<!-- pdf-page: 325 -->
322 References

[176] S. Goldwasser and S. Micali, “Probabilistic Encryption,” Journal of Computer

and System Sciences, vol. 28, pp. 270–299, April 1984.

[177] S. Goldwasser, S. Micali, and C. Rackoﬀ, “The knowledge complexity of
interactive proof systems,” SIAM Journal on Computing, vol. 18, no. 1,
pp. 186–208, 1989.

[178] P. Gopalan, R. Meka, and O. Reingold, “DNF Sparsiﬁcation and a faster
deterministic counting algorithm,” in IEEE Conference on Computational
Complexity, pp. 126–135, 2012.

[179] P. Gopalan, R. Meka, O. Reingold, L. Trevisan, and S. Vadhan, “Better pseu-
dorandom generators via milder pseudorandom restrictions,” in Proceedings
of the Annual IEEE Symposium on Foundations of Computer Science (FOCS
‘12), 20–23 October 2012. (To appear).

[180] W. T. Gowers, “A new proof of Szemer´edi’s theorem for arithmetic pro-
gressions of length four,” Geometric and Functional Analysis, vol. 8, no. 3,
pp. 529–551, 1998.

[181] W. T. Gowers, “A new proof of Szemer´edi’s theorem,” Geometric and

Functional Analysis, vol. 11, no. 3, pp. 465–588, 2001.

[182] R. L. Graham, B. L. Rothschild, and J. H. Spencer, Ramsey Theory.
Wiley-Interscience Series in Discrete Mathematics and Optimization. New
York: John Wiley & Sons Inc., Second Edition, 1990.

[183] V. Guruswami, “Guest column: Error-correcting codes and expander graphs,”

SIGACT News, vol. 35, no. 3, pp. 25–41, 2004.

[184] V. Guruswami, Algorithmic Results in List Decoding. volume 2, number 2 of
Foundations and Trends in Theoretical Computer Science. now publishers,
2006.

[185] V. Guruswami, “Linear-algebraic list decoding of folded reed-solomon codes,”

in IEEE Conference on Computational Complexity, pp. 77–85, 2011.

[186] V. Guruswami, J. H˚astad, and S. Kopparty, “On the list-decodability of
random linear codes,” IEEE Transactions on Information Theory, vol. 57,
no. 2, pp. 718–725, 2011.

[187] V. Guruswami, J. H˚astad, M. Sudan, and D. Zuckerman, “Combinatorial
bounds for list decoding,” IEEE Transactions on Information Theory, vol. 48,
no. 5, pp. 1021–1034, 2002.

[188] V. Guruswami and A. Rudra, “Explicit codes achieving list decoding
capacity: error-correction with optimal redundancy,” IEEE Transactions on
Information Theory, vol. 54, no. 1, pp. 135–150, 2008.

[189] V. Guruswami and M. Sudan, “Improved decoding of Reed-Solomon and
algebraic-geometry codes,” Institute of Electrical and Electronics Engineers.
Transactions on Information Theory, vol. 45, no. 6, pp. 1757–1767, 1999.
[190] V. Guruswami and M. Sudan, “List decoding algorithms for certain

concatenated codes,” in STOC, pp. 181–190, 2000.

[191] V. Guruswami and M. Sudan, “Extensions to the Johnson bound,” Unpub-

lished Manuscript, February 2001.

[192] V. Guruswami, C. Umans, and S. Vadhan, “Unbalanced expanders and
randomness extractors from Parvaresh–Vardy codes,” Journal of the ACM,
vol. 56, no. 4, pp. 1–34, 2009.



<!-- pdf-page: 326 -->
References

323

[193] V. Guruswami and C. Wang, “Optimal rate list decoding via derivative codes,”
in Approximation, randomization, and combinatorial optimization, vol. 6845
of Lecture Notes in Computer Science, pp. 593–604, Heidelberg: Springer,
2011.

[194] V. Guruswami and C. Xing, “Folded codes from function ﬁeld towers and
improved optimal rate list decoding,” in STOC, (H. J. Karloﬀ and T. Pitassi,
eds.), pp. 339–350, ACM, 2012.

[195] D. Gutfreund, R. Shaltiel, and A. Ta-Shma, “Uniform hardness versus
randomness tradeoﬀs for Arthur-Merlin games,” Computational Complexity,
vol. 12, no. 3–4, pp. 85–130, 2003.

[196] J. H˚astad, Computational Limitations of Small-Depth Circuits. MIT Press,

1987.

[197] J. H˚astad, R. Impagliazzo, L. A. Levin, and M. Luby, “A pseudorandom
generator from any one-way function,” SIAM Journal on Computing, vol. 28,
no. 4, pp. 1364–1396, 1999.

[198] I. Haitner, O. Reingold, and S. Vadhan, “Eﬃciency improvements in con-
structing pseudorandom generators from one-way functions,” in Proceedings
of the Annual ACM Symposium on Theory of Computing (STOC ‘10),
pp. 437–446, 6–8 June 2010.

[199] R. W. Hamming, “Error detecting and error correcting codes,” The Bell

System Technical Journal, vol. 29, pp. 147–160, 1950.

[200] J. Hartmanis and R. E. Stearns, “On the computational complexity of
algorithms,” Transactions of the American Mathematical Society, vol. 117,
pp. 285–306, 1965.

[201] N. J. A. Harvey, “Algebraic structures and algorithms for matching and
matroid problems,” in Annual IEEE Symposium on Foundations of Computer
Science (Berkeley, CA), pp. 531–542, 2006.

[202] A. Healy, S. Vadhan, and E. Viola, “Using nondeterminism to amplify

hardness,” SIAM Journal on Computing, vol. 35, no. 4, pp. 903–931, 2006.

[203] A. D. Healy, “Randomness-eﬃcient sampling within NC1,” Computational

Complexity, vol. 17, no. 1, pp. 3–37, 2008.

[204] W. Hoeﬀding, “Probability inequalities for sums of bounded random vari-
ables,” Journal of the American Statistical Association, vol. 58, pp. 13–30,
1963.

[205] A. J. Hoﬀman, “On eigenvalues and colorings of graphs,” in Graph Theory and
its Applications (Proceedings of Advanced Seminors, Mathematics Research
Center, University of Wisconsin, Madison, Wisconsin, 1969), pp. 79–91, New
York: Academic Press, 1970.

[206] T. Holenstein, “Key agreement from weak bit agreement,” in STOC’05:
the Annual ACM Symposium on Theory of Computing,

Proceedings of
pp. 664–673, New York, 2005.

[207] S. Hoory, N. Linial, and A. Wigderson, “Expander graphs and their
applications,” Bulletin of the AMS, vol. 43, no. 4, pp. 439–561, 2006.
[208] R. Impagliazzo, “Hard-core distributions for somewhat hard problems,”
in Annual Symposium on Foundations of Computer Science, pp. 538–545,
Milwaukee, Wisconsin, 23–25 October 1995.



<!-- pdf-page: 327 -->
324 References

[209] R. Impagliazzo, “Hardness as randomness: A survey of universal derandom-
ization,” in Proceedings of the International Congress of Mathematicians,
Vol. III (Beijing, 2002), pp. 659–672, Beijing, 2002.

[210] R. Impagliazzo, R. Jaiswal, and V. Kabanets, “Approximate list-decoding of
direct product codes and uniform hardness ampliﬁcation,” SIAM Journal on
Computing, vol. 39, no. 2, pp. 564–605, 2009.

[211] R. Impagliazzo, R. Jaiswal, V. Kabanets, and A. Wigderson, “Uniform direct
product theorems: Simpliﬁed, optimized, and derandomized,” SIAM Journal
on Computing, vol. 39, no. 4, pp. 1637–1665, 2009/2010.

[212] R. Impagliazzo, V. Kabanets, and A. Wigderson, “In search of an easy
witness: Exponential time vs. probabilistic polynomial time,” Journal of
Computer and System Sciences, vol. 65, no. 4, pp. 672–694, 2002.

[213] R. Impagliazzo and S. Rudich, “Limits on the provable consequences of
one-way permutations,” in Advances in cryptology — CRYPTO ’88 (Santa
Barbara, CA, 1988), vol 403 of Lecture Notes in Computer Science, pp. 8–26,
Berlin: Springer, 1990.

[214] R. Impagliazzo and A. Wigderson, “An information-theoretic variant of the
inclusion-exclusion bound (preliminary version),” Unpublished manuscript,
1996.

[215] R. Impagliazzo and A. Wigderson, “P = BPP if E requires exponential
circuits: Derandomizing the XOR lemma,” in Proceedings of the Annual ACM
Symposium on Theory of Computing, pp. 220–229, El Paso, Texas, 4–6 May
1997.

[216] R. Impagliazzo and A. Wigderson, “Randomness vs time: Derandomization
under a uniform assumption,” Journal of Computer and System Sciences,
vol. 63, no. 4, pp. 672–688, 2001. Special issue on FOCS 98 (Palo Alto CA).
[217] R. Impagliazzo and D. Zuckerman, “How to recycle random bits,” in Annual
Symposium on Foundations of Computer Science (Research Triangle Park,
North Carolina), pp. 248–253, 1989.

[218] K. Iwama and H. Morizumi, “An explicit lower bound of 5n − o(n) for Boolean
circuits,” in Mathematical foundations of computer science 2002, vol. 2420 of
Lecture Notes in Computer Science, pp. 353–364, Berlin: Springer, 2002.
[219] M. Jerrum and A. Sinclair, “Approximating the permanent,” SIAM Journal

on Computing, vol. 18, no. 6, pp. 1149–1178, 1989.

[220] M. Jerrum, A. Sinclair, and E. Vigoda, “A polynomial-time approximation
algorithm for the permanent of a matrix with nonnegative entries,” Journal
of the ACM, vol. 51, no. 4, pp. 671–697, 2004.

[221] S. Jimbo and A. Maruoka, “Expanders obtained from aﬃne transformations,”

Combinatorica, vol. 7, no. 4, pp. 343–355, 1987.

[222] A. Joﬀe, “On a sequence of almost deterministic pairwise independent ran-
dom variables,” Proceedings of the American Mathematical Society, vol. 29,
pp. 381–382, 1971.

[223] A. Joﬀe, “On a set of almost deterministic k-independent random variables,”

Annals of Probability, vol. 2, no. 1, pp. 161–162, 1974.

[224] S. Johnson, “Upper bounds for constant weight error correcting codes,”

Discrete Mathematics, vol. 3, pp. 109–124, 1972.



<!-- pdf-page: 328 -->
References

325

[225] S. M. Johnson, “A new upper bound for error-correcting codes,” IRE

Transactions on Information Theory, vol. IT-8, pp. 203–207, 1962.

[226] V. Kabanets, “Derandomization: A brief overview,” in Current Trends in
Theoretical Computer Science, vol. 1 Algorithms and Complexity, (G. Paun,
G. Rozenberg, and A. Salomaa, eds.), pp. 165–188, World Scientiﬁc, 2004.

[227] V. Kabanets and R. Impagliazzo, “Derandomizing polynomial identity tests
means proving circuit lower bounds,” Computational Complexity, vol. 13,
no. 1–2, pp. 1–46, 2004.

[228] N. Kahale, “Eigenvalues and expansion of regular graphs,” Journal of the

ACM, vol. 42, no. 5, pp. 1091–1106, 1995.

[229] J. D. Kahn, N. Linial, N. Nisan, and M. E. Saks, “On the cover time of
random walks on graphs,” Journal of Theoretical Probability, vol. 2, no. 1,
pp. 121–128, 1989.

[230] A. T. Kalai, “Unpublished manuscript,” 2004.
[231] J. Kamp, A. Rao, S. Vadhan, and D. Zuckerman, “Deterministic extractors
for small-space sources,” Journal of Computer and System Sciences, vol. 77,
no. 1, pp. 191–220, 2011.

[232] J. Kamp and D. Zuckerman, “Deterministic extractors for bit-ﬁxing sources
and exposure-resilient cryptography,” SIAM Journal on Computing, vol. 36,
no. 5, pp. 1231–1247, 2006/2007.

[233] H. J. Karloﬀ and T. Pitassi, eds., Proceedings of the Symposium on Theory
of Computing Conference, STOC 2012, New York, NY, USA, May 19–22,
2012, 2012.

[234] R. Karp, N. Pippenger, and M. Sipser, “A time-randomness tradeoﬀ,” in
AMS Conference on Probabilistic Computational Complexity, Durham, New
Hampshire, 1985.

[235] R. M. Karp and R. J. Lipton, “Turing machines that take advice,”
L’Enseignement Math´ematique. Revue Internationale. IIe S´erie, vol. 28,
no. 3–4, pp. 191–209, 1982.

[236] R. M. Karp, M. Luby, and N. Madras, “Monte Carlo approximation algo-
rithms for enumeration problems,” Journal of Algorithms, vol. 10, no. 3,
pp. 429–448, 1989.

[237] R. M. Karp, E. Upfal, and A. Wigderson, “Constructing a perfect matching

is in Random NC,” Combinatorica, vol. 6, no. 1, pp. 35–48, 1986.

[238] J. Katz and Y. Lindell, Introduction to modern cryptography. Chapman &
Hall/CRC Cryptography and Network Security. Boca Raton, FL: Chapman
& Hall/CRC, 2008.

[239] J. Katz and L. Trevisan, “On the eﬃciency of local decoding procedures for
error-correcting codes,” in Proceedings of the Annual ACM Symposium on
Theory of Computing, pp. 80–86 (electronic), New York, 2000.

[240] N. M. Katz, “An estimate for character sums,” Journal of the American

Mathematical Society, vol. 2, no. 2, pp. 197–200, 1989.

[241] N. Kayal and N. Saxena, “Polynomial identity testing for depth 3 circuits,”

Computational Complexity, vol. 16, no. 2, pp. 115–138, 2007.

[242] J. Kinne, D. van Melkebeek, and R. Shaltiel, “Pseudorandom generators,
typically-correct derandomization, and dircuit lower bounds,” Computational
Complexity, vol. 21, no. 1, pp. 3–61, 2012.



<!-- pdf-page: 329 -->
326 References

[243] A. R. Klivans and R. A. Servedio, “Boosting and Hard-Core Set Construc-

tion,” Machine Learning, vol. 51, no. 3, pp. 217–238, 2003.

[244] A. R. Klivans and D. van Melkebeek, “Graph nonisomorphism has subex-
ponential size proofs unless the polynomial-time hierarchy collapses,” SIAM
Journal on Computing, vol. 31, no. 5, pp. 1501–1526 (electronic), 2002.
[245] D. E. Knuth, The art of computer programming. Volume 2: Seminumerical

Algorithms. Addison–Wesley, Third Edition, 1998.

[246] R. K¨onig and U. M. Maurer, “Extracting randomness from generalized
symbol-ﬁxing and Markov sources,” in Proceedings of 2004 IEEE Interna-
tional Symposium on Information Theory, p. 232, 2004.

[247] R. K¨onig and U. M. Maurer, “Generalized strong extractors and deterministic
privacy ampliﬁcation,” in IMA International Conference, vol. 3796 of Lecture
Notes in Computer Science, (N. P. Smart, ed.), pp. 322–339, Springer, 2005.
[248] S. Kopparty, “List-decoding multiplicity codes,” Electronic Colloquium on

Computational Complexity (ECCC), vol. 19, p. 44, 2012.

[249] S. Kopparty, S. Saraf, and S. Yekhanin, “High-rate codes with sublinear-time
decoding,” in STOC, (L. Fortnow and S. P. Vadhan, eds.), pp. 167–176,
ACM, 2011.

[250] M. Kouck´y, P. Nimbhorkar, and P. Pudl´ak, “Pseudorandom generators for
group products: extended abstract,” in STOC, (L. Fortnow and S. P. Vadhan,
eds.), pp. 263–272, ACM, 2011.

[251] C. Koutsougeras and J. S. Vitter, eds., Proceedings of the Annual ACM Sym-
posium on Theory of Computing, May 5–8, 1991, New Orleans, Louisiana,
USA, ACM, 1991.

[252] H. Krawczyk, “How to predict congruential generators,” Journal of Algo-

rithms, vol. 13, no. 4, pp. 527–545, 1992.

[253] E. Kushilevitz and N. Nisan, Communication complexity.

Cambridge:

Cambridge University Press, 1997.

[254] O. Lachish and R. Raz, “Explicit lower bound of 4.5n − o(n) for Boolean
circuits,” in Annual ACM Symposium on Theory of Computing, pp. 399–408
(electronic), New York, 2001.

[255] H. O. Lancaster, “Pairwise statistical independence,” Annals of Mathematical

Statistics, vol. 36, pp. 1313–1317, 1965.

[256] C. Lautemann, “BPP and the polynomial hierarchy,” Information Processing

Letters, vol. 17, no. 4, pp. 215–217, 1983.

[257] C.-J. Lee, C.-J. Lu, and S.-C. Tsai, “Computational randomness from gen-
eralized hardcore sets,” in Fundamentals of Computation Theory, vol. 6914
of Lecture Notes in Computer Science, pp. 78–89, Heidelberg: Springer,
2011.

[258] F. T. Leighton, Introduction to Parallel Algorithms and Architectures: Arrays,

Trees, and Hypercubes. San Mateo, CA: Morgan Kaufmann, 1992.

[259] L. A. Levin, “One way functions and pseudorandom generators,” Combina-

torica, vol. 7, no. 4, pp. 357–363, 1987.

[260] D. Lewin and S. Vadhan, “Checking polynomial identities over any ﬁeld:
towards a derandomization?,” in Annual ACM Symposium on the Theory of
Computing (Dallas, TX), pp. 438–447, New York, 1999.



<!-- pdf-page: 330 -->
References

327

[261] M. Li and P. Vit´anyi, An Introduction to Kolmogorov Complexity and its
Applications. Texts in Computer Science. New York: Springer, Third Edition,
2008.

[262] X. Li, “A New Approach to Aﬃne Extractors and Dispersers,” in IEEE

Conference on Computational Complexity, pp. 137–147, 2011.

[263] R. Lidl and H. Niederreiter, Introduction to Finite Fields and their Applica-

tions. Cambridge: Cambridge University Press, First Edition, 1994.

[264] N. Linial, M. Luby, M. Saks, and D. Zuckerman, “Eﬃcient construction
of a small hitting set for combinatorial rectangles in high dimension,”
Combinatorica, vol. 17, no. 2, pp. 215–234, 1997.

[265] N. Linial and N. Nisan, “Approximate inclusion-exclusion,” Combinatorica,

vol. 10, no. 4, pp. 349–365, 1990.

[266] R. J. Lipton, “New directions in testing,” in Distributed computing and

cryptography (Princeton, NJ, 1989), vol. 2 ofDIMACS Series Discrete
Mathemtics and Theoretical Computer Science, pp. 191–202, Providence, RI:
American Mathematical Society, 1991.

[267] L. Lov´asz, “On determinants, matchings, and random algorithms,” in Funda-
mentals of Computation Theory (Berlin/Wendisch-Rietz), pp. 565–574, 1979.
[268] L. Lov´asz, “On the Shannon capacity of a graph,” IEEE Transactions on

Information Theory, vol. 25, no. 1, pp. 1–7, 1979.

[269] L. Lov´asz, Combinatorial Problems and Exercises. Providence, RI: AMS

Chelsea Publishing, Second Edition, 2007.

[270] S. Lovett, “Unconditional pseudorandom generators for low-degree polynomi-
als,” Theory of Computing. An Open Access Journal, vol. 5, pp. 69–82, 2009.
[271] C.-J. Lu, “Improved pseudorandom generators for combinatorial rectangles,”

Combinatorica, vol. 22, no. 3, pp. 417–433, 2002.

[272] C.-J. Lu, O. Reingold, S. Vadhan, and A. Wigderson, “Extractors: optimal
up to constant factors,” in Proceedings of the ACM Symposium on Theory of
Computing (STOC ‘03), pp. 602–611, 2003.

[273] C.-J. Lu, S.-C. Tsai, and H.-L. Wu, “Improved hardness ampliﬁcation in

NP,” Theoretical Computer Science, vol. 370, no. 1–3, pp. 293–298, 2007.

[274] C.-J. Lu, S.-C. Tsai, and H.-L. Wu, “Complexity of hard-core set proofs,”

Computational Complexity, vol. 20, no. 1, pp. 145–171, 2011.

[275] A. Lubotzky, Discrete Groups, Expanding Graphs and Invariant Measures.
volume 125 of Progress in Mathematics. Basel: Birkh¨auser Verlag, 1994.
(With an appendix by Jonathan D. Rogawski).

[276] A. Lubotzky, “Expander graphs in pure and applied mathematics,” American
Mathematical Society. Bulletin. New Series, vol. 49, no. 1, pp. 113–162, 2012.
[277] A. Lubotzky, R. Phillips, and P. Sarnak, “Ramanujan graphs,” Combinatorica,

vol. 8, no. 3, pp. 261–277, 1988.

[278] M. Luby, “A simple parallel algorithm for the maximal

independent set
problem,” SIAM Journal on Computing, vol. 15, no. 4, pp. 1036–1053, 1986.
[279] M. Luby, “Removing randomness in parallel computation without a pro-
cessor penalty,” Journal of Computer and System Sciences, vol. 47, no. 2,
pp. 250–286, 1993.



<!-- pdf-page: 331 -->
328 References

[280] M. Luby, B. Veliˇckovi´c, and A. Wigderson, “Deterministic Approximate

Counting of Depth-2 Circuits,” in ISTCS, pp. 18–24, 1993.

[281] M. Luby and A. Wigderson, Pairwise Independence and Derandomization.
Volume 1, number 4 of Foundations and Trends in Theoretical Computer
Science. now publishers, 2005.

[282] F. J. MacWilliams and N. J. A. Sloane, The Theory of Error-correcting
(North-Holland

Codes. Amsterdam: North-Holland Publishing Co., 1977.
Mathematical Library, Vol. 16).

[283] G. A. Margulis, “Explicit constructions of expanders,” Problemy Peredaˇci

Informacii, vol. 9, no. 4, pp. 71–80, 1973.

[284] G. A. Margulis, “Explicit group-theoretic constructions of combinato-
rial schemes and their applications in the construction of expanders and
concentrators,” Problemy Peredaˇci Informacii, vol. 24, no. 1, pp. 51–60, 1988.
[285] R. Martin and D. Randall, “Disjoint decomposition of Markov chains
and sampling circuits in Cayley graphs,” Combinatorics, Probability and
Computing, vol. 15, no. 3, pp. 411–448, 2006.

[286] M. Mihail, “Conductance and convergence of Markov Chains-A combinatorial
treatment of expanders,” in Annual Symposium on Foundations of Computer
Science (Research Triangle Park, North Carolina), pp. 526–531, 1989.
[287] G. L. Miller, “Riemann’s hypothesis and tests for primality,” Journal of
Computer and System Sciences, vol. 13, no. 3, pp. 300–317, December 1976.
[288] P. Miltersen, Handbook of Randomized Computing, chapter Derandomizing

Complexity Classes. Kluwer, 2001.

[289] P. B. Miltersen and N. V. Vinodchandran, “Derandomizing Arthur-Merlin
games using hitting sets,” Computational Complexity, vol. 14, no. 3,
pp. 256–279, 2005.

[290] M. Mitzenmacher and E. Upfal, Probability and Computing. Cambridge:
Cambridge University Press, 2005. (Randomized algorithms and probabilistic
analysis).

[291] R. Motwani and P. Raghavan, Randomized Algorithms.

Cambridge:

Cambridge University Press, 1995.

[292] M. Mucha and P. Sankowski, “Maximum matchings via Gaussian elimina-
tion,” in Symposium on Foundations of Computer Science (Rome, Italy),
pp. 248–255, IEEE Computer Society, 2004.

[293] D. E. Muller, “Boolean algebras in electric circuit design,” The American
Mathematical Monthly, vol. 61, no. 7 part II, pp. 27–28, 1954. (Proceedings
of the symposium on special topics in applied mathematics, Northwestern
University (1953)).

[294] K. Mulmuley, U. V. Vazirani, and V. V. Vazirani, “Matching is as easy as

matrix inversion,” Combinatorica, vol. 7, no. 1, pp. 105–113, 1987.

[295] S. Muthukrishnan, Data Streams: Algorithms and Applications, volume 1,
number 2 of Foundations and Trends in Theoretical Computer Science. now
publishers, 2005.

[296] J. Naor and M. Naor, “Small-bias probability spaces: Eﬃcient constructions
and applications,” SIAM Journal on Computing, vol. 22, pp. 838–856, August
1993.



<!-- pdf-page: 332 -->
References

329

[297] A. Nilli, “On the second eigenvalue of a graph,” Discrete Mathematics,

vol. 91, no. 2, pp. 207–210, 1991.

[298] N. Nisan, “Pseudorandom bits for constant depth circuits,” Combinatorica,

vol. 11, no. 1, pp. 63–70, 1991.

[299] N. Nisan, “Pseudorandom generators for space-bounded computation,”

Combinatorica, vol. 12, no. 4, pp. 449–461, 1992.

[300] N. Nisan, “RL ⊆ SC,” Computational Complexity, vol. 4, no. 1, pp. 1–11, 1994.
[301] N. Nisan and A. Ta-Shma, “Extracting randomness: A survey and new con-
structions,” Journal of Computer and System Sciences, vol. 58, pp. 148–173,
February 1999.

[302] N. Nisan and A. Wigderson, “Hardness vs Randomness,” Journal of Computer

and System Sciences, vol. 49, pp. 149–167, October 1994.

[303] N. Nisan and D. Zuckerman, “Randomness is linear in space,” Journal of

Computer and System Sciences, vol. 52, pp. 43–52, February 1996.

[304] R. O’Donnell, “Hardness ampliﬁcation within NP,” Journal of Computer and

System Sciences, vol. 69, no. 1, pp. 68–94, 2004.

[305] R. O’Donnell, “Analysis of boolean functions,” Book draft available at

analysisofbooleanfunctions.org, 2012.

[306] F. Parvaresh and A. Vardy, “Correcting errors beyond the Guruswami-Sudan
radius in polynomial time,” in Proceedings of the IEEE Symposium on
Foundations of Computer Science, pp. 285–294, 2005.

[307] Y. Peres, “Iterating von Neumann’s procedure for extracting random bits,”

The Annals of Statistics, vol. 20, no. 1, pp. 590–597, 1992.

[308] W. W. Peterson, “Encoding and error-correction procedures for the Bose-
Chaudhuri codes,” IRE Transactions on Information Theory, vol. IT-6,
pp. 459–470, 1960.

[309] M. Pinsker, “On the complexity of a concentrator,” in Annual Teletraﬃc

Conference, pp. 318/1–318/4, Stockholm, 1973.

[310] N. Pippenger, “On simultaneous resource bounds (Preliminary Version),” in
Annual Symposium on Foundations of Computer Science (San Juan, Puerto
Rico), pp. 307–311, 1979.

[311] N. Pippenger and M. J. Fischer, “Relations among complexity measures,”
the Association for Computing Machinery, vol. 26, no. 2,

Journal of
pp. 361–381, 1979.

[312] R. L. Plackett and J. E. Burman, “The design of optimum multi-factorial

experiments,” Biometrika, vol. 33, pp. 305–325, 1945.

[313] V. S. Pless, W. C. Huﬀman, and R. A. Brualdi, eds., Handbook of Coding

Theory. Vol. I, II. Amsterdam: North-Holland, 1998.

[314] M. O. Rabin, “Probabilistic algorithm for testing primality,” Journal of

Number Theory, vol. 12, no. 1, pp. 128–138, 1980.

[315] J. Radhakrishnan and A. Ta-Shma, “Bounds for dispersers, extractors, and
depth-two superconcentrators,” SIAM Journal on Discrete Mathematics,
vol. 13, no. 1 (electronic), pp. 2–24, 2000.

[316] P. Raghavan, “Probabilistic

construction of deterministic algorithms:
approximating packing integer programs,” Journal of Computer and System
Sciences, vol. 37, no. 2, pp. 130–143, 1988. (Annual IEEE Symposium on the
Foundations of Computer Science (Toronto, ON, 1986)).



<!-- pdf-page: 333 -->
330 References

[317] D. Randall, “Mixing,” in Symposium on Foundations of Computer Science

(Cambridge, MA), pp. 4–15, 2003.

[318] A. Rao, “Extractors for a constant number of polynomially small min-
entropy independent sources,” SIAM Journal on Computing, vol. 39, no. 1,
pp. 168–194, 2009.

[319] R. Raz and O. Reingold, “On recycling the randomness of states in space
bounded computation,” in Annual ACM Symposium on Theory of Computing
(Atlanta, GA, 1999), pp. 159–168 (electronic), New York: ACM, 1999.
[320] R. Raz, O. Reingold, and S. Vadhan, “Extracting all the Randomness and
Reducing the Error in Trevisan’s Extractors,” Journal of Computer and
System Sciences, vol. 65, pp. 97–128, August 2002.

[321] A. Razborov, E. Szemer´edi, and A. Wigderson, “Constructing small sets
that are uniform in arithmetic progressions,” Combinatorics Probability
Computing, vol. 2, no. 4, pp. 513–518, 1993.

[322] A. A. Razborov, “Lower bounds on the dimension of schemes of bounded
depth in a complete basis containing the logical addition function,” Akademiya
Nauk SSSR. Matematicheskie Zametki, vol. 41, no. 4, pp. 598–607, 623, 1987.
[323] A. A. Razborov and S. Rudich, “Natural proofs,” Journal of Computer and
System Sciences, vol. 55, no. 1, part 1, pp. 24–35, 1997. (26th Annual ACM
Symposium on the Theory of Computing (STOC ’94) (Montreal, PQ, 1994)).
[324] I. S. Reed, “A class of multiple-error-correcting codes and the decoding
scheme,” IRE Transactions on Information Theory, PGIT-4, pp. 38–49,
1954.

[325] I. S. Reed and G. Solomon, “Polynomial codes over certain ﬁnite ﬁelds,” Jour-
nal of the Society of Industrial and Applied Mathematics, vol. 8, pp. 300–304,
1960.

[326] O. Reingold, “On black-box separations in cryptography,” Tutorial at the
Third Theory of Cryptography Conference (TCC ‘06), March 2006. Slides
available from http://research.microsoft.com/en-us/people/omreing/.
[327] O. Reingold, “Undirected connectivity in log-space,” Journal of the ACM,

vol. 55, no. 4, pp. Art 17, 24, 2008.

[328] O. Reingold, R. Shaltiel, and A. Wigderson, “Extracting randomness
via repeated condensing,” SIAM Journal on Computing, vol. 35, no. 5,
pp. 1185–1209, (electronic), 2006.

[329] O. Reingold, L. Trevisan, M. Tulsiani, and S. Vadhan, “Dense subsets of
pseudorandom sets,” in Proceedings of the Annual IEEE Symposium on Foun-
dations of Computer Science (FOCS ‘08), pp. 76–85, 26–28 October 2008.

[330] O. Reingold, L. Trevisan, and S. Vadhan, “Notions of reducibility between
cryptographic primitives,” in Proceedings of the First Theory of Cryptography
Conference (TCC ‘04), vol. 2951 of Lecture Notes in Computer Science,
(M. Naor, ed.), pp. 1–20, Springer-Verlag, 19–21 February 2004.

[331] O. Reingold, L. Trevisan, and S. Vadhan, “Pseudorandom Walks in Regular
Digraphs and the RL vs. L Problem,” in Proceedings of the Annual ACM
Symposium on Theory of Computing (STOC ‘06), pp. 457–466, 21–23 May
2006. (Preliminary version as ECCC TR05-22, February 2005).



<!-- pdf-page: 334 -->
References

331

[332] O. Reingold, S. Vadhan, and A. Wigderson, “Entropy waves, the zig-zag
graph product, and new constant-degree expanders and extractors,” in
Proceedings of the Annual Symposium on Foundations of Computer Science
(FOCS ‘00), pp. 3–13, Redondo Beach, CA, 17–19 October 2000.

[333] O. Reingold, S. Vadhan, and A. Wigderson, “Entropy waves, the zig-zag
graph product, and new constant-degree expanders,” Annals of Mathematics,
vol. 155, no. 1, January 2001.

[334] O. Reingold, S. Vadhan, and A. Wigderson, “A note on extracting randomness

from Santha–Vazirani sources,” Unpublished manuscript, September 2004.

[335] A. R´enyi, “On measures of entropy and information,” in Proceedings of
Berkeley Symposium on Mathematics Statistics and Probability, Vol. I,
pp. 547–561, Berkeley, California: University of California Press, 1961.
[336] R. L. Rivest, A. Shamir, and L. Adleman, “A method for obtaining digital sig-
natures and public-key cryptosystems,” Communications of the Association
for Computing Machinery, vol. 21, no. 2, pp. 120–126, 1978.

[337] D. Ron, “Property testing,” in Handbook of Randomized Computing, Vol. I,
II, volume 9 of Comb. Optim., pp. 597–649, Dordrecht: Kluwer Academic
Publications, 2001.

[338] E. Rozenman and S. Vadhan, “Derandomized squaring of graphs,” in Pro-
ceedings of the International Workshop on Randomization and Computation
(RANDOM ‘05), vol. 3624 of Lecture notes in Computer Science, pp. 436–447,
Berkeley, CA, August 2005.

[339] R. Rubinfeld, “Sublinear time algorithms,” in International Congress of
Mathematicians. Vol. III, pp. 1095–1110, Z¨urich: European Mathematical
Society, 2006.

[340] R. Rubinfeld and M. Sudan, “Robust characterizations of polynomials with
applications to program testing,” SIAM Journal on Computing, vol. 25, no. 2,
pp. 252–271, 1996.

[341] A. Rukhin, J. Soto, J. Nechvatal, M. Smid, E. Barker, S. Leigh, M. Levenson,
M. Vangel, D. Banks, A. Heckert, J. Dray, and S. Vo, “A statistical test suite
for random and pseudorandom number generators for cryptographic applica-
tions,” National Institute of Standards and Technology, U.S. Department of
Commerce, Special Publication 800-22, Revision 1a, April 2010.

[342] S. Sahni and T. Gonzalez, “P -complete approximation problems,” Journal of

the ACM, vol. 23, no. 3, pp. 555–565, 1976.

[343] M. Saks, A. Srinivasan, and S. Zhou, “Explicit OR-dispersers with
polylogarithmic degree,” Journal of the ACM, vol. 45, no. 1, pp. 123–154,
1998.

[344] M. Saks and S. Zhou, “BPHSPACE(S) ⊆ DSPACE(S3/2),” Journal of

Computer and System Sciences, vol. 58, no. 2, pp. 376–403, 1999.

[345] M. Saks and D. Zuckerman, Unpublished manuscript. 1995.
[346] M. S´antha and U. V. Vazirani, “Generating quasirandom sequences from
semirandom sources,” Journal of Computer and System Sciences, vol. 33,
no. 1, pp. 75–87, 1986.
(Annual Symposium on Foundations of Computer
Science (Singer Island, FL, 1984)).



<!-- pdf-page: 335 -->
332 References

[347] R. Santhanam, “Circuit

for Merlin-Arthur classes,” in
STOC’07 — Proceedings of the Annual ACM Symposium on Theory of
Computing, pp. 275–283, New York, 2007.

lower bounds

[348] P. Sarnak, Some Applications of Modular Forms. Vol. 99 of Cambridge Tracts

in Mathematics. Cambridge: Cambridge University Press, 1990.

[349] W. J. Savitch, “Relationships between nondeterministic and deterministic
tape complexities,” Journal of Computer and System Sciences, vol. 4,
pp. 177–192, 1970.

[350] J. P. Schmidt, A. Siegel, and A. Srinivasan, “Chernoﬀ-Hoeﬀding bounds
for applications with limited independence,” SIAM Journal on Discrete
Mathematics, vol. 8, no. 2, pp. 223–250, 1995.

[351] J. T. Schwartz, “Fast probabilistic algorithms for veriﬁcation of polynomial

identities,” Journal of the ACM, vol. 27, no. 4, pp. 701–717, 1980.

[352] R. Shaltiel, “Recent Developments in Extractors,” in Current Trends in The-
oretical Computer Science, vol. 1, (G. Paun, G. Rozenberg, and A. Salomaa,
eds.), pp. 189–228, World Scientiﬁc, 2004.

[353] R. Shaltiel, “Dispersers for aﬃne sources with sub-polynomial entropy,” in

FOCS, (R. Ostrovsky, ed.), pp. 247–256, IEEE, 2011.

[354] R. Shaltiel, “An introduction to randomness extractors,” in Automata,
languages and programming. Part II, vol. 6756 of Lecture Notes in Computer
Science, pp. 21–41, Heidelberg: Springer, 2011.

[355] R. Shaltiel, “Weak derandomization of weak algorithms: explicit versions of

Yao’s lemma,” Computational Complexity, vol. 20, no. 1, pp. 87–143, 2011.

[356] R. Shaltiel and C. Umans, “Simple extractors for all min-entropies and a new
Pseudo-random generator,” Journal of the ACM, vol. 52, no. 2, pp. 172–216,
2005.

[357] R. Shaltiel and C. Umans, “Pseudorandomness for approximate counting and
sampling,” Computational Complexity, vol. 15, no. 4, pp. 298–341, 2006.
[358] R. Shaltiel and C. Umans, “Low-end uniform hardness versus randomness
tradeoﬀs for AM,” SIAM Journal on Computing, vol. 39, no. 3, pp. 1006–1037,
2009.

[359] A. Shamir, “How to share a secret,” Communications of the Association for

Computing Machinery, vol. 22, no. 11, pp. 612–613, 1979.

[360] A. Shamir, “On the generation of cryptographically strong pseudorandom
sequences,” in Automata, Languages and Programming (Akko, 1981), vol. 115
of Lecture Notes in Computer Science, pp. 544–550, Berlin: Springer, 1981.

[361] C. E. Shannon, “A mathematical theory of communication,” The Bell System

Technical Journal, vol. 27, pp. 379–423, 623–656, 1948.

[362] A. Shpilka and A. Yehudayoﬀ, “Arithmetic circuits: A survey of recent results
and open questions,” Foundations and Trends(cid:1) in Theoretical Computer
Science, vol. 5, no. 3–4, pp. 207–388 (2010), 2009.

[363] J. S´ıma and S. Z´ak, “Almost k-wise independent sets establish hitting sets
for width-3 1-branching programs,” in CSR, vol. 6651 of Lecture Notes in
Computer Science, (A. S. Kulikov and N. K. Vereshchagin, eds.), pp. 120–133,
Springer, 2011.



<!-- pdf-page: 336 -->
References

333

[364] M. Sipser, “A complexity theoretic approach to randomness,” in Annual ACM
Symposium on Theory of Computing, pp. 330–335, Boston, Massachusetts,
25–27 April 1983.

[365] M. Sipser, “Expanders, randomness, or time versus space,” Journal of
Computer and System Sciences, vol. 36, no. 3, pp. 379–383, 1988. (Structure
in Complexity Theory Conference (Berkeley, CA, 1986)).

[366] M. Sipser, Introduction to the Theory of Computation. Course Technology,

2nd Edition, 2005.

[367] M. Sipser and D. A. Spielman, “Expander codes,” IEEE Transactions on
Information Theory, vol. 42, no. 6 part 1, pp. 1710–1722, 1996. (Codes and
complexity).

[368] R. Smolensky, “Algebraic methods in the theory of lower bounds for Boolean
circuit complexity,” in STOC, (A. V. Aho, ed.), pp. 77–82, ACM, 1987.
[369] R. Solovay and V. Strassen, “A fast Monte-Carlo test for primality,” SIAM

Journal on Computing, vol. 6, no. 1, pp. 84–85, 1977.

[370] J. Spencer, Ten Lectures on the Probabilistic Method, volume 64 of CBMS-NSF
Regional Conference Series in Applied Mathematics. Philadelphia, PA: Society
for Industrial and Applied Mathematics (SIAM), Second Edition, 1994.
[371] D. A. Spielman, “Spectral graph theory and its applications,” in Symposium
on Foundations of Computer Science (FOCS 2007), 21-23 October 2007,
Providence, RI, USA, Proceedings, pp. 29–38, 2007.

[372] A. Srinivasan and D. Zuckerman, “Computing with very weak random
sources,” SIAM Journal on Computing, vol. 28, no. 4, pp. 1433–1459
(electronic), 1999.

[373] T. Steinke, “Pseudorandomness for permutation branching programs without
the group theory,” Technical Report TR12-083, Electronic Colloquium on
Computational Complexity (ECCC), July 2012.

[374] J. Stern, “Secret linear congruential generators are not cryptographically

secure,” in FOCS, pp. 421–426, IEEE Computer Society, 1987.

[375] H. Stichtenoth, Algebraic Function Fields and Codes, volume 254 of Graduate
Texts in Mathematics. Berlin: Springer-Verlag, Second Edition, 2009.
[376] D. R. Stinson, “Combinatorial techniques for universal hashing,” Journal of

Computer and System Sciences, vol. 48, no. 2, pp. 337–346, 1994.

[377] V. Strassen, “Gaussian elimination is not optimal,” Numerische Mathematik,

vol. 13, pp. 354–356, 1969.

[378] M. Sudan, “Decoding of Reed Solomon codes beyond the error-correction

bound,” Journal of Complexity, vol. 13, pp. 180–193, March 1997.

[379] M. Sudan, “Algorithmic introduction to coding theory,” Lecture notes,

http://people.csail.mit.edu/madhu/FT01/, 2001.

[380] M. Sudan, “Essential

coding theory (lecture notes),” http://people.

csail.mit.edu/madhu/FT04/, 2004.

[381] M. Sudan, L. Trevisan, and S. Vadhan, “Pseudorandom generators without
the XOR lemma,” Journal of Computer and System Sciences, vol. 62,
pp. 236–266, 2001.

[382] A. Ta-Shma, C. Umans, and D. Zuckerman, “Lossless condensers, unbalanced
expanders, and extractors,” Combinatorica, vol. 27, no. 2, pp. 213–240, 2007.



<!-- pdf-page: 337 -->
334 References

[383] A. Ta-Shma and D. Zuckerman, “Extractor codes,” IEEE Transactions on

Information Theory, vol. 50, no. 12, pp. 3015–3025, 2004.

[384] A. Ta-Shma, D. Zuckerman, and S. Safra, “Extractors from Reed-Muller
codes,” Journal of Computer and System Sciences, vol. 72, no. 5, pp. 786–812,
2006.

[385] M. R. Tanner, “Explicit concentrators from generalized N -gons,” SIAM
Journal on Algebraic Discrete Methods, vol. 5, no. 3, pp. 287–293, 1984.
[386] T. Tao, “Expansion in ﬁnite groups of Lie type,” Lecture Notes,

http://www.math.ucla.edu/ tao/254b.1.12w/, 2012.

[387] A. Terras, Fourier Analysis on Finite Groups and Applications, volume 43
of London Mathematical Society Student Texts. Cambridge: Cambridge
University Press, 1999.

[388] S. Tessaro, “Computational indistinguishability ampliﬁcation,” PhD thesis,
http://e-collection.library.ethz.ch/eserv/eth:1817/eth-1817-

ETH Zurich,
02.pdf, 2010.

[389] L. Trevisan, “Extractors and pseudorandom generators,” Journal of the

ACM, vol. 48, no. 4, pp. 860–879, (electronic), 2001.

[390] L. Trevisan, “List decoding using the XOR lemma,” in Proceedings of
the IEEE Symposium on Foundations of Computer Science, pp. 126–135,
Cambridge, MA, October 2003.

[391] L. Trevisan, “Some applications of coding theory in computational complex-

ity,” Quaderni di Matematica, vol. 13, pp. 347–424, 2004.

[392] L. Trevisan, “On uniform ampliﬁcation of hardness in NP,” in STOC’05:
the Annual ACM Symposium on Theory of Computing,

Proceedings of
pp. 31–38, New York, 2005.

[393] L. Trevisan, “Pseudorandomness and combinatorial constructions,” in
International Congress of Mathematicians. Vol. III, pp. 1111–1136, Z¨urich:
European Mathematics Society, 2006.

[394] L. Trevisan, “Guest column: Additive combinatorics and theoretical computer

science,” SIGACT News, vol. 40, no. 2, pp. 50–66, 2009.

[395] L. Trevisan, “Dense model theorems and their applications,” in Theory of
cryptography, vol. 6597 of Lecture Notes in Computer Science, pp. 55–57,
Heidelberg: Springer, 2011.

[396] L. Trevisan, M. Tulsiani, and S. Vadhan, “Regularity, boosting, and eﬃciently
simulating every high-entropy distribution,” in Proceedings of the Annual
IEEE Conference on Computational Complexity (CCC ‘09), pp. 126–136,
15–18 July 2009. (Preliminary version posted as ECCC TR08-103).

[397] L. Trevisan and S. Vadhan, “Pseudorandomness and average-case complexity
via uniform reductions,” Computational Complexity, vol. 16, pp. 331–364,
December 2007.

[398] L. Trevisan and S. Vadhan, “Extracting randomness from samplable distribu-
tions,” in Proceedings of the Annual Symposium on Foundations of Computer
Science (FOCS ‘00), pp. 32–42, Redondo Beach, CA, 17–19 October
2000.

[399] C. Umans, “Pseudo-random generators for all hardnesses,” Journal of

Computer and System Sciences, vol. 67, no. 2, pp. 419–440, 2003.



<!-- pdf-page: 338 -->
References

335

[400] S. Vadhan, “Probabilistic proof systems, Part I — interactive & zero-
knowledge proofs,” in Computational Complexity Theory, vol. 10 of IAS/Park
City Mathematics Series, (S. Rudich and A. Wigderson, eds.), pp. 315–348,
American Mathematical Society, 2004.

[401] S. Vadhan and C. J. Zheng, “Characterizing pseudoentropy and simplifying
pseudorandom generator constructions,” in Proceedings of the Annual ACM
Symposium on Theory of Computing (STOC ‘12), pp. 817–836, 19–22 May
2012.

[402] S. P. Vadhan, “Constructing locally computable extractors and cryptosys-
tems in the bounded-storage model,” Journal of Cryptology, vol. 17, no. 1,
pp. 43–77, January 2004.

[403] L. G. Valiant, “Graph-theoretic properties in computational complexity,”
Journal of Computer and System Sciences, vol. 13, no. 3, pp. 278–285, 1976.
[404] L. G. Valiant, “The complexity of computing the permanent,” Theoretical

Computer Science, vol. 8, no. 2, pp. 189–201, 1979.

[405] L. G. Valiant, “A theory of the learnable,” Communications of the ACM,

vol. 27, no. 11, pp. 1134–1142, 1984.

[406] R. Varshamov, “Estimate of the number of signals in error correcting codes,”

Doklady Akademe Nauk SSSR, vol. 117, pp. 739–741, 1957.

[407] U. V. Vazirani, “Towards a strong communication complexity theory or
generating quasi-random sequences from two communicating slightly-random
sources (extended abstract),” in Proceedings of the Annual ACM Symposium
on Theory of Computing, pp. 366–378, Providence, Rhode Island, 6–8 May
1985.

[408] U. V. Vazirani, “Eﬃciency considerations in using semi-random sources

(extended abstract),” in STOC, (A. V. Aho, ed.), pp. 160–168, ACM, 1987.

[409] U. V. Vazirani, “Strong communication complexity or generating quasirandom
sequences from two communicating semirandom sources,” Combinatorica,
vol. 7, no. 4, pp. 375–392, 1987.

[410] U. V. Vazirani and V. V. Vazirani, “Random polynomial time is equal to
slightly-random polynomial time,” in Annual Symposium on Foundations of
Computer Science, pp. 417–428, Portland, Oregon, 21–23 October 1985.
[411] E. Viola, “The complexity of constructing pseudorandom generators from hard

functions,” Computational Complexity, vol. 13, no. 3–4, pp. 147–188, 2004.

[412] E. Viola, “Pseudorandom bits for constant-depth circuits with few arbitrary
symmetric gates,” SIAM Journal on Computing, vol. 36, no. 5, pp. 1387–1403,
(electronic), 2006/2007.

[413] E. Viola, “The sum of d small-bias generators fools polynomials of degree d,”

Computational Complexity, vol. 18, no. 2, pp. 209–217, 2009.

[414] E. Viola, “Extractors for circuit sources,” in FOCS, (R. Ostrovsky, ed.),

pp. 220–229, IEEE, 2011.

[415] E. Viola, “The complexity of distributions,” SIAM Journal on Computing,

vol. 41, no. 1, pp. 191–218, 2012.

[416] J. von Neumann, “Various techniques used in conjunction with random dig-
its,” in Collected Works. Vol. V: Design of Computers, Theory of Automata
and Numerical Analysis, New York: The Macmillan Co., 1963.



<!-- pdf-page: 339 -->
336 References

[417] M. N. Wegman and J. L. Carter, “New hash functions and their use in
authentication and set equality,” Journal of Computer and System Sciences,
vol. 22, no. 3, pp. 265–279, 1981.

[418] R. Williams, “Improving exhaustive search implies superpolynomial lower
the 2010 ACM International

bounds,” in STOC’10 — Proceedings of
Symposium on Theory of Computing, pp. 231–240, New York: ACM, 2010.

[419] R. Williams, “Non-uniform ACC circuit lower bounds,” in IEEE Conference

on Computational Complexity, pp. 115–125, 2011.

[420] J. Wozencraft, “List decoding,” Quarterly Progress Report, Research

Laboratory of Electronics, MIT, vol. 48, pp. 90–95, 1958.

[421] A. C. Yao, “Theory and applications of trapdoor functions (extended
abstract),” in Annual Symposium on Foundations of Computer Science,
pp. 80–91, Chicago, Illinois, 3–5 November 1982.

[422] A. Yehudayoﬀ, “Aﬃne extractors over prime ﬁelds,” Combinatorica, vol. 31,

no. 2, pp. 245–256, 2011.

[423] S. Yekhanin, “Towards 3-query locally decodable codes of subexponential

length,” Journal of the ACM, vol. 55, no. 1, pp. Art 1, 16, 2008.

[424] S. Yekhanin, Locally Decodable Codes. Now Publishers, 2012. (To appear).
[425] R. Zippel, “Probabilistic algorithms for sparse polynomials,” in EUROSAM,
vol. 72 of Lecture Notes in Computer Science, (E. W. Ng, ed.), pp. 216–226,
Springer, 1979.

[426] D. Zuckerman, “Simulating BPP using a general weak random source,”

Algorithmica, vol. 16, pp. 367–391, October/November 1996.

[427] D. Zuckerman, “Randomness-optimal oblivious sampling,” Random Struc-

tures & Algorithms, vol. 11, no. 4, pp. 345–367, 1997.

[428] V. V. Zyablov and M. S. Pinsker, “List cascade decoding (in Russian),”
Problems of Information Transmission, vol. 17, no. 4, pp. 29–33, 1981.


